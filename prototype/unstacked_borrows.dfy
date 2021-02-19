// Use a counter instead of stack

//
// Library begins
//

// TODO: assignment also updates ownership and global counter

// Context class. This should be a singleton
class Ctx {
  // counter is a global counter.
  // This is incremented at each borrow site.
  // Each borrow gets a globally unique tag.
  var counter: nat;
}

// A pointer consists of an address and a tag
class Pointer {
  var addr: nat;
  var tag: nat;

  // Create a mutable ref from passed ptr
  // Memory location is owned by new reference
  constructor toMutBorrowRef(c: Ctx, tagmem: array<nat>, p: Pointer)
    requires p.addr >= 0 && p.addr < tagmem.Length
    modifies c, tagmem;
    ensures addr == p.addr
    ensures c.counter == old(c.counter) + 1;
    ensures addr >= 0 && addr < tagmem.Length
    ensures tagmem[addr] == tag;
    ensures forall a :: 0 <= a < tagmem.Length && a != addr ==> tagmem[a] == old(tagmem[a])
  {
    addr := p.addr;
    c.counter := c.counter + 1;
    tag := c.counter;
    set_owner(tagmem, p.addr, c.counter);
  }


  // Create a mutable raw (ptr) from passed ptr
  // Memory location is owned by new raw (ptr)
  constructor toMutBorrowRaw(c: Ctx, tagmem: array<nat>, p: Pointer)
    requires p.addr >= 0 && p.addr < tagmem.Length
    modifies c, tagmem;
    ensures addr == p.addr;
    ensures c.counter == old(c.counter) + 1;
    ensures addr >= 0 && addr < tagmem.Length;
    ensures tagmem[addr] == tag;  
    ensures forall a :: 0 <= a < tagmem.Length && a != addr ==> tagmem[a] == old(tagmem[a])

  {
    addr := p.addr;
    c.counter := c.counter + 1;
    tag := c.counter;
    set_owner(tagmem, p.addr, c.counter);
  }

  // Create a mutable ref from passed address
  // Memory location is owned by mutable ref
  constructor fromAddr(c: Ctx,tagmem: array<nat>, a: nat)
    requires a >= 0 && a < tagmem.Length
    modifies c, tagmem;
    ensures addr == a;
    ensures c.counter == old(c.counter) + 1;
    ensures addr >= 0 && addr < tagmem.Length
    ensures tagmem[a] == tag;    
    ensures forall l :: 0 <= l < tagmem.Length && a != l ==> tagmem[l] == old(tagmem[l])

  {
    addr := a;
    c.counter := c.counter + 1;
    tag := c.counter;
    set_owner(tagmem, a, c.counter);
  }

  // Read memory location through this ptr 
  //
  // if ptr does not have read access then return any number
  // other than expected value.
  method read(mem: array<int>, tagmem: array<nat>) returns (r: int)
    requires mem.Length == tagmem.Length
    requires addr >= 0 && addr < tagmem.Length
    ensures addr >= 0 && addr < tagmem.Length
    ensures (tagmem[addr] == tag) ==> r == mem[addr]
  {
    if (tagmem[addr] == tag) {
      return mem[addr];
    } else {
      var x: nat := *;
      assume (x != mem[addr]);
      return x;
    }
  }

  // Write to memory location through this ptr
  // 
  // if ptr does not have write access then this is a NOP
  method write(mem: array<int>, tagmem: array<nat>, v: nat)
    requires mem.Length == tagmem.Length
    requires addr >= 0 && addr < tagmem.Length
    modifies mem
    ensures addr >= 0 && addr < tagmem.Length
    ensures (tagmem[addr] == tag) ==>  mem[addr] == v;
    ensures forall l :: 0 <= l < mem.Length && addr != l ==> mem[l] == old(mem[l])
  {
    if (tagmem[addr] == tag) {
      mem[addr] := v;
    }
  }

}

// Update ownership tag value at addr
method set_owner(tagmem:array<nat>, addr: nat, tag: nat)
  requires addr >= 0 && addr < tagmem.Length
  modifies tagmem;
  ensures tagmem[addr] == tag;
  ensures forall a :: 0 <= a < tagmem.Length && a != addr ==> tagmem[a] == old(tagmem[a])

{
  tagmem[addr] := tag;
}

method get_owner(tagmem:array<nat>, addr: nat) returns (o: nat)
  requires addr >= 0 && addr < tagmem.Length
  ensures o == tagmem[addr];
{
  o := tagmem[addr];
  return o;
}

//
// Library ends
//


/*
method example1(x: Pointer, y: Pointer, mem: array<int>, tagmem: array<nat>) returns (v: int)
  requires mem.Length == tagmem.Length
  requires x.addr >= 0 && x.addr < mem.Length;
  requires y.addr >= 0 && y.addr < mem.Length;
  modifies mem;
  ensures v == 42;
{
  x.write(mem, tagmem, 42);
  assert(mem[x.addr] == 42);
  y.write(mem, tagmem, 13);
  v := x.read(mem, tagmem);
  return v;
}
*/

// This client violates stack principle
method bad_client(mem:array<int>, tagmem: array<nat>)
  requires mem.Length == tagmem.Length;
  modifies mem, tagmem;
{
  var c := new Ctx;
  c.counter := 0;
  // let mut local = 5;
  var local: nat := *;
  assume(0 < local < mem.Length);
  mem[local] := 5;
  // let raw_pointer = &mut local as *mut i32;
  var localref: Pointer := new Pointer.fromAddr(c, tagmem, local);
  var raw_pointer := new Pointer.toMutBorrowRaw(c, tagmem, localref);
  // unsafe begin
  // deref raw ptr only in `unsafe` code
  var arg1 := new Pointer.toMutBorrowRef(c, tagmem, raw_pointer);
  var arg2 := new Pointer.toMutBorrowRef(c, tagmem, raw_pointer);

  // function call starts
  arg1.write(mem, tagmem, 42);
  arg2.write(mem, tagmem, 13);
  var result := arg1.read(mem, tagmem);
  // function call ends
  // unsafe end

  // arg1 and arg2 point to the same location and hence stack principle
  // is violated here
  assert(result == 42);
}

// This client follows stack principle
method good_client(mem:array<int>, tagmem: array<nat>)
  requires mem.Length == tagmem.Length;
  modifies mem, tagmem;
{
  var c := new Ctx;
  c.counter := 0;
  
  // let mut local1 = 5;
  var local1: nat := *;
  assume(0 < local1 < mem.Length);
  mem[local1] := 5;
  var localref1: Pointer := new Pointer.fromAddr(c, tagmem, local1);

  // let mut local2 = 10;
  var local2: nat := *;
  assume(0 < local2 < mem.Length);
  assume(local1 != local2);
  mem[local2] := 10;
  var localref2: Pointer := new Pointer.fromAddr(c, tagmem, local2);

  // function call starts
  localref1.write(mem, tagmem, 42);
  localref2.write(mem, tagmem, 13);
  var result := localref1.read(mem, tagmem);
  // function call ends

  assert(result == 42);
}
