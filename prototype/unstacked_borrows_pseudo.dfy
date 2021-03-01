datatype Tag = Unique(t: nat, c: nat) | SharedRO(t: nat, c:nat)   
              | Disabled | Owner

class State {
   var counter: nat; // used to generate new id
   var mem: array<int>;
   var tagmem: array<Tag>;
   
   // the tag from which a raw ponter borrows from
   var rawfrom: array<int>;  

   constructor(mem: array<int>)
   ensures fresh(tagmem) && fresh(rawfrom);
   ensures this.mem == mem && counter == 0;
   ensures forall i:: 0 <= i && i < tagmem.Length ==> tagmem[i] == Owner;
   ensures forall i:: 0 <= i && i < rawfrom.Length ==> rawfrom[i] == -1;
   ensures valid();
   {
     this.mem := mem;
     tagmem := new Tag[mem.Length](_ => Owner);
     rawfrom := new int[mem.Length](_ => -1);
     counter := 0;
     
   }

   predicate valid()
   reads this, mem, tagmem, rawfrom;
   {
    mem.Length == tagmem.Length && mem.Length == rawfrom.Length 
   } 

   predicate valid_addr(addr: int)
   requires valid();
   reads this, mem,tagmem, rawfrom;
   {
      0 <= addr && addr < mem.Length
   }

predicate invalidTag(addr: nat, tag: Tag)
 requires valid() && valid_addr(addr);
 reads this, tagmem, rawfrom, mem;
 {
    match (tagmem[addr], tag)
    case (Unique(n1, c1), Unique(n2, c2)) => 
     if (rawfrom[addr] != -1) then n2 != n1
      else n1 < n2
    case (SharedRO(n1, c1), Unique(n2, c2)) => n1 < n2
    case (Unique(n1, c1), SharedRO(n2, c2)) => n2 < n1
    case (SharedRO(n1, c1), SharedRO(n2, c2)) => false
    case (Owner, _) => false
    case (_, _) => true
}  

predicate validTag(addr: nat, tag: Tag)
requires valid() && valid_addr(addr);
reads this, tagmem, rawfrom, mem;
{
  
   tagmem[addr] == Owner 
   ||  
   (tagmem[addr] != Owner ==> !invalidTag(addr, tag))
}
    
   
   method generateID() returns (ret: nat) 
   requires valid();
   modifies this;
   ensures counter == old(counter) + 1 && ret == counter;
   ensures mem == old(mem) && tagmem == old(tagmem) && rawfrom == old(rawfrom);
   ensures forall i :: 0 <= i && i < tagmem.Length  ==> tagmem[i] == old(tagmem[i]);
   ensures forall i :: 0 <= i && i < rawfrom.Length  ==> rawfrom[i] == old(rawfrom[i]);
   ensures valid();
   {
     counter := counter + 1;
     ret := counter;
   }
   
   predicate isWritable(p: Pointer)
   requires valid();
   requires p.valid(this);
   reads this, mem, rawfrom, tagmem, p;
   { 
      match p.tag
      case Unique(t, c)  => true
      case _ => false
   }
   
  method write(p: Pointer, v: int)
     requires valid();
     requires p.valid(this) && isWritable(p);
     modifies mem, tagmem, rawfrom;
     ensures forall i :: 0 <= i && i < tagmem.Length && i != p.addr ==> tagmem[i] == old(tagmem[i]);
     ensures forall i :: 0 <= i && i < mem.Length && i != p.addr ==> mem[i] == old(mem[i]);
     ensures forall i :: 0 <= i && i < rawfrom.Length && i != p.addr ==> rawfrom[i] == old(rawfrom[i]);
     ensures p.tag.Unique? ==> tagmem[p.addr] == p.tag;
     ensures mem[p.addr] == v;
     ensures valid();
   {
     match p.tag
     case Unique(t, c) =>
       mem[p.addr] := v;
       tagmem[p.addr] := p.tag;
     
   }
   
   method read(p: Pointer) returns (r: int)
   requires valid();
   requires p.valid(this);
   modifies tagmem;
   ensures forall i :: 0 <= i && i < tagmem.Length && i != p.addr ==> tagmem[i] == old(tagmem[i]);
   ensures forall i :: 0 <= i && i < mem.Length && i != p.addr ==> mem[i] == old(mem[i]);
   ensures forall i :: 0 <= i && i < rawfrom.Length && i != p.addr ==> rawfrom[i] == old(rawfrom[i]);
   ensures p.tag.Unique? ==> tagmem[p.addr] == p.tag;
   ensures valid();
   {
     r := mem[p.addr];
     match p.tag
     case Unique(t, c) =>
        tagmem[p.addr] := p.tag;
     case SharedRO(t, c) =>
      // nothing to do
     
     case _ => // ?
   }
} 
   

   

class Pointer{
  var addr: nat;
  var tag: Tag;
  
 predicate valid(s: State)
 requires s.valid();
 reads s, s.tagmem, s.rawfrom, s.mem, this;
 {
    s.valid_addr(addr) && s.validTag(addr, tag)
 }
 
 constructor(addr: nat, tag: Tag, s: State) 
  requires s.valid() && s.valid_addr(addr);
  requires s.validTag(addr, tag);
  ensures this.addr == addr && this.tag == tag;
  ensures valid(s);
  {
    this.addr := addr;
    this.tag := tag;
  }
}

method createMutableRef(p: Pointer, s: State) returns(ret: Pointer)
requires s.valid() &&  s.valid_addr(p.addr) /* p.valid(s) */ && p.tag.Unique?;
modifies s, s.tagmem, s.rawfrom;
ensures s.tagmem == old(s.tagmem) && s.mem == old(s.mem) && s.rawfrom == old(s.rawfrom);
ensures s.counter == old(s.counter) + 1;
ensures forall i :: 0 <= i && i < s.tagmem.Length && i != p.addr ==> s.tagmem[i] == old(s.tagmem[i]);
ensures forall i :: 0 <= i && i < s.rawfrom.Length && i != p.addr ==> s.rawfrom[i] == old(s.rawfrom[i]);
ensures s.tagmem[p.addr] == ret.tag && s.rawfrom[p.addr] == -1;
ensures ret.addr == p.addr && ret.tag == Unique(s.counter, p.tag.c);
ensures fresh(ret);
ensures s.valid() && ret.valid(s);
{
  var newID := s.generateID();
  
  match p.tag
    case Unique(t, c?) =>
       var newtag := Unique(newID, c?);
       s.tagmem[p.addr] := newtag;
       s.rawfrom[p.addr] := -1;
       ret := new Pointer(p.addr, newtag, s);
   // case _ =>
   //    ret := new Pointer(p.addr, Disabled, s);
       // todo
}

/*
rawfrom pointers can only be created from Unique(t)
let raw_pointer = &mut p as *mut i32;
*/
method createMutableRawRef(p: Pointer, s: State) returns(ret: Pointer)
requires s.valid() && s.valid_addr(p.addr);
requires s.rawfrom[p.addr] == -1 ==> p.tag.Unique?;
requires s.rawfrom[p.addr] != -1 ==> p.tag.Unique? && s.rawfrom[p.addr] == p.tag.t;
modifies s, s.tagmem, s.rawfrom;
ensures s.tagmem == old(s.tagmem) && s.mem == old(s.mem) && s.rawfrom == old(s.rawfrom);
ensures s.counter == old(s.counter) + 1;
ensures forall i :: 0 <= i && i < s.tagmem.Length && i != p.addr ==> s.tagmem[i] == old(s.tagmem[i]);
ensures forall i :: 0 <= i && i < s.rawfrom.Length && i != p.addr ==> s.rawfrom[i] == old(s.rawfrom[i]);
ensures p.tag.Unique? ==> s.tagmem[p.addr] == ret.tag && s.rawfrom[p.addr] == p.tag.t;
ensures p.tag.Unique? ==> ret.addr == p.addr && ret.tag == Unique(s.counter, p.tag.c);
ensures fresh(ret);
ensures s.valid() && ret.valid(s);
{
  var newID := s.generateID();
  
  match p.tag
  case Unique(t, c?) =>
      var newtag := Unique(newID, c?);
      s.tagmem[p.addr] := newtag;
      s.rawfrom[p.addr] := t;
      ret := new Pointer(p.addr, newtag, s);
      assert ret.tag.t == s.tagmem[p.addr].t;

}


/*
Rule (NEW-SHARE-REF-1)
*/
method createSharedRO(p: Pointer, s: State) returns(ret: Pointer)
requires s.valid() && s.valid_addr(p.addr);
requires p.tag.Unique? || p.tag.SharedRO?;
modifies s, s.tagmem, s.rawfrom;
ensures s.tagmem == old(s.tagmem) && s.mem == old(s.mem) && s.rawfrom == old(s.rawfrom);
ensures s.counter == old(s.counter) + 1;
ensures forall i :: 0 <= i && i < s.tagmem.Length && i != p.addr ==> s.tagmem[i] == old(s.tagmem[i]);
ensures forall i :: 0 <= i && i < s.rawfrom.Length  ==> s.rawfrom[i] == old(s.rawfrom[i]);
ensures ret.addr == p.addr && ret.tag == SharedRO(s.counter, p.tag.c);
ensures fresh(ret);
ensures s.valid() && ret.valid(s);
{
  var newID := s.generateID();
  var newtag := SharedRO(newID, p.tag.c);
  match p.tag
  case Unique(t, c?) =>
    s.tagmem[p.addr] := newtag;
    ret := new Pointer(p.addr, newtag, s);
  case SharedRO(t, c?) =>
    s.tagmem[p.addr] := newtag;
    ret := new Pointer(p.addr, newtag, s);
}

// This client follows stack principle
method mutableTest(mem:array<int>)
  modifies mem;
{
  var s := new State(mem);
      
  // let mut local1 = 5;
  var local1: nat;
  var tag1 := s.generateID();
  if(0 < local1 < mem.Length){
    mem[local1] := 5;
    var ref1: Pointer := new Pointer(local1, Unique(tag1, 1), s);
  
    var ref2: Pointer := createMutableRef(ref1, s);
    
    assert(ref2.valid(s));
  
    // function call starts
    s.write(ref1, 42);
   // s.write(ref2, 13);
    assert !ref2.valid(s);
  }
}


method mutableRawTest(mem:array<int>)
  modifies mem;
{
    var s := new State(mem);
        
    // let mut local1 = 5;
    var local1: nat;
    var tag1 := s.generateID();
    if(0 < local1 < mem.Length){
      mem[local1] := 5;
      var ref1: Pointer := new Pointer(local1, Unique(tag1, 1), s);
     // s.write(ref1, 42);
      var ref2: Pointer := createMutableRawRef(ref1, s);
      assert(ref2.valid(s));

      var ref3: Pointer := createMutableRawRef(ref1, s);
      assert(!ref2.valid(s));

      var ref4: Pointer := createMutableRawRef(ref1, s);
      assert(!ref3.valid(s));
    }

  }

method mutableSharedROTest(mem:array<int>)
modifies mem;
{
  var s := new State(mem);
        
  // let mut local1 = 5;
  var local1: nat;
  var tag1 := s.generateID();
  if(0 < local1 < mem.Length){
      mem[local1] := 5;
      var ref1: Pointer := new Pointer(local1, Unique(tag1, 1), s);
     // s.write(ref1, 42);
      var ref2: Pointer := createMutableRef(ref1, s);
      
      assert(ref2.valid(s));
      var ref3: Pointer := createSharedRO(ref2, s);
      assert(ref3.valid(s));
      var ref4: Pointer := createSharedRO(ref2, s);
      assert(ref4.valid(s));
      var ref5: Pointer := createMutableRef(ref2, s);
      assert(!ref4.valid(s));

  }
}
