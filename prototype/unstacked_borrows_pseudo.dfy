datatype Tag = Unique(t: nat, c: nat) | SharedRO(t: nat, c:nat)   
              | Disabled | Owner

class State {
   var counter: nat; // used to generate new id
   var mem: array<int>;
   var tagmem: array<Tag>;
   var predecessor: array<int>;
   
   // the tag from which a raw ponter borrows from
   var rawfrom: array<int>;  

   constructor(mem: array<int>)
   ensures fresh(tagmem) && fresh(rawfrom) && fresh(predecessor);
   ensures this.mem == mem && counter == 0;
   ensures forall i:: 0 <= i && i < tagmem.Length ==> tagmem[i] == Owner;
   ensures forall i:: 0 <= i && i < rawfrom.Length ==> rawfrom[i] == -1;
   ensures forall i:: 0 <= i && i < predecessor.Length ==> predecessor[i] == -1;
   ensures rawfrom != predecessor && mem!= predecessor;
   ensures valid();
   {
     this.mem := mem;
     tagmem := new Tag[mem.Length](_ => Owner);
     rawfrom := new int[mem.Length](_ => -1);
     predecessor := new int[mem.Length](_ =>-1);
     counter := 0;
     
   }

   predicate valid()
   reads this, mem, tagmem, rawfrom, predecessor;
   {
    rawfrom != predecessor && mem != predecessor && rawfrom != mem &&
    mem.Length == tagmem.Length && mem.Length == rawfrom.Length &&
    mem.Length == predecessor.Length && predecessor != rawfrom &&
    (forall i:: 0 <= i && i < tagmem.Length && tagmem[i].Unique? ==> 
          predecessor[i] < tagmem[i].t && tagmem[i].t <= counter)  &&
    (forall i:: 0 <= i && i < tagmem.Length && tagmem[i].SharedRO? ==> 
          predecessor[i] < tagmem[i].t && tagmem[i].t <= counter)   
   } 

   predicate valid_addr(addr: int)
   requires valid();
   reads this, mem,tagmem, rawfrom, predecessor;
   {
      0 <= addr && addr < mem.Length
   }

predicate invalidTag(addr: nat, tag: Tag, predece: int)
 requires valid() && valid_addr(addr);
 requires tag.Unique? ==>  predece < tag.t;
 reads this, tagmem, rawfrom, mem, predecessor;
 {
    match (tagmem[addr], tag, predece)
    case (Unique(n1, c1), Unique(n2, c2),  n3) => 
     if (rawfrom[addr] != -1) then n2 != n1
      else n1 < n2 || (n1 > n2 && n3 <= n1)
    case (SharedRO(n1, c1), Unique(n2, c2), _) => 
     if (rawfrom[addr] != -1) then true 
     else false  // unknown
    case (Unique(n1, c1), SharedRO(n2, c2), _) => n2 < n1
    case (SharedRO(n1, c1), SharedRO(n2, c2), n3) =>   
          n3 < n1 // fixme
    case (Owner, _, _) => false
    case (_, _, _) => true
}  

predicate validTag(addr: nat, tag: Tag, predece: int)
requires valid() && valid_addr(addr);
requires tag.Unique? ==>  predece < tag.t;
reads this, tagmem, rawfrom, mem, predecessor;
{
   (tag.Unique?  ==> tag.t <= counter && !invalidTag(addr, tag, predece)) && 
   (tag.SharedRO? ==> tag.t <= counter && !invalidTag(addr, tag, predece))
}
    
   
   method generateID() returns (ret: nat) 
   requires valid();
   modifies this;
   ensures counter == old(counter) + 1 && ret == counter;
   ensures mem == old(mem) && tagmem == old(tagmem) && rawfrom == old(rawfrom) && predecessor == old(predecessor);
   ensures forall i:: 0 <= i && i < tagmem.Length && tagmem[i].Unique? ==> tagmem[i].t < ret; 
   ensures valid();
   {
     counter := counter + 1;
     ret := counter;
   }
   
   predicate isWritable(p: Pointer)
   requires valid();
   requires p.valid(this);
   requires p.tag.Unique?;
   reads this, mem, rawfrom, tagmem, predecessor, p;
   { 
      validTag(p.addr, p.tag, p.predecessor)
   }
   
  method write(p: Pointer, v: int)
     requires valid();
     requires p.valid(this) && p.tag.Unique? && isWritable(p);
    //  requires valid_addr(p.addr) && p.tag.Unique?;
     requires p.tag.Unique? ==> p.tag.t <= counter;
     modifies this, mem, tagmem, rawfrom, predecessor;
     ensures mem == old(mem) && tagmem == old(tagmem)  && rawfrom == old(rawfrom) && predecessor == old(predecessor) && counter == old(counter);
     ensures forall i :: 0 <= i && i < tagmem.Length && i != p.addr ==> tagmem[i] == old(tagmem[i]);
     ensures forall i :: 0 <= i && i < mem.Length && i != p.addr ==> mem[i] == old(mem[i]);
     ensures forall i :: 0 <= i && i < rawfrom.Length && i != p.addr ==> rawfrom[i] == old(rawfrom[i]);
     ensures forall i :: 0 <= i && i < predecessor.Length && i != p.addr ==> predecessor[i] == old(predecessor[i]);
     ensures p.tag.Unique? ==> tagmem[p.addr] == p.tag && predecessor[p.addr] == p.predecessor;
     ensures mem[p.addr] == v;
     ensures valid();
   {
     match p.tag
     case Unique(t, c) =>
       mem[p.addr] := v;
       tagmem[p.addr] := p.tag;
       predecessor[p.addr] := p.predecessor;
     
   }
   /*
   predicate isReadble(p: Pointer)
   requires valid();
   requires p.valid(this);
   requires p.tag.Unique? || p.tag.SharedRO?
   reads this, mem, rawfrom, tagmem, predecessor, p;
   { 
      validTag(p.addr, p.tag, p.predecessor)

   }

   method read(p: Pointer) returns (r: int)
   requires valid();
   requires p.valid(this) && (p.tag.Unique? || p.tag.SharedRO?) && isReadble(p);
   // requires valid_addr(p.addr);
   requires p.tag.Unique? ==> p.tag.t <= counter;
   modifies tagmem, predecessor;
   ensures forall i :: 0 <= i && i < tagmem.Length && i != p.addr ==> tagmem[i] == old(tagmem[i]);
   // ensures forall i :: 0 <= i && i < mem.Length && i != p.addr ==> mem[i] == old(mem[i]);
   ensures forall i :: 0 <= i && i < rawfrom.Length && i != p.addr ==> rawfrom[i] == old(rawfrom[i]);
   ensures forall i :: 0 <= i && i < predecessor.Length && i != p.addr ==> predecessor[i] == old(predecessor[i]);
   ensures p.tag.Unique? ==> tagmem[p.addr] == p.tag && predecessor[p.addr] == p.predecessor;
   ensures valid();
   {
     r := mem[p.addr];
     match p.tag
     case Unique(t, c) =>
        tagmem[p.addr] := p.tag;
        predecessor[p.addr] := p.predecessor;
     case SharedRO(t, c) =>
      // nothing to do
     
     case _ => // ?
   }

   */
  
} 
  

   

class Pointer{
  var addr: nat;
  var tag: Tag;
  // can we treated as the upperbound of the predecessor
  var predecessor: int; 
  
 predicate valid(s: State)
 requires s.valid();
 reads s, s.tagmem, s.rawfrom, s.mem, s.predecessor, this;
 {
    s.valid_addr(addr) && 
    (tag.Unique? ==> predecessor < tag.t && s.validTag(addr, tag, predecessor)) &&
    (tag.SharedRO? ==> predecessor < tag.t && s.validTag(addr, tag, predecessor))
 }

  
 constructor(addr: nat, tag: Tag, predecessor: int, s: State) 
  requires s.valid() && s.valid_addr(addr);
  requires tag.Unique? || tag.SharedRO?;
  requires tag.Unique?  ==> predecessor < tag.t && tag.t == s.counter;
  requires tag.SharedRO? ==> predecessor <  tag.t && tag.t == s.counter;
  requires s.validTag(addr, tag, predecessor);
  // ensures this.addr == addr && this.tag == tag; // under specified
   ensures this.addr == addr && this.tag == tag && this.predecessor == predecessor;
  ensures valid(s);
  {
    this.addr := addr;
    this.tag := tag;
    this.predecessor := predecessor;
  }
}

/*-----------------Unique------------------------------------------------*/

method createMutableRef(p: Pointer, s: State) returns(ret: Pointer)
requires s.valid() &&  s.valid_addr(p.addr) /* p.valid(s) */ && p.tag.Unique?;
requires p.tag.Unique? ==> p.tag.t <= s.counter;
modifies s, s.tagmem, s.rawfrom, s.predecessor;
ensures s.tagmem == old(s.tagmem)  && s.rawfrom == old(s.rawfrom) && s.predecessor == old(s.predecessor);
ensures s.counter == old(s.counter) + 1;
ensures forall i :: 0 <= i && i < s.tagmem.Length && i != p.addr ==> s.tagmem[i] == old(s.tagmem[i]);
ensures forall i :: 0 <= i && i < s.rawfrom.Length && i != p.addr ==> s.rawfrom[i] == old(s.rawfrom[i]);
ensures forall i :: 0 <= i && i < s.predecessor.Length && i != p.addr ==> s.predecessor[i] == old(s.predecessor[i]);
ensures s.tagmem[p.addr] == ret.tag && s.rawfrom[p.addr] == -1 && s.predecessor[p.addr] == p.tag.t;
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
       s.predecessor[p.addr] := t;
       ret := new Pointer(p.addr, newtag, t, s);
   // case _ =>
   //    ret := new Pointer(p.addr, Disabled, s);
       // todo
}


// This client follows stack principle
// C1
// s

/*---------------SharedRO---------------------------------*/
/*
Rule (NEW-SHARE-REF-1)
*/
/*
method createSharedRO(p: Pointer, s: State) returns(ret: Pointer)
requires s.valid() && s.valid_addr(p.addr);
//requires p.valid(s);
requires  (p.tag.Unique? || p.tag.SharedRO?);
requires p.tag.Unique? ==> p.tag.t <= s.counter;
requires p.tag.SharedRO? ==> p.tag.t <= s.counter && p.predecessor.Unique? && p.predecessor.t < s.counter;
modifies s, s.tagmem, s.rawfrom;
ensures s.tagmem == old(s.tagmem) && s.mem == old(s.mem) && s.rawfrom == old(s.rawfrom);
ensures s.counter == old(s.counter) + 1;
ensures forall i :: 0 <= i && i < s.tagmem.Length && i != p.addr ==> s.tagmem[i] == old(s.tagmem[i]);
ensures forall i :: 0 <= i && i < s.rawfrom.Length  ==> s.rawfrom[i] == old(s.rawfrom[i]);
ensures ret.addr == p.addr && ret.tag == SharedRO(s.counter, p.tag.c);
ensures p.tag.Unique? ==> ret.predecessor == p.tag;
ensures p.tag.SharedRO? ==> ret.predecessor == p.predecessor;
ensures fresh(ret);
ensures s.valid() && ret.valid(s);
{
  var newID := s.generateID();
  var newtag := SharedRO(newID, p.tag.c);
  match p.tag
  case Unique(t, c?) =>
    s.tagmem[p.addr] := newtag;
    ret := new Pointer(p.addr, newtag, p.tag, s);
  case SharedRO(t, c?) =>
    // not update the top
    // inherit top's predecessor
     assert newtag.SharedRO? && (p.predecessor.Unique? || p.predecessor.Owner?);
     assert newtag.SharedRO? && p.predecessor.Unique? ==> newtag.t > p.predecessor.t;
    ret := new Pointer(p.addr, newtag, p.predecessor, s);
}

method SharedROTest(mem:array<int>)
modifies mem;
{
  var s := new State(mem);
        
  // let mut local1 = 5;
  var local1: nat;
  var tag1 := s.generateID();
  if(0 < local1 < mem.Length){
      mem[local1] := 5;
      var ref1: Pointer := new Pointer(local1, Unique(tag1, 1), Owner, s);
     
      // let x = & mut local;
      var ref2: Pointer := createMutableRef(ref1, s);
      
      // let y = & x;
      var ref3: Pointer := createSharedRO(ref2, s);
      assert(ref3.valid(s));
      var ref4: Pointer := createSharedRO(ref2, s);
      assert(ref4.valid(s));
      var ref5: Pointer := createMutableRef(ref2, s);
      assert(!ref4.valid(s));

  }
}
*/
