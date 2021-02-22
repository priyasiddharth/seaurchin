datatype stack_state = Raw | Mutable | Share | Invalid | Owner

class State {
   var counter: nat; // used to generate new id
   var mem: array<int>;
   var tagmem: array<Pointer>;
   var markmem: array<Pointer>; 
   
   function getStackState(addr: nat) : stack_state {
     tagmem[addr].kind
   }
   
   method generateID() returns (ret: nat) {
     counter := counter + 1;
     ret := counter;
   }
   method write(p: Pointer, v: int)
     modifies mem;
   {
     if (!p.valid(this)){
       mem[p.addr] := *;
       return;
     }
     
     if (p.kind == Invalid || p.kind == Share){
       mem[p.addr] := *;
       return;
     }
     match p.kind
     case Owner =>
       mem[p.addr] := v;
       tagmem[p.addr] := p;
     case Mutable =>
       if (p.tag == tagmem[p.addr].tag){
          // p is the top of the stack
          mem[p.addr] := v;
       } else if (p.tag < tagmem[p.addr].tag){
         // p is not on the top
         tagmem[p.addr].kind := Invalid;  // old top is out
         tagmem[p.addr] := p; // update the top
         mem[p.addr] := v;
       }
     case Raw =>
       if (tagmem[p.addr].tag == p.tag){
         // p is on the top
          mem[p.addr] := v;
       } else{
         mem[p.addr] := *;
       }
   }
   
   method read(p: Pointer) returns (r: int){
     r := mem[p.addr];
     if (!p.valid(this)){
       r := *;
       return;
     }
     
     if (p.kind == Invalid){
       r := *;
       return;
     }
     match p.kind
     case Owner =>
       // nothing need to do
     case Share =>
      // nothing to do
     case Mutable => 
       // mutable ref
       if (p.tag == tagmem[p.addr].tag){
         // top
         r := mem[p.addr];
       } else if (p.tag < tagmem[p.addr].tag){
         tagmem[p.addr].kind := Invalid; // old top is out
         tagmem[p.addr] := p;
       } 
     }
   }
   

class Pointer{
  var addr: nat;
  var tag: nat;
  var kind: stack_state;
  var predecessor: Pointer;
  
  predicate isAncestor(p: Pointer, s: State) 
  requires p.valid(s);
  {
    (predecessor == null ==> tag == p.tag) ||
    (predecessor != null ==> p.predecessor.tag == p.tag || predecessor.isAncestor(p, s))
  }
  
  predicate valid(s: State){
    kind != Invalid &&
    tag <= s.tagmem[addr].tag && 
    (s.tagmem[addr].kind == kind ==> tag <= s.tagmem[addr].tag) &&
    (s.tagmem[addr].kind != kind ==> tag == s.markmem[addr].tag)
  }
  
  constructor(addr: nat, tag: nat, kind: stack_state, pred: Pointer) {
    this.addr := addr;
    this.tag := tag;
    this.kind := kind;
    this.predecessor := pred;
  }
  
}

method createOwner(addr: nat, s: State)  returns(ret: Pointer) {
   var newID := s.generateID();
   ret := new Pointer(addr, newID, Owner, null);
}


method createMutableRef(p: Pointer, s: State) returns(ret: Pointer)
{
  var newID := s.generateID();
  
  if (!p.valid(s)) {
    s.mem[p.addr] := *;
    return;
  }
  // mutable borrowing is from mutable ref or owner
  if (p.kind != Mutable || p.kind != Owner) {
     s.mem[p.addr] := *;
     return;
  }
  
  // get the state of the stack;
  var stack_status := s.getStackState(p.addr);
  
  match stack_status
  case Invalid => s.mem[p.addr] := *;
  case Share => 
       // pop the top
       s.tagmem[p.addr].kind := Invalid;
        ret := new Pointer(p.addr, newID, Mutable, s.markmem[p.addr]);
       s.tagmem[p.addr] := ret;  // push new mut ref
  case Mutable =>
      // p is the top of the stack && p is mutable
      if (s.tagmem[p.addr].tag == p.tag){
        ret := new Pointer(p.addr, newID, Mutable, s.tagmem[p.addr]);
        s.tagmem[p.addr] := ret;
      } else if (s.tagmem[p.addr].isAncestor(p, s)){
         // p is an ancestor of the top
        var oldtop := s.tagmem[p.addr];
        oldtop.kind := Invalid;  // old top is out
        ret := new Pointer(p.addr, newID, Mutable, p);
        s.tagmem[p.addr] := ret; // new top
      } 
    case Owner =>
       s.markmem[p.addr] := s.tagmem[p.addr];
       ret := new Pointer(p.addr, newID, Mutable, p);
       s.tagmem[p.addr] := ret;
    case Raw =>
       // todo
}

method createShareRef(p: Pointer, s: State) returns(ret: Pointer){
  var newID := s.generateID();
  if (!p.valid(s)) {
    s.mem[p.addr] := *;
    return;
  }
  
  // shared borrowing is from mutable ref or owner or shared ref
  if (p.kind != Mutable || p.kind != Owner || p.kind != Share) {
     s.mem[p.addr] := *;
     return;
  }
  
  // get the state of the stack;
  var stack_status := s.getStackState(p.addr);
  
  match stack_status
  case Invalid => s.mem[p.addr] := *;
  case Share =>
     // we consider the original mutable ref as its predecessor
     ret := new Pointer(p.addr, newID, Share, s.markmem[p.addr]);
     s.tagmem[p.addr] := ret; // just push
  case Owner =>
     // saving the owner to the marker
     s.markmem[p.addr] := s.tagmem[p.addr]; 
     ret := new Pointer(p.addr, newID, Share, p);
     s.tagmem[p.addr] := ret; // push
  case Mutable =>
        // saving the mutable to the marker
        s.markmem[p.addr] := s.tagmem[p.addr];
        ret := new Pointer(p.addr, newID, Share, p);
        s.tagmem[p.addr] := ret;
  case Raw =>
     // convert from raw to & mutable
       // pop up te top
       s.tagmem[p.addr].kind := Invalid;
       ret := new Pointer(p.addr, newID, Mutable, s.markmem[p.addr]);
       s.tagmem[p.addr] := ret;
}

method createRawRef(p: Pointer, s: State) returns(ret: Pointer)
modifies s.mem;
{
   var newID := s.generateID();
   if (!p.valid(s)) {
    s.mem[p.addr] := *;
    return;
  }
   
   // raw borrowing is from mutable ref or owner
  if (p.kind != Mutable || p.kind != Owner) {
     s.mem[p.addr] := *;
     return;
  }
  
  // get the state of the stack;
  var stack_status := s.getStackState(p.addr);
  
  match stack_status
  case Mutable =>
    if (p.tag == s.tagmem[p.addr].tag){
      // p is on the top
      // saving top to the marker
      s.markmem[p.addr] := s.tagmem[p.addr];
      ret := new Pointer(p.addr, newID, Raw, s.markmem[p.addr]);
      s.tagmem[p.addr] := ret;
    } else if (p.tag < s.tagmem[p.addr].tag){
      // saving p to the marker
      s.markmem[p.addr] := p;
      // old top is out
      s.tagmem[p.addr].kind := Invalid;
      ret := new Pointer(p.addr, newID, Raw, s.markmem[p.addr]);
      s.tagmem[p.addr] := ret;
    }
   case Owner =>
     if (p.tag != s.tagmem[p.addr].tag){
      s.mem[p.addr] := *;
     } else{
       // saving owner to the marker
       s.markmem[p.addr] := s.tagmem[p.addr];
       ret := new Pointer(p.addr, newID, Raw, s.markmem[p.addr]);
       s.tagmem[p.addr] := ret;
     }
   case Raw =>
     // top is out
     s.tagmem[p.addr].kind := Invalid;
     // we only know the ref from marker,
     // which was the top mutable or owner before the first raw sharing
     if (p.tag == s.markmem[p.addr].tag){
       ret := new Pointer(p.addr, newID, Raw, s.markmem[p.addr]);
       s.tagmem[p.addr] := ret;
     } 
  
}