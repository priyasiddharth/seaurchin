datatype Tag = Unique(t: nat, c: nat) | SharedRO(t: nat, c:nat) | SharedRW(t: nat, c: nat) 
              | SharedRWBot | Disabled

class State {
   var counter: nat; // used to generate new id
   var mem: array<int>;
   var tagmem: array<Tag>;
   var ancestors: map<Tag, set<Tag>>;
   var predecessor: map<Tag, Tag>;
   // indicate if ShareRW(Bot) is on stack
   var raw: array<bool>;   
   // record the last SharedRO(t, c)
   var lastread: array<Tag>;
   
   method generateID() returns (ret: nat) 
   modifies this;
   {
     counter := counter + 1;
     ret := counter;
   }
   
   predicate isWritable(p: Pointer)
   requires p.valid(this);
   reads this, p;
   { 
      match p.tag
      case Unique(t, c)  => p.tag in ancestors[tagmem[p.addr]]
      case SharedRW(t, c) =>  p.tag in ancestors[tagmem[p.addr]]
      case _ => false
   }
   
   method write(p: Pointer, v: int)
     requires p.valid(this) && isWritable(p);
     modifies mem, tagmem;
   {
     match p.tag
     case Unique(t, c) =>
       use1(p);
       mem[p.addr] := v;
     case SharedRW(t, c) =>
        tagmem[p.addr] := p.tag; // update the top
         mem[p.addr] := v;
   }
   
 method use1(p: Pointer) 
 requires p.valid(this);
{
  match p.tag
  case Unique(t, c) =>  
    // Rule (USE -1 ) 
    // requires Unique(t) is in the stack
    // p becomes the top
    tagmem[p.addr] := p.tag; 
}

method use2(p: Pointer)
requires p.valid(this);
{
  if (raw[p.addr]) { // Pointer(l, Bot)
    // pop up anything above SharedRWBot
    tagmem[p.addr] := SharedRWBot;
  } else{
    match p.tag
    case Unique(t, c) => // Pointer(l, t)
    // pop up anything above Pointer(l, t)
    tagmem[p.addr] := p.tag;
  }
}
   
   method read(p: Pointer) returns (r: int)
   requires p.valid(this);
   {
     r := mem[p.addr];
     match p.tag
     case Unique(t, c) =>
        use1(p);
     case SharedRO(t, c) =>
      // nothing to do
     case SharedRW(t, c) => 
      // ?
     
   }
} 
   

class Pointer{
  var addr: nat;
  var tag: Tag;
  
 predicate valid(s: State){
    tag in s.ancestors[s.tagmem[addr]]
  }
  
  constructor(addr: nat, tag: Tag) {
    this.addr := addr;
    this.tag := tag;
  }
}

method createOwner(addr: nat, s: State)  returns(ret: Pointer) 
modifies s;
{
   var newID := s.generateID();
   var new_tag := Unique(newID, 1);
   ret := new Pointer(addr, new_tag);
   s.ancestors := s.ancestors[new_tag := {new_tag}];
   s.predecessor := s.predecessor[new_tag := new_tag];
   s.raw[addr] := false;
}

method createMutableRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  match p.tag
    case Unique(t, c) =>
        /*
            let x = & mut p;
            1. it is considered as a use of p
            2. generate a fresh tag for the new reference x, i.e., Unique(t', c)
            3. record Unique(t', c)'s predecessor
            4. record Unique(t',c)'s ancestors
            5. push Unique(t', c) to the stack
        */
       var top := s.tagmem[p.addr];
       var newtag := Unique(newID, c);
       s.use1(p);
       ret := new Pointer(p.addr, newtag);
       s.predecessor := s.predecessor[newtag := predecessor_of_top];
       s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
       s.tagmem[p.addr] := newtag;
    case Raw =>
       // todo
}

/*
Rule (NEW-SHARE-REF-1)
*/
method createShareRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  /*
  1. consider a read access to p
  2. generate a fresh tag for the new reference x, i.e., SharedRO(t', c)
  3. record SharedRO(t', c)'s predecessor
  4. record SharedRO(t', c)'s ancestors
  5. update lastread as SharedRO(t', c)
  6. push SharedRO(t', c) to the stack
  */
  readPointer(p, s);
  var newtag := SharedRO(newID, 1);
  ret := new Pointer(p.addr, newtag);
  s.predecessor := s.predecessor[newtag := predecessor_of_top];
  s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
  s.lastread[p.addr] := newtag;
  s.tagmem[p.addr] := newtag;
}

// Rule READ-1
// p could be Unique(t, c), SharedRO(t, c), SharedRW(t, c)
method readPointer(p: Pointer, s: State)
requires p.valid(s) ;
modifies s, s.tagmem;
{
  // pop items off the stack until all the items above the item 
  // with tag t are SharedRO(t, c)
  s.tagmem[p.addr] := s.lastread[p.addr];
}

/*
Raw pointers can only be created from Unique(t)
let raw_pointer = &mut p as *mut i32;
*/
method createMutableRawRef(p: Pointer, s: State) returns(ret: Pointer)
requires p.valid(s);
modifies s;
{
  var newID := s.generateID();
  var top := s.tagmem[p.addr];
  var predecessor_of_top := s.predecessor[p.tag];
  var ancestors_of_top := s.ancestors[p.tag];
  
  match p.tag
  case ShareRWBot =>
      /*
      1. a use of p
      2. generate new pointer
      3. record new tag's predecessor
      4. record new tag's ancestors
      5. push ShareRW(BOT) on the top
      */
      var newtag := Unique(newID, 1);
      s.use2(p);
      var ret := new Pointer(p.addr, newtag);
      s.predecessor := s.predecessor[newtag := top];
      s.ancestors := s.ancestors[newtag := s.ancestors[top] + {newtag}];
      s.tagmem[p.addr] := newtag;
   case Unique(t, c) =>
      /*
      Rule (NEW-MUTABLE-RAW-1)
      1. a use of p (USE-2)
      2. generate new pointer
      3. record new tag's predecessor
      4. record new tag's ancestors
      5. push ShareRW(BOT) on the top
      6. mark the addr as raw
      */
      var newtag := SharedRWBot;
      s.use2(p);
      var ret := new Pointer(p.addr, newtag);
      s.predecessor := s.predecessor[newtag := predecessor_of_top];
      s.ancestors := s.ancestors[newtag := ancestors_of_top + {newtag}];
      s.tagmem[p.addr] := newtag;
      s.raw[p.addr] := true;
}