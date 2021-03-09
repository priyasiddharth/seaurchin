datatype Tag = Unique(t: nat) | SharedRO(t: nat) | SharedRW(t: nat) 
datatype MaybePointer = None | Some(p:Pointer)

class State {
   var counter: nat; // used to generate new id

   // main memory
   var mem: array<int>;

   // the following configurations are possible
   // ptrOnStack == None, tracked_tag == Unique(0) 
   //     ==> no pointer is tracked
   // ptrOnStack == Some(p), tracked_tag == p.tag
   //     ==> pointer p is tracked, currently on stack, maybe top?
   // ptrOnStack == None, tracked_tag == Unique(t), t > 0
   //     ==> pointer p is tracked, but was removed from the stack, 
  //          using it is an error
   var ptrOnStack : MaybePointer;
   var tracked_tag : Tag;
   
   constructor() 
   {
     this.counter := 1;
     this.ptrOnStack := None;
     this.tracked_tag := Unique(0);
   }
   method newId() returns (ret: nat) 
   modifies this;
   {
     counter := counter + 1;
     ret := counter;
   }
   
   method push(p: Pointer)
   {
     if (*) 
     {
       this.tracked_tag := p.tag;
       this.ptrOnStack := Some(p);
     }
   }

   method use(p: Pointer) 
   requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
   {
     // if using a pointer with tracked_tag, and the pointer is 
     // not in the stack, then this is an error
     // all other cases are ok
     if (p.tag == this.tracked_tag) 
     {
       assert this.ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then the tracked pointer is removed 
       // from the stack
       match this.ptrOnStack
       case None => 
       case Some(ptr) => 
           assert ptr.tag == this.tracked_tag;
           assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(p)) 
           {
             this.ptrOnStack := None;
           }
     }
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
   

class Pointer 
{
  // -- address of this pointer
  var addr: nat;
  // -- the tag
  var tag: Tag;
  // -- immediate predecessor, or None if the pointer owns its memory
  var pred: MaybePointer;
  // -- some ancestor of the pointer
  // -- this is the prophecy of an intersting ancesstor
  var ancestor: MaybePointer;
  
  predicate valid(s: State)
  {
    true
  }
  
  constructor(addr: nat, tag: Tag, pred: Pointer, ances: Pointer) 
  {
    this.addr := addr;
    this.tag := tag;
    this.pred := Some(pred);
    this.ancestor := match ances 
                    case None => Some(pred)
                    case Some(p) => ances;
  }


  constructor(addr: nat, s: State) 
  {
    this.addr := addr;
    var id := s.newId();
    this.tag := Unique(id);
    this.pred := None;
    this.ancestor := None;
  }

  method mut_borrow(s: State) returns (p: Pointer) 
  {
    s.use(this);
    var ancestor := this;
    if (*) 
    {
      match this.ancestor
      case None => 
      case Some(t) => ancestor := t;
    }
    var id := s.newId();
    var np := new Pointer(p.addr, Unique(id), this, ancestor);
    s.push(np);
    return np;
  }

  method borrow(s: State) returns (p: Pointer) 
  {

    return new Pointer(this.addr, SharedRO(s.newId()));
  }

  method raw(s: State) returns (p: Pointer) 
  {
    return new Pointer(this.addr, SharedRW(s.newId()));
  }

  method write(val: int, s: State) 
  {
    this.use(s);

  }

  method read(s: State) returns (val: int)
  {
    this.use(s);

  }

  method use(s: State) 
  {
    s.use(this);
  }


}

