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
  // read ==> SharedROs are all adjacent at the top 
   var ptrOnStack : MaybePointer;
   var tracked_tag : Tag;
   var read : bool;   
   
   constructor() 
   {
     this.counter := 1;
     this.ptrOnStack := None;
     this.tracked_tag := Unique(0);
     this.read := false;
   }
   method newId() returns (ret: nat) 
   modifies this;
   {
     counter := counter + 1;
     ret := counter;
   }
   
   method push(p: Pointer)
   modifies this;
   {
     read := false;
     if (*) 
     {
       this.tracked_tag := p.tag;
       this.ptrOnStack := Some(p);
     }
   }

   // for mutable borrow
   method use_mutable(p: Pointer) 
   requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
   modifies this;
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

        this.read := false;   
     }
   }

   method use_raw(p: Pointer) 
   requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
   modifies this;
   {
      assert !read;
      // if using a pointer with tracked_tag, and the pointer is 
     // not in the stack, then this is an error
     // all other cases are ok
     if (p.tag == this.tracked_tag) 
     {
       assert this.ptrOnStack != None;
     } 
   }

   method use_shareread(p: Pointer)
   modifies this;
   {
    // check if SharedROs are all adjacent at the top
     assert read;
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
    
  constructor(addr: nat, tag: Tag, pred: Pointer, ances: MaybePointer) 
  {
    this.addr := addr;
    this.tag := tag;
    this.pred := Some(pred);
    this.ancestor := ances;
  }

  method mut_borrow(s: State) returns (np: Pointer) 
  modifies s;
  {
    if (!this.tag.Unique?){
        assert false;
    }
    s.use_mutable(this);
    var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    var id := s.newId();
    np := new Pointer(this.addr, Unique(id), this, ancestor);
    s.push(np);
    return np;
  }

  method share_borrow(s: State) returns (np: Pointer)
  modifies s;
  {
    if(this.tag.Unique?){
        // shared-borrow from a mutable reference  
        s.use_mutable(this);
        s.read := true;
    } else if (this.tag.SharedRO?){
        // shared-borrow from a SharedRO reference
        s.use_shareread(this);
    } else{
        assert false;
    }
     var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    var id := s.newId();
    np := new Pointer(this.addr, SharedRO(id), this, ancestor);
    s.push(np);
        
    return np;
  }
  
  method raw_borrow(s: State) returns (np: Pointer)
  requires this.tag.SharedRW?
  {
      // we can only raw borrow from SharedRW
      if (!this.tag.SharedRW?){
          assert false;
      }
      var ancestor := Some(this);
      if(*){
          ancestor := this.ancestor;
      }
      var id := s.newId();
      np := new Pointer(this.addr, SharedRO(id), this, ancestor);
      s.push(np);
       
      return np;
  }
  
  method write(val: int, s: State) 
  modifies s;
  {
    this.use(s);

  }

  method read(s: State) returns (val: int)
  modifies s;
  {
    this.use(s);

  }

  method use(s: State) 
  modifies s;
  {
      match this.tag
      case Unique? => s.use_mutable(this);
      case SharedRO? => s.use_shareread(this);
  }


}

