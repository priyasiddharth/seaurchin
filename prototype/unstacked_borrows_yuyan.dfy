// if the callid != 0, then it is protected
// it the callid == 0, the it is not protected
datatype Tag = Unique(t: nat, c: nat) | SharedRO(t: nat, c: nat) | SharedRW(t: nat, c: nat) 

datatype MaybePointer = None | Some(p:Pointer)

class State {
  // used to generate new tagid, callid and pointer's address
  // the Rust techical appedix use different counters for tagid and callid
   var counter: nat; 

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

   var activeCallId: nat;
      
   constructor() 
   {
     this.counter := 0;
     this.ptrOnStack := None;
     this.tracked_tag := Unique(0, 0);
     this.activeCallId := 0;
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
     if (*) 
     {
       this.tracked_tag := p.tag;
       this.ptrOnStack := Some(p);
     }
   }

    // this function is used to generate a mutable ref from a value
   // e.g., let mut local = 0
   //       let x = & mut loal;
   //       generate_mutable_ref();
   method generate_mutable_ref() returns(np: Pointer)
   modifies this;
   {
     var addr := this.newId(); 
     var tag_id := this.newId();
     
     np := new Pointer(addr, Unique(tag_id, activeCallId), None, None);   
   }

   // for mutable borrow
   method use_mutable(p: Pointer) 
 //  requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
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
       // is being used, then 
       ///// if the tracked pointer is protected, then this is an error 
       ////  else it is removed from the stack
       match this.ptrOnStack
       case None => 
       case Some(ptr) => 
           // assert ptr.tag == this.tracked_tag;  
           // assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(p)) 
           {
             match p.tag{
             case Unique(_, c) => assert c == 0;
             case SharedRO(_, c) => assert c == 0;
             case SharedRW(_, c) => assert c == 0;
             }
             this.ptrOnStack := None;
           }

     }
   }

   method use_raw(p: Pointer) 
 //  requires p.tag == this.tracked_tag ==> this.ptrOnStack != None
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
       // is being used, then
       //// if the predecessor is raw pointer, then this is an error
       //// if the predecessor is mutable borrow, then it is ok (do nothing)

       match this.ptrOnStack{
       case None => 
       case Some(ptr) => 
           assert ptr.tag == this.tracked_tag;
           assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(p) && p.tag.SharedRW?) 
           {
             assert false;
           }
       }   

     }
   }

   method use_shareread(p: Pointer)
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
       // is being used, then
       //// if the predecessor is mutable_borrow, then 
       //////// if tracked pointer is protected, then this is an error
       //////// othersie tracked pointer is removed from the stack
       //// otherwise do nothing

       match this.ptrOnStack{
       case None => 
       case Some(ptr) => 
           assert ptr.tag == this.tracked_tag;
           assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(p) && p.tag.Unique?) 
           {
             match p.tag
             case Unique(t, c) => assert c == 0;
             this.ptrOnStack := None;
           }
       }

     }
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
    
  constructor(addr: nat, tag: Tag, pred: MaybePointer, ances: MaybePointer) 
  ensures this.addr == addr && this.tag == tag && this.pred == pred && this.ancestor == ances;
    {
    this.addr := addr;
    this.tag := tag;
    this.pred := pred;
    this.ancestor := ances;
  }

  // if it is not protected, passing 0 to funID
  // othersie, passing the ID, which is greater than 0.
  method mut_borrow(s: State, funID: nat) returns (np: Pointer) 
  modifies s;
  {
    // assert !this.tag.Unique?; // debug: should uncomment it
    assume !this.tag.Unique?;
    s.use_mutable(this);
    var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    var id := s.newId();
    np := new Pointer(this.addr, Unique(id, funID), Some(this), ancestor);
    s.push(np);
    return np;
  }

  // if it is not protected, passing 0 to funID
  // othersie, passing the ID, which is greater than 0.
  method shared_borrow(s: State, funID: nat) returns (np: Pointer)
  modifies s;
  {
    assert !this.tag.SharedRW?; 
    if(this.tag.Unique?){
        // shared-borrow from a mutable reference  
        s.use_mutable(this);
    } else if (this.tag.SharedRO?){
        // shared-borrow from a SharedRO reference
      //  s.use_shareread(this);
    } 
     var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    var id := s.newId();
    np := new Pointer(this.addr, SharedRO(id, funID), Some(this), ancestor);
    s.push(np);
        
    return np;
  }
  
  // if it is not protected, passing 0 to funID
  // othersie, passing the ID, which is greater than 0.
  method raw_borrow(s: State, funID: nat) returns (np: Pointer)
 // requires this.tag.SharedRW?
  modifies s;
  {
      // we can only raw borrow from SharedRW
      assert !this.tag.SharedRW?; // debug: should uncomment it
      var ancestor := Some(this);
      if(*){
          ancestor := this.ancestor;
      }
      var id := s.newId();
      np := new Pointer(this.addr, SharedRW(id, funID), Some(this), ancestor);
      s.push(np);
       
      return np;
  }

  method initCall(s: State) returns(np: Pointer)
    modifies s;
  {
    var callId := s.newId();
    s.activeCallId := callId;
    np := retag(s, callId);
  }

  method endCall(s : State, oldCallId: nat)
    modifies s;
  {
    s.activeCallId := oldCallId;
  }

  method retag(s: State, funID: nat) returns(np: Pointer)
 // requires funID > 0;
  modifies s;
  {
      assert !this.tag.SharedRW?; 
      // retagging achieves the desried effect by basically performing a reborrow.
      // retagging only applies to mut_borrow and shared_borrow (page 41:17)
      match this.tag{
      case Unique(_, _) =>  np := mut_borrow(s, funID);
      case SharedRO(_, _) => np := shared_borrow(s, funID);
      }
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
      case Unique(_, _) => s.use_mutable(this);
      case SharedRO(_, _) => s.use_shareread(this);
      case SharedRW(_, _) => s.use_raw(this); 
  }
}



