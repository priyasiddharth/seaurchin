// if the callid != 0, then it is protected
// it the callid == 0, the it is not protected
datatype Tag = Unique(t: nat, c: nat) | SharedRO(t: nat, c: nat) | SharedRW(t: nat, c: nat) 

datatype MaybePointer = None | Some(p:Pointer)

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
}

/*
// The client is to find a counter example in the following case.
// There is supposed to be no error.
//  var s : State = new State();

    let mut local = 0;

    let x = & local;
//   var xp = s.generate_sharedro_ref();
//   var xb = xp.shared_borrow(s, 0)

    let y = & local;
//   var yb = xp.shared_borrow(s, 0)   

    println!("xb is {}", *xb)
//  xb.read(s);    

    println!("yb is {}", *yb) 
 //  yb.read(s);

*/
method client(){
  // spec: var s : State = new State();
  var counter := 0;
  var ptrOnStack := None;
  var tracked_tag := Unique(0, 0);
  var activeCallId := 0;

  // rust code: let mut local = 0;
  //            let x = & local;
  // spc:       let x = s.generate_sharedro_ref();
  //            var xb = xp.shared_borrow(s, 0)
  var addr := 1;
  counter := counter + 1;
  var tag_id := counter;
  var xp : Pointer := new Pointer(1, SharedRO(tag_id, 0), None, None);

  /*------- inlining shared_borrow begin --------------------------------*/
  assert !xp.tag.SharedRW?; 
    if(xp.tag.Unique?){
        // shared-borrow from a mutable reference  
   /*------- inlining use_mutable begin -------------------------------------*/     
   if (xp.tag == tracked_tag) 
     {
       assert ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then 
       ///// if the tracked pointer is protected, then this is an error 
       ////  else it is removed from the stack
       match ptrOnStack
       case None => 
       case Some(ptr) => 
           // assert ptr.tag == this.tracked_tag;  
           // assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(xp)) 
           {
             match xp.tag{
             case Unique(_, c) => assert c == 0;
             case SharedRO(_, c) => assert c == 0;
             case SharedRW(_, c) => assert c == 0;
             }
             ptrOnStack := None;
           }

     }
    /*------ inlining use_mutable end --------------------------------------*/     
       
    } else if (xp.tag.SharedRO?){
        // shared-borrow from a SharedRO reference
        /*---------- inlining use_sharero begin--------------*/
        assert(xp.tag.SharedRO?);
        // if using a pointer with tracked_tag, and the pointer is 
        // not in the stack, then this is an error
        // all other cases are ok
        if (xp.tag == tracked_tag) 
        {
          assert ptrOnStack != None;
        } 
        else
        {
          // if tracked pointer is on stack, and its predecessor 
          // is being used, then
          //// if the predecessor is mutable_borrow, then 
          //////// if tracked pointer is protected, then this is an error
          //////// othersie tracked pointer is removed from the stack
          //// otherwise do nothing

          match ptrOnStack{
          case None => 
          case Some(ptr) => 
              if (ptr.ancestor == Some(xp) && xp.tag.Unique?) 
              {
                match xp.tag{
                case Unique(t, c) => assert c == 0;
                }
                ptrOnStack := None;
              }
          }
      }
      /*-------------inlining use_sharero end--------------------------*/
    } 
    /*
     var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    */
    counter := counter + 1;
    tag_id := counter;
    var xb := new Pointer(xp.addr, SharedRO(tag_id, 0), Some(xp), Some(xp));   

    tracked_tag := xb.tag;
    ptrOnStack := Some(xb);
   
   // rust code: let x = & local;
   // spec: var yb = xp.shared_borrow(s, 0);
   /*------- inlining shared_borrow begin --------------------------------*/
  assert !xp.tag.SharedRW?; 
    if(xp.tag.Unique?){
        // shared-borrow from a mutable reference  
   /*------- inlining use_mutable begin -------------------------------------*/     
   if (xp.tag == tracked_tag) 
     {
       assert ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then 
       ///// if the tracked pointer is protected, then this is an error 
       ////  else it is removed from the stack
       match ptrOnStack
       case None => 
       case Some(ptr) => 
           // assert ptr.tag == this.tracked_tag;  
           // assert p.tag != ptr.tag;
           if (ptr.ancestor == Some(xp)) 
           {
             match xp.tag{
             case Unique(_, c) => assert c == 0;
             case SharedRO(_, c) => assert c == 0;
             case SharedRW(_, c) => assert c == 0;
             }
             ptrOnStack := None;
           }

     }
    /*------ inlining use_mutable end --------------------------------------*/     
       
    } else if (xp.tag.SharedRO?){
        // shared-borrow from a SharedRO reference
         /*---------- inlining use_sharero begin--------------*/
        assert(xp.tag.SharedRO?);
        // if using a pointer with tracked_tag, and the pointer is 
        // not in the stack, then this is an error
        // all other cases are ok
        if (xp.tag == tracked_tag) 
        {
          assert ptrOnStack != None;
        } 
        else
        {
          // if tracked pointer is on stack, and its predecessor 
          // is being used, then
          //// if the predecessor is mutable_borrow, then 
          //////// if tracked pointer is protected, then this is an error
          //////// othersie tracked pointer is removed from the stack
          //// otherwise do nothing

          match ptrOnStack{
          case None => 
          case Some(ptr) => 
              if (ptr.ancestor == Some(xp) && xp.tag.Unique?) 
              {
                match xp.tag{
                case Unique(t, c) => assert c == 0;
                }
                ptrOnStack := None;
              }
          }
      }
    } 
    /*
     var ancestor := Some(this);
    if (*) 
    {
      ancestor := this.ancestor;
    }
    */
    counter := counter + 1;
    tag_id := counter;
    var yb := new Pointer(xp.addr, SharedRO(tag_id, 0), Some(xp), Some(xp));   

    tracked_tag := yb.tag;
    ptrOnStack := Some(yb);
   
    // Rust code: println!("xb is {}", *xb)
    // spec: xb.read(s);  
    /*----- inlining use_shareread begin ----------------------*/
    assert(xb.tag.SharedRO?);
     // if using a pointer with tracked_tag, and the pointer is 
     // not in the stack, then this is an error
     // all other cases are ok
     if (xb.tag == tracked_tag) 
     {
       assert ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then
       //// if the predecessor is mutable_borrow, then 
       //////// if tracked pointer is protected, then this is an error
       //////// othersie tracked pointer is removed from the stack
       //// otherwise do nothing

       match ptrOnStack{
       case None => 
       case Some(ptr) => 
           if (ptr.ancestor == Some(xb) && xb.tag.Unique?) 
           {
             match xb.tag{
             case Unique(t, c) => assert c == 0;
             }
             ptrOnStack := None;
           }
       }

     }
    /*----- inlining use_shareread end ----------------------*/

    // Rust code: println!("yb is {}", *yb)
    // spec: yb.read(s);  
    /*----- inlining use_shareread begin ----------------------*/
    assert(yb.tag.SharedRO?);
     // if using a pointer with tracked_tag, and the pointer is 
     // not in the stack, then this is an error
     // all other cases are ok
     if (yb.tag == tracked_tag) 
     {
       assert ptrOnStack != None;
     } 
     else
     {
       // if tracked pointer is on stack, and its predecessor 
       // is being used, then
       //// if the predecessor is mutable_borrow, then 
       //////// if tracked pointer is protected, then this is an error
       //////// othersie tracked pointer is removed from the stack
       //// otherwise do nothing

       match ptrOnStack{
       case None => 
       case Some(ptr) => 
           if (ptr.ancestor == Some(yb) && yb.tag.Unique?) 
           {
             match yb.tag{
             case Unique(t, c) => assert c == 0;
             }
             ptrOnStack := None;
           }
       }

     }
    /*----- inlining use_shareread end ----------------------*/



    

}