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
// The gooe_client is to find a counter example in the following case.
//  var s : State = new State();

    let mut local = 0;

    let x = &mut local;
//   var xp = s.generate_mutable_ref();
//   var xb = xp.mut_borrow(s, 0)

    let y = &mut local;
//   var yb = xp.mut_borrow(s, 0)   

    *x = 1;
//  xb.write(1, s);    
*/

method good_client()
{
  // spec: var s : State = new State();
  var counter := 0;
  var ptrOnStack := None;
  var tracked_tag := Unique(0, 0);
  var activeCallId := 0;
  
  // rust code: let mut local = 0;
  //            let x = &mut local;
  // spc:       var xp = s.generate_mutable_ref();
  var addr := 1;
  counter := counter + 1;
  var tag_id := counter;
  var xp : Pointer := new Pointer(1, Unique(tag_id, 0), None, None);

  // spec:      var xb = xp.mut_borrow(s, 0)
  /*------- inlining mut_borrow begin --------------------------------*/
  /*--------inlining use_mutable begin -------------------------------*/
  ptrOnStack := Some(xp); 
  tracked_tag := xp.tag;
  if (xp.tag == tracked_tag){
    assert ptrOnStack != None;
  } else{
    match ptrOnStack
       case None => 
       case Some(ptr) => 
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
  /*--------inlining use_mutable end -------------------------------*/
    counter := counter + 1;
    tag_id := counter; 
    var xb : Pointer := new Pointer(xp.addr, Unique(tag_id, 0), Some(xp), Some(xp));
    /*-------inlining push begin ----------------------------------*/
    // if (*) 
    //  {
    //    tracked_tag := xb.tag;
    //    ptrOnStack := Some(xb);
    //  }
    tracked_tag := xb.tag;
    ptrOnStack := Some(xb);
    /*-------inlining push end--------------------------------------*/

  /*------- inlining mut_borrow end --------------------------------*/

  // rust code: let y = &mut local;
  // spc:       var yb = xp.mut_borrow(s, 0);

  /*------- inlining mut_borrow begin --------------------------------*/
  /*--------inlining use_mutable begin -------------------------------*/
  if (xp.tag == tracked_tag){
    assert ptrOnStack != None;
  } else{
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
  /*--------inlining use_mutable end -------------------------------*/
    counter := counter + 1;
    tag_id := counter; 
    var yb : Pointer := new Pointer(xp.addr, Unique(tag_id, 0), Some(xp), Some(xp));
    /*-------inlining push begin ----------------------------------*/
    // if (*) 
    //  {
    //    tracked_tag := yb.tag;
    //    ptrOnStack := Some(yb);
    //  }
    
    /*-------inlining push end--------------------------------------*/

    /*------- inlining mut_borrow end --------------------------------*/

    /* Rust code: *x = 1; ------------------------*/
    /* Spec:       xb.write(1, s); ---------------*/
    /*-------inlining write begin----------------------------------*/
    /*--------inlining use_mutable begin -------------------------------*/
  
  if (xb.tag == tracked_tag){
    assert ptrOnStack != None;
  } else{
    match ptrOnStack
       case None => 
       case Some(ptr) => 
           assert ptr.ancestor == Some(xp);
           if (ptr.ancestor == Some(xp)) 
           { 
             
             match xp.tag {
             case Unique(_, c) => {assert c == 0;}
             case SharedRO(_, c) => {assert c == 0;}
             case SharedRW(_, c) => {assert c == 0;}
             }
             ptrOnStack := None;    
             
           }
  }
    /*--------inlining use_mutable end -------------------------------*/
    /*-------inlining write end----------------------------------*/
}