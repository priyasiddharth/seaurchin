fn main{
//  var s : State = new State();

    let mut local = 0;

    let x = &mut local;
//   var xp = s.generate_mutable_ref();
//   var xb = xp.mut_borrow(s, 0)

    let y = &mut *x;
//   var yb = xp.mut_borrow(s, 0)   

    *x = 1;
//  xb.write(1, s);    

    *y = 2;
//   yb.write(2, s);  
}