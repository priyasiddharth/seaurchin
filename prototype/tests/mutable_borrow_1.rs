fn main{
    let mut local = 0;
    let x = &mut local;
    let y = &mut *x;
    *x = 1;
    *y = 2;
}