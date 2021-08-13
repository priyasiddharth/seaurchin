extern crate verification_annotations as verifier;

fn bing(v: &mut Vec<&mut usize>) -> usize {
    v.iter_mut().enumerate().for_each(|(idx, e)| {
        **e = idx;
    });
    return *(v[0]);
}

macro_rules! startup {
    ($sz: expr) => {
        let mut v: Vec<&mut usize> = Vec::new();
        let mut p = [0; 2 * $sz];
        for chunk in p.chunks_mut(2) {
            let idx: usize = verifier::AbstractValue::abstract_where(|&x| x == 0 || x == 1);
            v.push(&mut chunk[idx]);
        }
        let r = bing(&mut v);
        verifier::assert!(r == 0);
    };
}

#[test]
fn test_small() {
    startup!(100);
}

fn main() {}

// struct Bong {
//     x: i32,
//     y: i32,
//     z: i32,
// }

// fn main() {
//     let mut bing = Bong { x: 1, y: 2, z: 3 };
//     let toss: bool = verifier::AbstractValue::abstract_where(|x| *x == true || *x == false);
//     let (a, b) = if toss {
//         (&mut bing.x, &mut bing.y)
//     } else {
//         (&mut bing.y, &mut bing.x)
//     };
//     let c = &mut bing.z;
//     *a = -1;
//     *b = -2;
//     *a = -3;
//     verifier::assert!(*c == 3);
// }
