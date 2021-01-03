open Prop.Formula_prop
open OUnit2

open Kernel_prop.Compile
open Kernel_prop.Verif
let x1,x2 = PVar 1,PVar 2
let (=>) a b = PImpl(a,b)
let formula = x1=>x1
let demo =
  [ 
    (x1 =>((x1 => x1) => x1)) =>((x1 =>(x1 => x1)) =>(x1 => x1));
    x1 =>((x1 => x1) => x1);
    (x1 =>(x1 => x1)) =>(x1 => x1);
    x1 =>(x1 => x1);
    x1 => x1
  ]
let test = compile_demonstration ~theory:[] ~demo ();;

let test_cut _ =
  assert_equal {theorem=x2 ; demonstration=[Known 1 ; Known 2 ; Cut(1,2)]}
    (compile_demonstration ~demo:[x1; x1=>x2 ; x2] ~theory:[x1;x1=>x2] ())

let test_compile _ =
  assert_equal { theorem=formula ; demonstration=[ Known 1 ] }
    (compile_demonstration ~demo:[formula] ~theory:[formula] ())

let test_compile_a_implies_a _ =
  assert_equal 
    { theorem=formula ; 
      demonstration= [Ax (2, [(3, x1); (1, x1); (2, x1 => x1)]);
                      Ax (1, [(1, x1); (2, x1 => x1)]);
                      Cut (2, 1);
                      Ax (1, [(1, x1); (2, x1)]);
                      Cut (4, 3)]}

    (compile_demonstration ~demo:demo ())

let compile_suite =
  "compile test" >:::
  [ 
    "test cut" >:: test_cut;
    "test compile" >:: test_compile;
    "test_compile_a_implies_a" >:: test_compile_a_implies_a;
  ]

let () = 
  run_test_tt_main compile_suite
