open OUnit2
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Prop_parser
open Kernel_prop_interp.Formula_tooling

let test_parenthesis _ = 
  assert_equal (PVar 1) (formula_from_string "(X_1)")

let test_x1 _ =
  assert_equal (formula_from_string "X_1") (PVar 1);
  assert_equal (formula_from_string " X_1 ") (PVar 1)

let test_x1_implies_x1 _ =
  assert_equal (PImpl (PVar 1, PVar 1)) (formula_from_string "X_1 \\implies X_1")  ~printer:to_string_formula_prop

let parser_formula_suite =
  "parser test" >:::
  [ 
    "test parenthesis ">:: test_parenthesis;
    "test x1" >:: test_x1;
    "test_x1_implies_x1" >:: test_x1_implies_x1;
  ]


let () =
  run_test_tt_main parser_formula_suite;
;;
