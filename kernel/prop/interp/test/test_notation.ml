open OUnit2
open Kernel_prop_interp.Verif

let _ = print_endline "avant notation";;

let notation = Kernel_prop_interp.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;


(* 
   |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
*)
let add_chaining =
  let chaining =
    formula_from_string "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
  let demo_chaining = 
    List.map (fun s -> formula_from_string s) [
      "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";
      "((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies  (X_1 \\implies (X_2 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      (*k*)
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)))";

      (*s*)
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))  \\implies 
    (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
    ] 
  in
  let verif = (print_endline "avant verif chaining";kernel_prop_interp_verif ~axioms:!axioms_prop ~theorems:!theorems_prop chaining ~proof:demo_chaining)          
  in
  print_endline "apres verif chaining ";
  if verif then
    theorems_prop :=
      {
        kind_prop = Kernel_prop_interp.Kind_prop.Theorem;
        name_theorem_prop = "C6";
        proof_prop = demo_chaining;
        conclusion_prop = chaining;
      }
      :: !theorems_prop
;;
print_endline "apres C6";;
let add_idem =
  let idem = (formula_from_string "X_1 \\implies X_1") 
  and demo_idem = 
    (List.map (fun s -> formula_from_string s) [
        "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies 
    (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ]) in
  let verif = (kernel_prop_interp_verif ~axioms:!axioms_prop idem ~theorems:!theorems_prop ~proof:demo_idem)          
  in
  if verif then
    theorems_prop :=
      {
        kind_prop = Kernel_prop_interp.Kind_prop.Theorem;
        name_theorem_prop = "C8";
        proof_prop = demo_idem;
        conclusion_prop = idem;
      }
      :: !theorems_prop
;;

(*non A  \\implies  non B  \\implies   B  \\implies  A*)
let verif =
  kernel_prop_interp_verif ~axioms:!axioms_prop ~theorems:!theorems_prop (formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))")
    ~proof:(List.map (fun s -> formula_from_string s) [

        "((\\lnot (\\lnot X_1)) \\implies X_1)";
        "((\\lnot (\\lnot X_1)) \\implies X_1) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1))";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))  \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))  \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
        "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)";
        "(X_2 \\implies \\lnot (\\lnot X_2))";
        "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2)))";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))";
        "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
        "((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies  (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))  \\implies  ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1)))";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)))";
        "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1))";
        "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)";
        "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))))";
        "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
        "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
        "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";
      ])
in 
if verif then 
  theorems_prop := {
    kind_prop = Assumed;
    name_theorem_prop="contraposition";
    proof_prop = [];
    conclusion_prop=formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
    ::!theorems_prop
;;

let f() = kernel_prop_interp_verif ~axioms:!axioms_prop ~theorems:!theorems_prop
    (formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}")
    ~proof:(List.map (fun s -> formula_from_string s) [
        "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))";
        "((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
        "((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
        "((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A}))";
        "(((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
        "((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})";
        "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}";
      ])

let g() = kernel_prop_interp_verif ~axioms:!axioms_prop ~theorems:!theorems_prop
    (formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}")
    ~proof:(List.map (fun s -> formula_from_string s) [
        "((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))";
        "((\\lnot \\mathbf{A}) => ((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}))";
        "((\\lnot \\mathbf{A}) => ((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A})) => ((((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) => ((\\lnot \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) => ((\\lnot \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
        "((\\lnot \\mathbf{A}) => ((\\lnot \\mathbf{A}) => \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) => (((\\lnot \\mathbf{A}) => (\\lnot \\mathbf{A})) => ((\\lnot \\mathbf{A}) => (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) => (\\lnot \\mathbf{A}))";
        "(((\\lnot \\mathbf{A}) => (\\lnot \\mathbf{A})) => ((\\lnot \\mathbf{A}) => (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
        "((\\lnot \\mathbf{A}) => (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
        "((\\lnot \\mathbf{A}) => (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) => ((\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A})";
        "(\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}";
      ])


let test_without_notation _ =
  assert_bool "without notation : failed" (f())

let test_with_notation _ =
  assert_bool "with notation : failed" (g())

let notation_suite =
  "Notation">:::
  [ "test_without_notation" >:: test_without_notation;
    "test_with_notation" >:: test_with_notation
  ]
;;

let () =
  run_test_tt_main notation_suite
