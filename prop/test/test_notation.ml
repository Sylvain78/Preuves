open OUnit2
open Prop.Verif

let notation = Prop.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;
(* 
   |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
*)
let add_chaining =
  let chaining =
    formula_from_string "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
  let demo_chaining = 
    List.map (fun s -> (formula_from_string s)) [
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
  let verif = (prop_proof_verif ~hyp:(List.map Prop.Verif.formula_from_string [])
                 chaining
                 ~proof:demo_chaining)          
  in
  if verif then
    begin
      print_string "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ\nZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ\n";
      theorems_prop :=
        {
          kind_prop = Prop.Kind_prop.Theorem;
          name_theorem_prop = "C6";
          proof_prop = demo_chaining;
          conclusion_prop = chaining;
        }
        :: !theorems_prop
    end
;;

let add_idem =
  let idem = (formula_from_string "X_1 \\implies X_1") 
  and demo_idem = 
    (List.map formula_from_string [
        "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies 
    (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ]) in
  let verif = (prop_proof_verif ~hyp:(List.map Prop.Verif.formula_from_string [])
                 idem
                 ~proof:demo_idem)          
  in
  if verif then
    begin
      print_string "ZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ\nZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZZ\n";
      theorems_prop :=
        {
          kind_prop = Prop.Kind_prop.Theorem;
          name_theorem_prop = "C8";
          proof_prop = demo_idem;
          conclusion_prop = idem;
        }
        :: !theorems_prop
    end
;;

let f() = prop_proof_verif ~hyp:[]
    (formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}")
    ~proof:(List.map formula_from_string [
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

let g() = prop_proof_verif ~hyp:[]
    (formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}")
    ~proof:(List.map formula_from_string [
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
