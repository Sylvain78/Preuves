open OUnit2
open Kernel_prop_interp.Prop_theory.Prop

let _ = print_endline "avant notation";;

let notation = Kernel_prop_interp.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;


(* 
   |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
*)
let add_chaining =
  let chaining =
    string_to_formula "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
  let demo_chaining = 
    List.map (fun s -> string_to_formula s) [
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
  let verif = (print_endline "avant verif chaining";verif ~theorems:!theorems () ~formula:chaining ~proof:demo_chaining)          
  in
  print_endline "apres verif chaining ";
  match verif with 
  | Ok() -> 
    theorems :=
      {
        kind = Kernel_prop_interp.Prop_theory.Prop.Theorem;
        name = "C6";
        params = [];
        premisses = [];
        demonstration = demo_chaining;
        conclusion = chaining;
      }
      :: !theorems
  | Error _ -> ()
;;
print_endline "apres C6";;
let add_idem =
  let idem = (string_to_formula "X_1 \\implies X_1") 
  and demo_idem = 
    (List.map (fun s -> string_to_formula s) [
        "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies 
    (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ]) in
  let verif = (verif  ~formula:idem ~theorems:!theorems ~proof:demo_idem ())
  in
  match verif 
  with 
  | Ok() ->
    theorems :=
      {
        kind = Kernel_prop_interp.Kind_prop.Theorem;
        name = "C8";
        params = [];
        premisses = [];
        demonstration = demo_idem;
        conclusion = idem;
      }
      :: !theorems
  | Error _ -> ()
;;

(*non A  \\implies  non B  \\implies   B  \\implies  A*)
let verif =
  verif  ~theorems:!theorems ~formula:(string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))")
    ~proof:(List.map (fun s -> string_to_formula s) [

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
      ]) ()
in 
match verif 
with 
| Ok() ->
  theorems := {
    kind = Assumed;
    name ="contraposition";
    params = [];
    premisses = [];
    demonstration = [];
    conclusion=string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
    ::!theorems
| Error _ -> ()
;;

let f() = verif  ~theorems:!theorems
    ~formula:(string_to_formula "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}")
    ~proof:(List.map (fun s -> string_to_formula s) [
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
      ]) ()

let g() = verif  ~theorems:!theorems
    ~formula:(string_to_formula "(\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}")
    ~proof:(List.map (fun s -> string_to_formula s) [
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
      ]) ()


let test_without_notation _ =
  assert_equal (Error "without notation : failed") (f())

let test_with_notation _ =
  assert_equal (Error "with notation : failed") (g())

let notation_suite =
  "Notation">:::
  [ "test_without_notation" >:: test_without_notation;
    "test_with_notation" >:: test_with_notation
  ]
;;

let () =
  run_test_tt_main notation_suite
