open OUnit2
open Kernel.Logic
open Kernel_prop_interp.Theory.Prop

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
    List.map (fun s -> Single(string_to_formula s)) [
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
  let theorem_chaining = {
    kind=Kernel.Logic.KTheorem;
    name="C6";
    params=[];
    premisses=[];
    conclusion= chaining;
    demonstration=demo_chaining
  }
  in
  let verif = (print_endline "avant verif chaining";verif  ~speed:Paranoid theorem_chaining)          
  in
  print_endline "apres verif chaining ";
  match verif with 
  | Ok th -> 
    theorems :=
      th
      :: !theorems
  | Error _ -> ()
;;
print_endline "apres C6";;
let add_idem =
  let idem = (string_to_formula "X_1 \\implies X_1") 
  and demo_idem = 
    (List.map (fun s -> Single (string_to_formula s)) [
        "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies 
    (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ]) in
  let theorem_unproved = 
    {
      kind = Kernel.Logic.KTheorem;
      name = "C8";
      params = [];
      premisses = [];
      demonstration = demo_idem;
      conclusion = idem;
    }
  in
  let verif = (verif  ~speed:Paranoid theorem_unproved)
  in
  match verif 
  with 
  | Ok (Theorem theorem) ->
    theorems :=
      (Theorem {theorem with kind = KTheorem}) :: !theorems
  | Error _ -> ()
;;

(*non A  \\implies  non B  \\implies   B  \\implies  A*)
let demo_contraposition = List.map (fun f -> Single (string_to_formula f)) [

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
  ]
in
let theorem_contraposition_unproved = {
  kind = KUnproved;
  name ="contraposition";
  params = [];
  premisses = [];
  demonstration = demo_contraposition ;
  conclusion=string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
in
let verif =
  verif ~speed:Fast theorem_contraposition_unproved 
in 
match verif 
with 
| Ok (Theorem theorem) ->
  theorems := 
    (Theorem {theorem with kind = KTheorem}) ::!theorems
| Error _ -> ()
;;

let f_unproved_demo = List.map (fun s -> Single(string_to_formula s)) [
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
  ] 
and f_unproved = string_to_formula "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}"
let f() =

  verif ~speed:Paranoid {kind=KUnproved;name="";params=[];premisses=[];demonstration=f_unproved_demo; conclusion=f_unproved}

let g_unproved =(string_to_formula "(\\mathbf{A} \\lor \\mathbf{A}) => \\mathbf{A}")
and g_unproved_demo =
  (List.map (fun s -> Single(string_to_formula s)) [
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
let g() = verif ~speed:Paranoid {kind=KUnproved;name="";params=[];premisses=[];demonstration=g_unproved_demo; conclusion=g_unproved}

let test_without_notation _ =
  assert_equal ~printer:(function Ok _ -> "Ok" | Error (error,_) -> error) 
    (Ok (Theorem{kind=KUnproved;name="";params=[];premisses=[];conclusion=f_unproved;demonstration = compile ~speed:Paranoid ~demonstration:f_unproved_demo ()})) 
    (f())

let test_with_notation _ =
  assert_equal ~printer:(function Ok _ -> "Ok" | Error (error,_) -> error)
    (Ok (Theorem {kind=KUnproved;name="";params=[];premisses=[];conclusion=g_unproved;demonstration = compile ~speed:Paranoid ~demonstration:g_unproved_demo ()}))
    (g())

let notation_suite =
  "Notation">:::
  [ "test_without_notation" >:: test_without_notation;
    "test_with_notation" >:: test_with_notation
  ]
;;

let () =
  run_test_tt_main notation_suite
