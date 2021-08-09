open OUnit2
open Prop.Verif

let notation = Prop.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;
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
