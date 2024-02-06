open OUnit2
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Theory.Prop

let x1,x2 = PVar 1,PVar 2

let print_result = function
  | Ok _ -> "Ok"
  | Error (m,e) -> m ^ ( match print_invalid_demonstration e with None -> "" | Some s -> s)

let test_invalid_empty_proof _ =
  assert_equal 
    ~printer:print_result 
    ~msg:"Invalid empty proof"
    (Error ("Formula is not at the end of the proof",Invalid_demonstration(x1,[],[],[]))) 
    (verif ~proof:[] ~formula:x1 ())

let test_invalid_proof _ =
  assert_equal ~printer:print_result (Error ("Invalid demonstration", Invalid_demonstration(x1,[],[],[x1]))) ~msg:"Invalid proof"  (verif ~proof:[x1] ~formula:x1 ())

let test_invalid_proof_length_2 _ =
  assert_equal ~printer:print_result ~msg:"Invalid proof" 
    (Error ("Invalid demonstration", Invalid_demonstration(x1,[],[],[x1])))
    (verif ~proof:[x1;x2] ~formula:x2 ())

let test_invalid_proof_length_2_hyp _ =
  assert_equal ~printer:print_result ~msg:"Invalid proof" 
    (Error ("Invalid demonstration", Invalid_demonstration(x2,[],[x1],[x1;x2]))) 
    (verif ~hypotheses:[x1] ~proof:[x1;x2] ~formula:x2 ())

let test_S1_Bourbaki _ =
  (*let _ = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"\\implies\" b\nSemantics\na \" \\implies \" b\nEnd"
    in*)
  let f = string_to_formula "((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A} \\lor \\mathbf{A}))"
  in
  assert_equal (Ok()) ~msg:"test_S0_Bourbaki" (verif ~proof:[f] ~formula:f ())

let proof_prop_suite = "Proof prop" >:::
                       [ "test invalid empty proof">::test_invalid_empty_proof;
                         "test_invalid_proof">::test_invalid_proof;
                         "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
                         "test_invalid_proof_length_2_hyp">::test_invalid_proof_length_2_hyp; 
                         "test_S1_Bourbaki">::test_S1_Bourbaki
                       ]


let () = 
  run_test_tt_main proof_prop_suite
