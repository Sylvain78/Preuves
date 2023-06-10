open OUnit2
open Prop.Formula_prop
open Prop.Verif

let x1,x2 = PVar 1,PVar 2

let test_invalid_empty_proof _ =
        assert_raises ~msg:"Invalid empty proof" (Failure("Formula is not at the end of the proof")) (fun () -> prop_proof_verif ~proof:[] x1)

let test_invalid_proof _ =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> prop_proof_verif ~proof:[Step  x1] x1)

let test_invalid_proof_length_2 _ =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> prop_proof_verif ~proof:[Step x1;Step x2] x2)

let test_invalid_proof_length_2_hyp _ =
        assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x2,[x1;x2])) (fun () -> prop_proof_verif ~hypotheses:[x1] ~proof:[Step x1;Step x2] x2)

let test_S1_Bourbaki _ =
  (*let _ = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"\\implies\" b\nSemantics\na \" \\implies \" b\nEnd"
  in*)
  let f = formula_from_string "((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A} \\lor \\mathbf{A}))"
  in
  assert_bool "test_S1_Bourbaki" (prop_proof_verif ~axioms:!axioms_prop ~proof:[Step f] f)

let proof_prop_suite = "Proof prop" >:::
        [ "test invalid empty proof">::test_invalid_empty_proof;
          "test_invalid_proof">::test_invalid_proof;
          "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
          "test_invalid_proof_length_2_hyp">::test_invalid_proof_length_2_hyp; 
          "test_S1_Bourbaki">::test_S1_Bourbaki
        ]


let () = 
        run_test_tt_main proof_prop_suite
