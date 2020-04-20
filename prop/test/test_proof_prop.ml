open OUnit2
open Prop
open Formula_prop
open Proof_prop

let x1,x2 = PVar (PVVar 1),PVar (PVVar 2)

let test_invalid_empty_proof test_ctxt =
        assert_raises ~msg:"Invalid empty proof" (Failure("Formula is not at the end of the proof")) (fun () -> proof_verification ~hyp:[] ~proof:[] x1)

let test_invalid_proof test_ctxt =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> proof_verification ~hyp:[] ~proof:[TPPFormula x1] x1)

let test_invalid_proof_length_2 test_ctxt =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> proof_verification ~hyp:[] ~proof:[TPPFormula x1;TPPFormula x2] x2)

let test_S1_Bourbaki test_ctxt =
  let _ = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\na \" \\implies \" b\nEnd"
  in
  let f = formula_from_string "((\\mathbb{A} \\lor \\mathbb{A})  =>  \\mathbb{A})  =>  ((\\lnot \\mathbb{A})  =>  \\lnot (\\mathbb{A} \\lor \\mathbb{A}))"
  in
  assert_bool "test_S1_Bourbaki" (proof_verification ~hyp:[] ~proof:[TPPFormula f] f)

let proof_prop_suite = "Proof prop" >:::
        [ "test invalid empty proof">::test_invalid_empty_proof;
          "test_invalid_proof">::test_invalid_proof;
          "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
          "test_S1_Bourbaki">::test_S1_Bourbaki
        ]


let () = 
        run_test_tt_main proof_prop_suite
