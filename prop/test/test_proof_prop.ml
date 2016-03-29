open OUnit2
open Formula_prop
open Proof_prop

let x1,x2 = PVar 1,PVar 2

let test_invalid_empty_proof test_ctxt =
        assert_raises ~msg:"Invalid empty proof" (Failure("Formula is not at the end of the proof")) (fun () -> proof_verification ~hyp:[] ~proof:[] x1)

let test_invalid_proof test_ctxt =
        assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[])) (fun () -> proof_verification ~hyp:[] ~proof:[x1] x1)

let test_invalid_proof_length_2 test_ctxt =
        assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x2])) (fun () -> proof_verification ~hyp:[] ~proof:[x2;x1] x1)

let proof_prop_suite = "Proof prop" >:::
        [ "test invalid empty proof">::test_invalid_empty_proof;
          "test invalid proof">::test_invalid_proof;
          "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
        ]


let () = 
        run_test_tt_main proof_prop_suite;
