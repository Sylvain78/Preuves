open OUnit2
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Verif

let x1,x2 = PVar 1,PVar 2

let test_invalid_empty_proof _ =
        assert_raises ~msg:"Invalid empty proof" (Failure("Formula is not at the end of the proof")) (fun () -> kernel_prop_interp_verif ~proof:[] x1)

let test_invalid_proof _ =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> kernel_prop_interp_verif ~proof:[x1] x1)

let test_invalid_proof_length_2 _ =
  assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x1,[x1])) (fun () -> kernel_prop_interp_verif ~proof:[x1;x2] x2)

let test_invalid_proof_length_2_hyp _ =
        assert_raises ~msg:"Invalid proof" (Invalid_demonstration (x2,[x1;x2])) (fun () -> kernel_prop_interp_verif ~hypotheses:[x1] ~proof:[x1;x2] x2)

let test_S1_Bourbaki _ =
  (*let _ = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"\\implies\" b\nSemantics\na \" \\implies \" b\nEnd"
  in*)
  let f = formula_from_string "((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A} \\lor \\mathbf{A}))"
  in
  assert_bool "test_S1_Bourbaki" (kernel_prop_interp_verif ~axioms:!axioms_prop ~proof:[f] f)

let proof_prop_suite = "Proof prop" >:::
        [ "test invalid empty proof">::test_invalid_empty_proof;
          "test_invalid_proof">::test_invalid_proof;
          "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
          "test_invalid_proof_length_2_hyp">::test_invalid_proof_length_2_hyp; 
          "test_S1_Bourbaki">::test_S1_Bourbaki
        ]


let () = 
        run_test_tt_main proof_prop_suite
