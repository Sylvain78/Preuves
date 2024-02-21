open OUnit2
open Kernel.Logic
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Theory.Prop

let x1,x2 = PVar 1,PVar 2

let print_result = function
  | Ok _ -> "Ok"
  | Error (m,e) -> m ^ ( match print_invalid_demonstration e with None -> "" | Some s -> s)

let test_invalid_empty_proof _ =
  let invalid_empty_theorem = {
    kind = Kernel.Logic.KUnproved;
    name = "invalid";
    params=[];
    premisses=[];
    conclusion=x1;
    demonstration=[]
  }
  in
  assert_equal 
    ~printer:print_result 
    ~msg:"Invalid empty proof"
    (Error ("Formula is not at the end of the proof",Invalid_demonstration(invalid_empty_theorem))) 
    (verif  ~speed:Paranoid invalid_empty_theorem)

let test_invalid_proof _ =
  let invalid_theorem = {
    kind = Kernel.Logic.KUnproved;
    name = "invalid";
    params=[];
    premisses=[];
    conclusion=x1;
    demonstration=[Single x1]
  }
  in
  assert_equal ~printer:print_result (Error ("Invalid demonstration", Invalid_demonstration(invalid_theorem))) ~msg:"Invalid proof"
    (verif ~speed:Paranoid invalid_theorem)

let test_invalid_proof_length_2 _ =
  let invalid_proof_length_2_theorem = {
    kind = Kernel.Logic.KUnproved;
    name = "invalid";
    params=[];
    premisses=[];
    conclusion=x2;
    demonstration=[Single x1;Single x2]
  }
  in
  assert_equal ~printer:print_result ~msg:"Invalid proof" 
    (Error ("Invalid demonstration", Invalid_demonstration({ invalid_proof_length_2_theorem with conclusion=x1 ; demonstration=[Single x1]})))
    (verif ~speed:Paranoid invalid_proof_length_2_theorem)

let test_invalid_proof_length_2_hyp _ =
  let invalid_proof_length_2_hyp_theorem = {
    kind = Kernel.Logic.KUnproved;
    name = "invalid";
    params=[];
    premisses=[x1];
    conclusion=x2;
    demonstration=[Single x1;Single x2]
  }
  in
  assert_equal ~printer:print_result ~msg:"Invalid proof" 
    (Error ("Invalid demonstration", Invalid_demonstration(invalid_proof_length_2_hyp_theorem))) 
    (verif ~speed:Paranoid invalid_proof_length_2_hyp_theorem)

let test_S1_Bourbaki _ =
  (*let _ = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"\\implies\" b\nSemantics\na \" \\implies \" b\nEnd"
    in*)
  let f = string_to_formula "((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A} \\lor \\mathbf{A}))"
  in
  let s1_unproved = {kind=KUnproved;name="S1";params=[];premisses=[];conclusion=f; demonstration=[Single f]}
  in
  assert_equal ~msg:"test_S0_Bourbaki"
    (Ok (Theorem {kind=KUnproved;name="S1";params=[];premisses=[];conclusion=f; demonstration=Demonstration[[f], Single f]}))
    (verif ~speed:Paranoid s1_unproved)

let proof_prop_suite = "Proof prop" >:::
                       [ "test invalid empty proof">::test_invalid_empty_proof;
                         "test_invalid_proof">::test_invalid_proof;
                         "test_invalid_proof_length_2">::test_invalid_proof_length_2; 
                         "test_invalid_proof_length_2_hyp">::test_invalid_proof_length_2_hyp; 
                         "test_S1_Bourbaki">::test_S1_Bourbaki
                       ]


let () = 
  run_test_tt_main proof_prop_suite
