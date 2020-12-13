open OUnit2
open Kernel_prop.Kernel_prop_proof

let test_verif _ = 
  assert_equal ~printer:(function | Ok() -> "ok" | Error s -> "error : " ^ s) (Ok ()) (kernel_verif Prop.Axioms_prop.a1 [Ax (0,[])] [])

let kernel_proof_suite =
        "kernel_proof test" >:::
                [ "test kernel_verif ">:: test_verif;
                ]


let () =
        run_test_tt_main kernel_proof_suite;
;;

