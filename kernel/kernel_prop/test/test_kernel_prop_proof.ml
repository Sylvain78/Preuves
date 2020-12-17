open OUnit2
open Kernel_prop.Verif
open Kernel_prop.Compile
open Prop.Formula_prop

let test_verif _ = 
  assert_equal ~printer:(function | Ok() -> "ok" | Error s -> "error : " ^ s) (Ok ()) (kernel_verif Prop.Axioms_prop.a1 [Ax (0,[])] [])

let test_compile _ =
  assert_equal {theorem = PImpl (PVar 3, PImpl(PVar 4, PVar 3));demonstration=[Ax (1, [1, PVar 3; 2, PVar 4])]} (compile_demonstration ~demo:[PImpl (PVar 3, PImpl(PVar 4, PVar 3))] ~theory:[])

let kernel_proof_suite =
        "kernel_proof test" >:::
                [ "test kernel_verif ">:: test_verif;
                  "test compile">:: test_compile
                ]


let () =
        run_test_tt_main kernel_proof_suite;
;;

