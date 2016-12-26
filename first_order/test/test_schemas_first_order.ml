open OUnit2
open Base_term
open Formula
open Signature
open Util

module FormulaTest = struct
        include Formula(SignatureMinimal)
        let r = SignatureMinimal.of_string "s"
        let () = SignatureMinimal.binary_relations := [r]
end
open FormulaTest

let v1 = Var (new_var())
let v2 = Var (new_var())
let v3 = Var (new_var())
let v4 = Var (new_var())

let x1,x2,x3,x4 = V v1, V v2, V v3, V v4
let f1 = Eq(x1, x2)
let f2 = Eq(x3, x4)

let g1 = Forall(v1, Atomic_formula(Eq(x1, x2)))
let g2 = Exists(v1, Atomic_formula(Eq(x1, x2)))

let nf1 = Neg (Atomic_formula f1)
let nf2 = Neg (Atomic_formula f2)

let test_ test_ctxt =


        let test_suite = "Schemas test suite">::: []

        let () = run_test_tt_main test_suite
