open OUnit2
open Base_term
open Formula
open Signature

module FormulaTest = struct
        include Formula(SignatureMinimal)
        let r = SignatureMinimal.of_string "s"
        let () = SignatureMinimal.binary_relations := [r]
end
open FormulaTest

let x1,x2,x3,x4 = V(Var 1), V(Var 2),V(Var 3), V(Var 4)
let f1 = Eq(x1, x2)
let f2 = Eq(x3, x4)

let g1 = Forall(Var 1, Atomic_formula(Eq(x1, x3)))

let nf1 = Neg (Atomic_formula f1)
let nf2 = Neg (Atomic_formula f2)

let test_initialization_printers_relations test_ctxt =
        assert_equal 0 (Hashtbl.length printers_relations)

let test_simultaneous_substitution_atomic_formula_eq test_ctxt =
        assert_equal f2 (simultaneous_substitution_atomic_formula [Var 1 ; Var 2] [x3 ; x4] f1)

let test_simultaneous_substitution_atomic_formula_relation test_ctxt =
        assert_equal (Relation(r,[x3 ; x4])) (simultaneous_substitution_atomic_formula [Var 1 ; Var 2] [x3 ; x4] (Relation(r, [x1 ; x2])))

let test_simultaneous_substitution_formula test_ctxt =
        assert_equal (Atomic_formula f2) (simultaneous_substitution_formula [Var 1 ; Var 2] [V(Var 3) ; V(Var 4)] (Atomic_formula f1))

let test_simultaneous_substitution_formula_neg test_ctxt =
        assert_equal nf2 (simultaneous_substitution_formula [Var 1 ; Var 2] [V(Var 3) ; V(Var 4)]  nf1)

let test_simultaneous_substitution_formula_and test_ctxt =
        assert_equal (And((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [Var 1 ; Var 2 ; Var 3 ;Var 4 ] [x3 ; x4 ; x1 ; x2] 
                     (And((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_or test_ctxt =
        assert_equal (Or((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [Var 1 ; Var 2 ; Var 3 ;Var 4 ] [x3 ; x4 ; x1 ; x2] 
                     (Or((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_imply test_ctxt =
        assert_equal (Imply((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [Var 1 ; Var 2 ; Var 3 ;Var 4 ] [x3 ; x4 ; x1 ; x2]
                     (Imply((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_forall_nominal test_ctxt =
        let f1 = (Forall(Var 1, Atomic_formula f1)) 
        in
        assert_equal (f1) (simultaneous_substitution_formula [Var 1 ] [x2]  f1)

let test_simultaneous_substitution_formula_forall_nominal_2 test_ctxt =
        let f1 = (Forall(Var 1, Atomic_formula f1)) 
        in
        assert_equal (g1) (simultaneous_substitution_formula [Var 2 ] [x3]  f1)

let formula_suite = "First order formula tests">:::
        [ 
        "Test of initialization of printers_relations">::test_initialization_printers_relations;
        "test_simultaneous_substitution_atomic_formula (case Eq) ">::test_simultaneous_substitution_atomic_formula_eq; 
        "test_simultaneous_substitution_atomic_formula (case Relation)">::test_simultaneous_substitution_atomic_formula_relation;
        "test_simultaneous_substitution_formula (case Atomic_formula">::test_simultaneous_substitution_formula;
        "test_simultaneous_substitution_formula_neg">::test_simultaneous_substitution_formula_neg;
        "test_simultaneous_substitution_formula_and">::test_simultaneous_substitution_formula_and;
        "test_simultaneous_substitution_formula_or">::test_simultaneous_substitution_formula_or;
        "test_simultaneous_substitution_formula_imply">::test_simultaneous_substitution_formula_imply;
        "test_simultaneous_substitution_formula_forall_nominal">::test_simultaneous_substitution_formula_forall_nominal;
        "test_simultaneous_substitution_formula_forall_nominal2">::test_simultaneous_substitution_formula_forall_nominal_2;
        ]

let () = run_test_tt_main formula_suite
