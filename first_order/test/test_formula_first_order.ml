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

let test_initialization_printers_relations test_ctxt =
        assert_equal 0 (Hashtbl.length printers_relations)

let test_simultaneous_substitution_atomic_formula_eq test_ctxt =
        assert_equal f2 (simultaneous_substitution_atomic_formula [v1 ; v2] [x3 ; x4] f1)

let test_simultaneous_substitution_atomic_formula_relation test_ctxt =
        assert_equal (Relation(r,[x3 ; x4])) (simultaneous_substitution_atomic_formula [v1 ; v2] [x3 ; x4] (Relation(r, [x1 ; x2])))

let test_simultaneous_substitution_formula test_ctxt =
        assert_equal (Atomic_formula f2) (simultaneous_substitution_formula [v1 ; v2] [V(v3) ; V(v4)] (Atomic_formula f1))

let test_simultaneous_substitution_formula_neg test_ctxt =
        assert_equal nf2 (simultaneous_substitution_formula [v1 ; v2] [V(v3) ; V(v4)]  nf1)

let test_simultaneous_substitution_formula_and test_ctxt =
        assert_equal (And((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2] 
                     (And((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_or test_ctxt =
        assert_equal (Or((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2] 
                     (Or((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_imply test_ctxt =
        assert_equal (Imply((Atomic_formula f2), (Atomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2]
                     (Imply((Atomic_formula f1), (Atomic_formula f2))))

let test_simultaneous_substitution_formula_forall_nominal test_ctxt =
        let ff1 = (Forall(v1, Atomic_formula f1)) 
        in
        let f'1= (simultaneous_substitution_formula [v1 ] [x2]  ff1)
        in
        let new_variable = match f'1 with Forall(v,_) -> v | _ -> failwith "unreachable"
        in
        assert_equal (Forall(new_variable, Atomic_formula(Eq(V new_variable, x2)))) f'1

let test_simultaneous_substitution_formula_forall_nominal_2 test_ctxt =
        let ff2 = (Forall(v1, Atomic_formula f1)) 
        in
        let f'2 = (simultaneous_substitution_formula [v1 ; v2 ] [x2 ; x3]  ff2)
        in
        let new_variable = match f'2 with Forall(v,_) -> v | _ -> failwith "unreachable"
        in
        assert_equal (Forall(new_variable, Atomic_formula(Eq(V new_variable, x3)))) f'2 

let test_simultaneous_substitution_formula_exists_nominal test_ctxt =
        let ff1 = (Exists(v1, Atomic_formula f1)) 
        in
        let f'1= (simultaneous_substitution_formula [v1 ] [x2]  ff1)
        in
        let new_variable = match f'1 with Exists(v,_) -> v | _ -> failwith "unreachable"
        in
        assert_equal (Exists(new_variable, Atomic_formula(Eq(V new_variable, x2)))) f'1

let test_simultaneous_substitution_formula_exists_nominal_2 test_ctxt =
        let ff2 = (Exists(v1, Atomic_formula f1)) 
        in
        let f'2 = (simultaneous_substitution_formula [v1 ; v2 ] [x2 ; x3]  ff2)
        in
        let new_variable = match f'2 with Exists(v,_) -> v | _ -> failwith "unreachable"
        in
        assert_equal (Exists(new_variable, Atomic_formula(Eq(V new_variable, x3)))) f'2 

let test_free_variables_of_atomic_formula_eq test_ctxt =
        assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_atomic_formula (Eq(x1,x2)))

let test_free_variables_of_atomic_formula_relation test_ctxt =
        assert_equal (FormulaTest.SetVar.of_list [v1 ; v2 ; v3]) (free_variables_of_atomic_formula (Relation(SignatureMinimal.of_string "",[x1;x2;x2;x3])))

let test_free_variables_of_formula_atomic test_ctxt =
        assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_formula (Atomic_formula f1))

let test_free_variables_of_formula_neg test_ctxt =
        assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_formula (nf1))

let test_free_variables_of_formula_bin test_ctxt =
        assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (And (Atomic_formula f1, Atomic_formula f2))));
        assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (Or  (Atomic_formula f1, Atomic_formula f2))));
        assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (Imply (Atomic_formula f1, Atomic_formula f2))))

let test_free_variables_of_formula_quant test_ctxt =
        assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.singleton v2) (free_variables_of_formula g1));
        assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.singleton v2) (free_variables_of_formula g1))

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
        "test_simultaneous_substitution_formula_exists_nominal">::test_simultaneous_substitution_formula_exists_nominal;
        "test_simultaneous_substitution_formula_exists_nominal2">::test_simultaneous_substitution_formula_exists_nominal_2;
        "test_free_variables_of_atomic_formula_eq">::test_free_variables_of_atomic_formula_eq;
        "test_free_variables_of_atomic_formula_relation">::test_free_variables_of_atomic_formula_relation;
        "test_free_variables_of_formula_atomic">::test_free_variables_of_formula_atomic;
        "test_free_variables_of_formula_neg>">::test_free_variables_of_formula_neg;
        "test_free_variables_of_formula_bin">::test_free_variables_of_formula_bin;
        "test_free_variables_of_formula_quant">::test_free_variables_of_formula_quant;
        ]

let () = run_test_tt_main formula_suite
