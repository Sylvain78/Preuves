open OUnit2
open Base_term
open Formula
open Schemas
open Signature
open Util
(*
module FormulaTest = struct
        include Formula(SignatureMinimal)
        let r = SignatureMinimal.of_string "s"
        let () = SignatureMinimal.binary_relations := [r]
end
*)
module SchemaTest = struct
        include Schema(SignatureMinimal)
end

(*open FormulaTest*)
open SchemaTest


let v0 = Var (new_var ())

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
(*
type schema = {
        nom : string;
        variables_reservees : var list;
        groupe_variables_neutres : var;
        variable_schematique : Sig.symbol;
        variables_libres_utilisees_predicat : var list;
        formula : formula;
}
*)
let schema1 = 
        let variable_schematique = SignatureMinimal.of_string "p"
        in
        {
        nom="schema 1";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula=Atomic_formula(Relation(variable_schematique,[]));
        }

let test_apply_schemas test_ctxt = 
    assert_equal (Atomic_formula f1) (apply_schema ~schema:schema1 ~predicat:(Atomic_formula f1))


let test_suite = "Schemas test suite">:::[
        "Schema">::test_apply_schemas;      
        ]

let () = run_test_tt_main test_suite
