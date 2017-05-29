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
let variable_schematique = SignatureMinimal.of_string "p"
and variable_non_schematique = SignatureMinimal.of_string "q"
let f_schema = Atomic_formula(Relation(variable_schematique,[]))
let schema1 = 
        {
        nom="schema 1";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula= f_schema;
        }
and schema2 = 
        {
        nom="schema 2";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula=Atomic_formula(Relation(variable_non_schematique,[]));
        }
and schema_neg =
        {
        nom="schema neg";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula = Neg f_schema;
        }
and schema_or =
        {
        nom="schema or";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula = Or (Atomic_formula f1, f_schema);
        }
and schema_and=
        {
        nom="schema and";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula = And (f_schema, f_schema);
        }
and schema_imply =
        {
        nom="schema imply";
        variables_reservees=[];
        groupe_variables_neutres=v0;
        variable_schematique=variable_schematique;
        variables_libres_utilisees_predicat=[];
        formula = Imply (f_schema,  Atomic_formula f1);
        }
;;

let printer =(fun s ->  (printer_first_order_formula Format.str_formatter s; let s = Format.flush_str_formatter () in s))

let test_apply_schemas test_ctxt = 
        assert_equal (nf1) (apply_schema ~schema:schema1 ~predicat:(nf1));
        assert_equal (Atomic_formula f1) (apply_schema ~schema:schema1 ~predicat:(Atomic_formula f1));
        assert_equal (Atomic_formula (Relation(variable_non_schematique,[]))) (apply_schema ~schema:schema2 ~predicat:(Atomic_formula f1));
        assert_equal ~printer:printer (Neg (Atomic_formula f1)) (apply_schema ~schema:schema_neg ~predicat:(Atomic_formula f1));
        assert_equal ~printer:printer (Or (Atomic_formula f1, Atomic_formula f2) ) (apply_schema ~schema:schema_or ~predicat:(Atomic_formula f2));
        assert_equal ~printer:printer (And (Atomic_formula f2, Atomic_formula f2) ) (apply_schema ~schema:schema_and ~predicat:(Atomic_formula f2));
        assert_equal ~printer:printer (Imply (Atomic_formula f2, Atomic_formula f1) ) (apply_schema ~schema:schema_imply ~predicat:(Atomic_formula f2))

(** Tests sur les schémas de théorie des ensembles **)
  let a = Var (new_var())
  let b = Var (new_var())
  let c = Var (new_var())
  let x = Var (new_var())
  let y = Var (new_var())
  let z = Var (new_var())
  let of_string = Signature.Ens.of_string
  let f = Signature.Ens.create_meta_symbol(of_string "f") 
  let is_in = of_string "\\in"
  let (&=) a b = Atomic_formula(Relation(is_in,[a; b]))


  let axiome_separation =
    let fx = Atomic_formula(Relation(f,[V x;V c]))
    in
    {nom="Axiome de séparation";
     variables_reservees = [a;b];
     variable_schematique = f;
     groupe_variables_neutres = c;
     variables_libres_utilisees_predicat = [x];
     formula =  (Forall(a, Forall(c, Exists(b, Forall(x, equiv ((V x) &= (V b))
                                         (And ((V x) &= (V a), fx)))))))
    }

  let axiome_remplacement =
    {nom = "Axiome de remplacement";
     variables_reservees = [a;b];
     variable_schematique = f;
     variables_libres_utilisees_predicat = [x;y];
     groupe_variables_neutres = c;
     formula = 
       let fxy,fxz=Atomic_formula(Relation(f,[V x;V y;V c])),Atomic_formula(Relation(f,[V x;V z;V c]))
       in
       Forall(a,Forall(c,((Forall(x,Forall(y,Forall(z,
                                Imply(Imply(And(fxy, fxz), Atomic_formula(Eq(V y, V z)))
                                ,
                                Exists(b,Forall(y,(
                                        Imply(
                                              Exists(x, Imply((V x) &= (V a) , fxy))
                                              ,
                                              ((V y) &= (V b)))))))
                                )))))))
    }

let test_reserved_variables test_ctxt =
        try 
            ignore (apply_schema ~schema:axiome_separation ~predicat:(Atomic_formula (Eq((V a, V b)))));
            assert_failure "Rserved variable non found" 
        with
        | Variable_reservee _ ->()

let test_suite = "Schemas test suite">:::[
        "Apply schema">::test_apply_schemas;      
        "Reserved variables">::test_reserved_variables;
        ]

let () = run_test_tt_main test_suite
