open OUnit2
open First_order
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

let x1,x2,x3,x4 = TV v1, TV v2, TV v3, TV v4
let f1 = Eq(x1, x2)
let f2 = Eq(x3, x4)

let g1 = FForall(v1, FAtomic_formula(Eq(x1, x2)))
let g2 = FExists(v1, FAtomic_formula(Eq(x1, x2)))

let nf1 = FNeg (FAtomic_formula f1)
let nf2 = FNeg (FAtomic_formula f2)
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
let f_schema = FAtomic_formula(Relation(variable_schematique,[]))
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
    formula=FAtomic_formula(Relation(variable_non_schematique,[]));
  }
and schema_neg =
  {
    nom="schema neg";
    variables_reservees=[];
    groupe_variables_neutres=v0;
    variable_schematique=variable_schematique;
    variables_libres_utilisees_predicat=[];
    formula = FNeg f_schema;
  }
and schema_or =
  {
    nom="schema or";
    variables_reservees=[];
    groupe_variables_neutres=v0;
    variable_schematique=variable_schematique;
    variables_libres_utilisees_predicat=[];
    formula = FOr (FAtomic_formula f1, f_schema);
  }
and schema_and=
  {
    nom="schema and";
    variables_reservees=[];
    groupe_variables_neutres=v0;
    variable_schematique=variable_schematique;
    variables_libres_utilisees_predicat=[];
    formula = FAnd (f_schema, f_schema);
  }
and schema_imply =
  {
    nom="schema imply";
    variables_reservees=[];
    groupe_variables_neutres=v0;
    variable_schematique=variable_schematique;
    variables_libres_utilisees_predicat=[];
    formula = FImply (f_schema,  FAtomic_formula f1);
  }
;;

let printer =(fun s ->  (printer_first_order_formula Format.str_formatter s; let s = Format.flush_str_formatter () in s))

let test_apply_schemas test_ctxt = 
  assert_equal (nf1) (apply_schema ~schema:schema1 ~predicat:(nf1));
  assert_equal (FAtomic_formula f1) (apply_schema ~schema:schema1 ~predicat:(FAtomic_formula f1));
  assert_equal (FAtomic_formula (Relation(variable_non_schematique,[]))) (apply_schema ~schema:schema2 ~predicat:(FAtomic_formula f1));
  assert_equal ~printer:printer (FNeg (FAtomic_formula f1)) (apply_schema ~schema:schema_neg ~predicat:(FAtomic_formula f1));
  assert_equal ~printer:printer (FOr (FAtomic_formula f1, FAtomic_formula f2) ) (apply_schema ~schema:schema_or ~predicat:(FAtomic_formula f2));
  assert_equal ~printer:printer (FAnd (FAtomic_formula f2, FAtomic_formula f2) ) (apply_schema ~schema:schema_and ~predicat:(FAtomic_formula f2));
  assert_equal ~printer:printer (FImply (FAtomic_formula f2, FAtomic_formula f1) ) (apply_schema ~schema:schema_imply ~predicat:(FAtomic_formula f2))

(** Tests sur les schémas de théorie des ensembles **)
let a = Metavar "a"
let b = Metavar "b"
let c = Metavar "c"
let x = Metavar "x"
let y = Metavar "y"
let z = Metavar "z"
let of_string = Signature.Ens.of_string
let f = Signature.Ens.create_meta_symbol(of_string "f") 
let is_in = of_string "\\in"
let (&=) a b = FAtomic_formula(Relation(is_in,[a; b]))


let axiome_separation =
  let fx = FAtomic_formula(Relation(f,[TV x;TV c]))
  in
  {nom="Axiome de séparation";
   variables_reservees = [a;b];
   variable_schematique = f;
   groupe_variables_neutres = c;
   variables_libres_utilisees_predicat = [x];
   formula =  (FForall(a, FForall(c, FExists(b, FForall(x, equiv ((TV x) &= (TV b))
                                                      (FAnd ((TV x) &= (TV a), fx)))))))
  }

let axiome_remplacement =
  {nom = "Axiome de remplacement";
   variables_reservees = [a;b];
   variable_schematique = f;
   variables_libres_utilisees_predicat = [x;y];
   groupe_variables_neutres = c;
   formula = 
     let fxy,fxz=FAtomic_formula(Relation(f,[TV x;TV y;TV c])),FAtomic_formula(Relation(f,[TV x;TV z;TV c]))
     in
     FForall(a,FForall(c,((FForall(x,FForall(y,FForall(z,
                                                  FImply(FImply(FAnd(fxy, fxz), FAtomic_formula(Eq(TV y, TV z)))
                                                        ,
                                                        FExists(b,FForall(y,(
                                                            FImply(
                                                              FExists(x, FImply((TV x) &= (TV a) , fxy))
                                                              ,
                                                              ((TV y) &= (TV b)))))))
                                                 )))))))
  }

let test_dehornoy test_ctxt =
  let sepf1 = FForall(a, FExists(b, FForall(x, (equiv ((TV x) &= (TV b)) (FAnd((TV x) &= (TV a), (TV x) &= (TV x)) )))))
  and sepf2 = FForall(a, FForall(c, FExists(b, FForall(x, (equiv ((TV x) &= (TV b)) (FAnd((TV x) &= (TV a), FNeg ((TV x) &= (TV c))) ))))))
  and sepf3 = FForall(a, FExists(b, FForall(x, (equiv ((TV x) &= (TV b)) 
                                               (FAnd((TV x) &= (TV a), FExists(y, FImply ((TV y) &= (TV x), (TV x) &= (TV y)))))))))
  in
  assert_equal ~printer:printer sepf1 (apply_schema ~schema:axiome_separation ~predicat:((TV x) &= (TV x)));
  assert_equal ~printer:printer sepf2 (apply_schema ~schema:axiome_separation ~predicat:(FNeg ((TV x) &= (TV c))));
  assert_equal ~printer:printer sepf3 (apply_schema ~schema:axiome_separation ~predicat:
                                         (FExists(y, (FImply((TV y) &= (TV x), (TV x) &= (TV y)))))) 

let test_reserved_variables test_ctxt =
  try 
    ignore (apply_schema ~schema:axiome_separation ~predicat:(FAtomic_formula (Eq((TV a, TV b)))));
    assert_failure "Reserved variable non found" 
  with
  | Variable_reservee _ ->()

let test_suite = "Schemas test suite">:::[
    "Apply schema">::test_apply_schemas;      
    "Reserved variables">::test_reserved_variables;
    "Dehornoy separation axiom">::test_dehornoy;
  ]
let () = run_test_tt_main test_suite
let () =
  ignore (apply_schema ~schema:axiome_separation ~predicat:((TV x) &= (TV x)));
  ignore (apply_schema ~schema:axiome_separation ~predicat:(FNeg ((TV x) &= (TV c))));
  ignore (apply_schema ~schema:axiome_separation ~predicat: (FExists(y, (FImply((TV y) &= (TV x), (TV x) &= (TV y)))))) 
