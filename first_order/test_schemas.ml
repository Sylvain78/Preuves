open Util
open Schemas
open Formule
open Signature

module S = Schema(SignatureMinimale);;
module F = Formule(SignatureMinimale);;
open S
open F

let c,f = Var (new_var()),
          SignatureMinimale.create_meta_symbole (SignatureMinimale.of_string "f") 

let x = Var (new_var())

let s = {
        nom = "f(x,c)";
        variables_reservees = [];
        groupe_variables_neutres = c;
        variable_schematique = f;
        variables_libres_utilisees_predicat = [x];
        formule = Formule_atomique(Relation(f,[V x;V c]))
}


let f1 = Formule_atomique(Eq(V x,V x))
let f1' = apply_schema ~schema:s ~predicat:f1
let y = Var (new_var())
let f2 = Formule_atomique(Eq(V y,V y))
let f2' = apply_schema ~schema:s ~predicat:f2
let test1 () = 
        assert (f1 = f1');
        assert (is_instance ~schema:s ~predicat:f1 = (true,Some f1));
        assert (f2 = f2');
        assert (is_instance ~schema:s ~predicat:f2 = (true,Some f2))
;;

let s' = {
        nom = "f(x,c) && f(y,c)";
        variables_reservees = [];
        groupe_variables_neutres = c;
        variable_schematique = f;
        variables_libres_utilisees_predicat = [x];
        formule = (Formule_atomique(Relation(f,[V x;V c]))) && (Formule_atomique(Relation(f,[V y;V c])))  
}

let f1'' = apply_schema ~schema:s' ~predicat:f1

let formule_erronee = ref None
let test2() = 
        assert (f1'' = (f1 && f2));
        try assert(is_instance ~schema:s' ~predicat:f1''=(true, Some f1))
        with Missing_var_groupe_var_neutres f -> formule_erronee := Some f
;;

let z = Var (new_var())

let f3 = (Formule_atomique(Eq(V z, V z)))

let test3 () =
        assert (is_instance ~schema:s ~predicat:(f1 && f3) = (true,Some (f1 && f3)));
        assert (is_instance ~schema:s' ~predicat:(f1 && f3) = (false,Some f1))
;;

let f4 = (f1 && f3) && (f2 && f3)
let test4() =
	assert(is_instance ~schema:s' ~predicat:f4 = (true,Some (f1 && f3)));
;;

(*Tests sur la variable de groupe des variables neutres*)

let s5 = {
        nom = "forall c, f(x,c)";
        variables_reservees = [];
        groupe_variables_neutres = c;
        variable_schematique = f;
        variables_libres_utilisees_predicat = [x];
        formule = (?@) (c, Formule_atomique(Relation(f,[V x;V c])))   
}


let test5 () =
        assert(is_instance ~schema:s5 ~predicat:(F.(?@) (x,f1)) = (true,Some (F.(?@) (x,f1))));
        assert(is_instance ~schema:s5 ~predicat:(F.(?@) (z,f1 && f3)) = (true, Some (f1 && f3)))
;;
let _ =
test1();
test2();
test3();
test4();
test5();
;;
