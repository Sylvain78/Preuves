open Util
open Signature
open Theory


module ZF =
struct
  include Theory(Signature.Ens);;
  open Signature.Ens

  let of_string = Signature.Ens.of_string
  let (&=) a b = Atomic_formula(Relation(is_in,[a; b]))

  (** Ensemble empty *)
  let def_empty =
    let x = Var (new_var())
    and y = Var (new_var())
    in
    (Forall(y, Neg ((V y) &= (V x))))
  and printer_empty_ascii ff = Format.fprintf ff "Ø"
  and printer_empty_latex ff = Format.fprintf ff "\\empty"

  let empty = Constant (of_string "\\empty")


  (** Axiomes standards *)
  let a = Var (new_var())
  let b = Var (new_var())
  let c = Var (new_var())
  let x = Var (new_var())
  let y = Var (new_var())
  let z = Var (new_var())
  let f = Signature.Ens.create_meta_symbol(Signature.Ens.of_string "f") 

  let axiome_extensionnalite =
    let formula_axiome_extensionnalite =
      Forall(a, Forall(b, (Imply (Forall(x, equiv ((V x) &= (V a)) ((V x) &= (V b))) , 
      Atomic_formula (Eq (V a , V b))
      ))))
    in
    {nom_theoreme="Axiome d'extensionnalitÃ©"; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_extensionnalite}

  let axiome_paire =
    let formula_axiome_paire =
      Forall(a, Forall(b, Exists(c, 
      (And ((V a) &= (V c) , (V b) &= (V c)))
      )))
    in
    {nom_theoreme="Axiome de la paire" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_paire}

  let axiome_union =
    let formula_axiome_union =
      Forall (a, Exists (b, Forall (x, ( 
              Imply (Exists (y, And((V x) &= (V y) , (V y) &= (V a) )),
               ((V x) &= (V b)))
              ))))
    in
    {nom_theoreme="Axiome de l'union" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_union}

  let axiome_parties =
    let formula_axiome_parties =
      Forall(a, Exists(b, Forall(x, (
              Imply(
              Forall(y, ( Imply ((V y) &= (V x) , (V y) &= (V a))))
              , 
              ((V x) &= (V b))
              )
              ))))
    in
    {nom_theoreme="Axiome de l'ensemble des parties" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_parties}

  let axiome_separation =
    let fx = Atomic_formula(Relation(f,[V x;V c]))
    in
    {nom="Axiome de sÃ©paration";
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

  let axiome_fondation=
    let formula_axiome_fondation =
      Forall(a, Imply((Neg (Atomic_formula(Eq(V a, empty))) )  , Exists(b, (And(V b &= V a, (Atomic_formula(Eq(Operation(of_string "inter", [V b;V a]),  empty ))))))))
    in
    {nom_theoreme="Axiome de fondation"; parametres=[]; premisses=[]; preuve= []; conclusion=formula_axiome_fondation} 

  let successeur x = Operation(of_string "union",[x; Operation(of_string "singleton",[x])]);;


  let axiome_infini =
    let formula_axiome_infini =
      let a = Var (new_var())
      and x = Var (new_var())
      in
      Exists(a, And(Constant (of_string "Ø") &= (V a) , Forall(x, Imply((V x) &= (V a), ((successeur (V x)) &= (V a))))))
    in
    {nom_theoreme="Axiome de l'infini" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_infini}

  let (z_fini_dehornoy: theorie) =
    {
      axiomes = [axiome_extensionnalite; axiome_paire; axiome_union; axiome_parties];
      schemas = [axiome_separation];
      constantes = Hashtbl.create 0;
      operations = Hashtbl.create 0;
      relations = Hashtbl.create 0;
      theoremes = ref [];
    };;




  (** Définitions standards *)
  intro_symbol_constante z_fini_dehornoy def_empty (of_string "Ø") printer_empty_ascii printer_empty_latex;;

  (**)
  let rec x = Var (new_var()) and vx = V x
  and y = Var (new_var()) and vy = V y
  and z = Var (new_var()) and vz = V z
  and t = Var (new_var()) and vt = V t
  in
  let def_union = 
    Forall (z, equiv (vz &= vy) (Exists(t, And(vt &= vx, (vz &= vt)))))

  and printer_union_latex ff = function
    | Operation(op, [x]) when op = of_string "U"-> Format.fprintf ff "\\cup("; print_term ff x; Format.fprintf ff ")"
    | _ -> failwith "printer_union_latex appelé sur autre chose que l'opérateur unaire U"

  in
  intro_symbol_operation z_fini_dehornoy def_union y (of_string "U") 1 printer_union_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "U";;*)


  let rec x = Var (new_var()) and vx = V x
  and y = Var (new_var()) and vy = V y
  and z = Var (new_var()) and vz = V z
  and t = Var (new_var()) and vt = V t
  ;;
  let def_paire =
    Forall(z,
       equiv (vz &= vt)  (Or(Atomic_formula(Eq(vz, vx)), Atomic_formula(Eq(vz, vy)) ))) 

  and printer_paire_latex ff = function
    | Operation(op,[x;y]) when op = of_string "P" -> Format.fprintf ff "{"; print_term ff x; Format.fprintf ff ",";print_term ff y; Format.fprintf ff "}";
    | _ -> failwith "printer_paire_latex appelé sur autre chose que l'opérateur binaire P"

  in
  intro_symbol_operation z_fini_dehornoy def_paire t (of_string "P") 2 printer_paire_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "P";;*)

  let def_singleton =
    Forall(z,
       equiv (vz &= vt)  (Atomic_formula(Eq(vz, vx)))) 

  and printer_singleton_latex ff = function
    | Operation(op,[x]) when op = of_string "S" -> Format.fprintf ff "{"; print_term ff x; Format.fprintf ff "}";
    | _ -> failwith "printer_singleton_latex appelé sur autre chose que l'opérateur unaire S"

  in
  intro_symbol_operation z_fini_dehornoy def_singleton t (of_string "S") 1 printer_singleton_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "S";;*)

  let def_couple =
    let p,s = of_string "P",of_string "S"
    in
    (vz &=  Operation(p,[Operation(p,[vx;vy]);Operation(s,[vx])])) 

  and printer_couple_latex ff = function
    | Operation(op,[x;y]) when op = of_string "C" -> Format.fprintf ff "("; print_term ff x; Format.fprintf ff ",";print_term ff y; Format.fprintf ff ")";
    | _ -> failwith "printer_couple_latex appelé sur autre chose que l'opérateur binaire C"

  in
  intro_symbol_operation z_fini_dehornoy def_couple z (of_string "C") 2 printer_couple_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "C";;*)


  let x = Metavar("x")
  and y = Metavar("y")
  and t = Metavar("t")
  in
  let def_inclusion =
    Forall(t, Imply((V t) &= (V x), (V t) &= (V y)))

  and printer_incl_latex ff = function
    | Relation(rel,[x; y]) when rel = of_string "\\subset" -> Format.fprintf
                                                                ff "("; print_term ff x; Format.fprintf ff " \\subset "; print_term ff y; Format.fprintf ff ")";
    | _ -> failwith "printer_incl_latex appelé sur autre chose que l'opérateur binaire \\subset"

  in
  intro_symbol_relation z_fini_dehornoy def_inclusion (of_string "\\subset") 2 printer_incl_latex;;
  (*Hashtbl.find z_fini_dehornoy.relations_definies "\subset";;*)


  let (z_dehornoy : theorie) =
    let axiomes_z =
      z_fini_dehornoy.axiomes @ [axiome_infini]
    in
    {
      z_fini_dehornoy with axiomes = axiomes_z;
    }

  let (zf_point_dehornoy : theorie) =
    let schemas_zf_point =
      z_dehornoy.schemas @ [axiome_remplacement]
    in
    {
      z_dehornoy with schemas = schemas_zf_point;
    }

  let (zf_dehornoy : theorie) =
    let axiomes_zf_dehornoy =
      zf_point_dehornoy.axiomes@ [axiome_fondation]
    in
    {
      zf_point_dehornoy with axiomes = axiomes_zf_dehornoy;
    }

end
