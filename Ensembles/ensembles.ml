open Util
open Signature
open Theory


module ZF =
struct
  include Theory(Signature.Ens);;
  open Signature.Ens

  let of_string = Signature.Ens.of_string
  let (&=) a b = FAtomic_formula(Relation(is_in,[a; b]))

  (** Ensemble empty *)
  let def_empty =
    let x = Var (new_var())
    and y = Var (new_var())
    in
    (FForall(y, FNeg ((TV y) &= (TV x))))
  and printer_empty_ascii ff = Format.fprintf ff "�"
  and printer_empty_latex ff = Format.fprintf ff "\\empty"

  let empty = TConstant (of_string "\\empty")


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
      FForall(a, FForall(b, (FImply (FForall(x, equiv ((TV x) &= (TV a)) ((TV x) &= (TV b))) , 
      FAtomic_formula (Eq (TV a , TV b))
      ))))
    in
    {nom_theoreme="Axiome d'extensionnalité"; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_extensionnalite}

  let axiome_paire =
    let formula_axiome_paire =
      FForall(a, FForall(b, FExists(c, 
      (FAnd ((TV a) &= (TV c) , (TV b) &= (TV c)))
      )))
    in
    {nom_theoreme="Axiome de la paire" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_paire}

  let axiome_union =
    let formula_axiome_union =
      FForall (a, FExists (b, FForall (x, ( 
              FImply (FExists (y, FAnd((TV x) &= (TV y) , (TV y) &= (TV a) )),
               ((TV x) &= (TV b)))
              ))))
    in
    {nom_theoreme="Axiome de l'union" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_union}

  let axiome_parties =
    let formula_axiome_parties =
      FForall(a, FExists(b, FForall(x, (
              FImply(
              FForall(y, ( FImply ((TV y) &= (TV x) , (TV y) &= (TV a))))
              , 
              ((TV x) &= (TV b))
              )
              ))))
    in
    {nom_theoreme="Axiome de l'ensemble des parties" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_parties}

  let axiome_separation =
    let fx = FAtomic_formula(Relation(f,[TV x;TV c]))
    in
    {nom="Axiome de s�paration";
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

  let axiome_fondation=
    let formula_axiome_fondation =
      FForall(a, FImply((FNeg (FAtomic_formula(Eq(TV a, empty))) )  , FExists(b, (FAnd(TV b &= TV a, (FAtomic_formula(Eq(TOperation(of_string "inter", [TV b;TV a]),  empty ))))))))
    in
    {nom_theoreme="Axiome de fondation"; parametres=[]; premisses=[]; preuve= []; conclusion=formula_axiome_fondation} 

  let successeur x = TOperation(of_string "union",[x; TOperation(of_string "singleton",[x])]);;


  let axiome_infini =
    let formula_axiome_infini =
      let a = Var (new_var())
      and x = Var (new_var())
      in
      FExists(a, FAnd(TConstant (of_string "�") &= (TV a) , FForall(x, FImply((TV x) &= (TV a), ((successeur (TV x)) &= (TV a))))))
    in
    {nom_theoreme="Axiome de l'infini" ; parametres=[] ; premisses=[] ; preuve=[] ; conclusion=formula_axiome_infini}

  let (z_fini_dehornoy: theory) =
    {
      axiomes = [axiome_extensionnalite; axiome_paire; axiome_union; axiome_parties];
      schemas = [axiome_separation];
      constantes = Hashtbl.create 0;
      operations = Hashtbl.create 0;
      relations = Hashtbl.create 0;
      theoremes = ref [];
    };;




  (** D�finitions standards *)
  intro_symbol_constante z_fini_dehornoy def_empty (of_string "�") printer_empty_ascii printer_empty_latex;;

  (**)
  let rec x = Var (new_var()) and vx = TV x
  and y = Var (new_var()) and vy = TV y
  and z = Var (new_var()) and vz = TV z
  and t = Var (new_var()) and vt = TV t
  in
  let def_union = 
    FForall (z, equiv (vz &= vy) (FExists(t, FAnd(vt &= vx, (vz &= vt)))))

  and printer_union_latex ff = function
    | TOperation(op, [x]) when op = of_string "U"-> Format.fprintf ff "\\cup("; print_term ff x; Format.fprintf ff ")"
    | _ -> failwith "printer_union_latex appel� sur autre chose que l'op�rateur unaire U"

  in
  intro_symbol_operation z_fini_dehornoy def_union y (of_string "U") 1 printer_union_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "U";;*)


  let rec x = Var (new_var()) and vx = TV x
  and y = Var (new_var()) and vy = TV y
  and z = Var (new_var()) and vz = TV z
  and t = Var (new_var()) and vt = TV t
  ;;
  let def_paire =
    FForall(z,
       equiv (vz &= vt)  (FOr(FAtomic_formula(Eq(vz, vx)), FAtomic_formula(Eq(vz, vy)) ))) 

  and printer_paire_latex ff = function
    | TOperation(op,[x;y]) when op = of_string "P" -> Format.fprintf ff "{"; print_term ff x; Format.fprintf ff ",";print_term ff y; Format.fprintf ff "}";
    | _ -> failwith "printer_paire_latex appel� sur autre chose que l'op�rateur binaire P"

  in
  intro_symbol_operation z_fini_dehornoy def_paire t (of_string "P") 2 printer_paire_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "P";;*)

  let def_singleton =
    FForall(z,
       equiv (vz &= vt)  (FAtomic_formula(Eq(vz, vx)))) 

  and printer_singleton_latex ff = function
    | TOperation(op,[x]) when op = of_string "S" -> Format.fprintf ff "{"; print_term ff x; Format.fprintf ff "}";
    | _ -> failwith "printer_singleton_latex appel� sur autre chose que l'op�rateur unaire S"

  in
  intro_symbol_operation z_fini_dehornoy def_singleton t (of_string "S") 1 printer_singleton_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "S";;*)

  let def_couple =
    let p,s = of_string "P",of_string "S"
    in
    (vz &=  TOperation(p,[TOperation(p,[vx;vy]);TOperation(s,[vx])])) 

  and printer_couple_latex ff = function
    | TOperation(op,[x;y]) when op = of_string "C" -> Format.fprintf ff "("; print_term ff x; Format.fprintf ff ",";print_term ff y; Format.fprintf ff ")";
    | _ -> failwith "printer_couple_latex appel� sur autre chose que l'op�rateur binaire C"

  in
  intro_symbol_operation z_fini_dehornoy def_couple z (of_string "C") 2 printer_couple_latex;;
  (*Hashtbl.find z_fini_dehornoy.operations_definies "C";;*)


  let x = Metavar("x")
  and y = Metavar("y")
  and t = Metavar("t")
  in
  let def_inclusion =
    FForall(t, FImply((TV t) &= (TV x), (TV t) &= (TV y)))

  and printer_incl_latex ff = function
    | Relation(rel,[x; y]) when rel = of_string "\\subset" -> Format.fprintf
                                                                ff "("; print_term ff x; Format.fprintf ff " \\subset "; print_term ff y; Format.fprintf ff ")";
    | _ -> failwith "printer_incl_latex appel� sur autre chose que l'op�rateur binaire \\subset"

  in
  intro_symbol_relation z_fini_dehornoy def_inclusion (of_string "\\subset") 2 printer_incl_latex;;
  (*Hashtbl.find z_fini_dehornoy.relations_definies "\subset";;*)


  let (z_dehornoy : theory) =
    let axiomes_z =
      z_fini_dehornoy.axiomes @ [axiome_infini]
    in
    {
      z_fini_dehornoy with axiomes = axiomes_z;
    }

  let (zf_point_dehornoy : theory) =
    let schemas_zf_point =
      z_dehornoy.schemas @ [axiome_remplacement]
    in
    {
      z_dehornoy with schemas = schemas_zf_point;
    }

  let (zf_dehornoy : theory) =
    let axiomes_zf_dehornoy =
      zf_point_dehornoy.axiomes@ [axiome_fondation]
    in
    {
      zf_point_dehornoy with axiomes = axiomes_zf_dehornoy;
    }

end
