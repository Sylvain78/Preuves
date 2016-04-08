open Signature
open Formula

module Schema  (Sig:SIGNATURE) =
  struct
    module Schema_Formula = Formula(Sig)
    open Schema_Formula

    type schema = {
      nom : string;
      variables_reservees : var list;
      groupe_variables_neutres : var;
      variable_schematique : Sig.symbol;
      variables_libres_utilisees_predicat : var list;
      formula : formula;

    }
   
    exception Variable_reservee of var

    let apply_schema ~schema ~predicat =
      let verification_variables_reservees p =
        let vars_of_p = free_variables_of_formula p
        in
        List.iter (fun v -> if (SetVar.mem v vars_of_p) 
                            then raise (Variable_reservee v)) 
                  schema.variables_reservees
      in
      let rec apply_schema_formula schema_formula predicat =
        verification_variables_reservees predicat;    
      match schema_formula  with
        | Neg s -> Neg (apply_schema_formula s predicat)
        | Or(s,t) -> Or(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | And(s,t) -> And(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | Imply(s,t) -> Imply(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | Atomic_formula(Eq(_,_)) -> schema_formula
        (* Cas spéciaux *)
        | Atomic_formula(Relation(r,args)) ->
                        let args' = List.filter (fun v -> v <> (V schema.groupe_variables_neutres)) args
                        in
                        if (r = schema.variable_schematique)
                        then simultaneous_substitution_formula schema.variables_libres_utilisees_predicat args' predicat
                        else schema_formula
        | Exists(v,s) -> if (v = schema.groupe_variables_neutres) 
                         then 
                           let s' = apply_schema_formula s predicat
                           and variables_neutres =  
                                 List.filter (function v -> not (List.mem v schema.variables_libres_utilisees_predicat))
                                             (SetVar.elements (free_variables_of_formula predicat))
                           in
                           List.fold_right ( fun v f -> Exists(v,f)) variables_neutres s'      
                         else 
                           Exists(v,apply_schema_formula s predicat)       
        | Forall(v,s) -> if (v = schema.groupe_variables_neutres) 
                         then 
                           let s' = apply_schema_formula s predicat
                           and variables_neutres =  
                                 List.filter (function v -> not (List.mem v schema.variables_libres_utilisees_predicat))
                                             (SetVar.elements (free_variables_of_formula predicat))
                           in
                           List.fold_right ( fun v f -> Forall(v,f)) variables_neutres s'      
                         else 
                           Forall(v,apply_schema_formula s predicat)        
      in
      apply_schema_formula schema.formula predicat
   
    type quantif = 
    | Univ 
    | Exist
   
    let rec consomme_variables_neutres q ~liste_var_util:l p =
      match q,p with
         ( Univ, Forall(v,p') 
         | Exist, Exists(v,p')) when (not (List.mem v l)) ->
           consomme_variables_neutres q ~liste_var_util:l p'
        | _ -> p 
     
    exception Instance of (formula * formula)  
    exception Missing_var_groupe_var_neutres of formula
    exception Parametres_metapredicat of formula
    (* Les méta prédicats sont seulements appliqués à des variables ou des
     * constantes ; si besoin de les appliquer à des opérations, le faire de la
     * manière suivante :
       ... && exists z, z= f(x,y...) & metapredicat(x,y,z,...)
     *)

    (** @deprecated *)
    [@@ocaml.deprecated "Utiliser apply_schema"]
    let is_instance ~schema ~predicat =
      let rec candidat = ref None
      in
      let rec (find_metapredicat : formula -> formula -> unit)  = fun s p ->
          let update_candidat s args p =
            let normalize_args args =
              (*Supprime la variable groupe_variables_neutres qui doit
               * être présente en fin des arguments du schéma*)
              let rev_args = List.rev args
              in
              if (List.hd rev_args) <> V schema.groupe_variables_neutres
              then raise (Missing_var_groupe_var_neutres p);
              let args_pertinents_metapredicat = 
                List.map (function V v -> v | _ -> raise (Parametres_metapredicat p)) (List.rev (List.tl rev_args))
              in
              (* Couples variables paramètres (privés des doublons) du métaprédicat et
               * variables déclarées du métaprédicat *)
              let rec association_vars k v k_forbidden ~accu= 
                                match k,v with
                                  | [],[] -> []
                                  | [v1],[k1] -> [(v1,k1)] 
                                  | k::lk,v::lv -> 
                                      if (List.mem k lk) 
                                      then association_vars lk lv (k::k_forbidden) ~accu
                                      else if (List.mem k k_forbidden)
                                           then association_vars lk lv k_forbidden ~accu
                                           else association_vars lk lv k_forbidden ~accu:((k,v)::accu) 
                                  | _ -> raise (Instance (s,p))
              in
              List.split(association_vars args_pertinents_metapredicat 
                                          (List.map (fun v -> V v) schema.variables_libres_utilisees_predicat) 
                                          [] ~accu:[])
            in
            match !candidat with
              | None -> candidat := Some p
              | Some s -> 
                 let (lv,lt) = normalize_args args 
                 in
                 candidat := Some (simultaneous_substitution_formula lv lt s)
          in
          match s, p with
          | Atomic_formula (Eq(_,_)), Atomic_formula (Eq(_,_)) -> 
              if (s=p) 
              then ()
              else raise (Instance (s,p))
          | Atomic_formula(Relation(rs,args_s)), _ when rs = schema.variable_schematique ->
             (* Instanciation de la variable schématique*)        
                          update_candidat s args_s p;
          | Atomic_formula(Relation(rs,args_s)), Atomic_formula(Relation(rp,args_p)) when rs <> schema.variable_schematique ->
             if Pervasives.(||) (rs <> rp) (List.exists2 (<>)  args_s args_p)
             then raise  (Instance (s,p))
          | Neg s', Neg p' -> find_metapredicat s' p'
          | And (s1,s2), And(p1,p2) 
          | Or (s1,s2), Or(p1,p2) 
          | Imply (s1,s2), Imply(p1,p2) -> 
              find_metapredicat s1 p1; 
              find_metapredicat s2 p2
          | Forall(vs,s'), Forall(vp,p') ->
              if  (vs <> schema.groupe_variables_neutres) 
              then find_metapredicat s' (simultaneous_substitution_formula [vp] [V vs] p')
              else let p'' = consomme_variables_neutres Univ schema.variables_libres_utilisees_predicat p
                   in
                   find_metapredicat s' p''
          | Exists (vs,s'),Exists(vp,p') -> 
              if  (vs <> schema.groupe_variables_neutres) 
              then find_metapredicat s' (simultaneous_substitution_formula [vp] [V vs] p')
              else let p'' = consomme_variables_neutres Exist schema.variables_libres_utilisees_predicat p
                   in
                   find_metapredicat s' p''
          | _ -> raise (Instance(s,predicat))
      in
      let s = schema.formula
      in
      find_metapredicat s predicat; (*Mise à jour du candidat*)
      match !candidat with 
        | None -> true, None
        | Some c -> (((apply_schema ~schema ~predicat:c) = predicat),  Some c)
  end
