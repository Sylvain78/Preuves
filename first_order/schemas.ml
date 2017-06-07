open Signature
open Formula

module Schema  (Sig:SIGNATURE) =
  struct
    module Schema_Formula = Formula(Sig)
    include Schema_Formula

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
                           Exists(v, apply_schema_formula s predicat)       
        | Forall(v,s) -> if (v = schema.groupe_variables_neutres) 
                         then 
                           let s' = apply_schema_formula s predicat
                           and variables_neutres =  
                                 List.filter (function v -> not (List.mem v schema.variables_libres_utilisees_predicat))
                                             (SetVar.elements (free_variables_of_formula predicat))
                           in
                           List.fold_right ( fun v f -> Forall(v,f)) variables_neutres s'      
                         else 
                           Forall(v, apply_schema_formula s predicat)        
      in
      apply_schema_formula schema.formula predicat
   
   
     
    exception Instance of (formula * formula)  
    exception Missing_var_groupe_var_neutres of formula
    exception Parametres_metapredicat of formula
    (* Les méta prédicats sont seulements appliqués à des variables ou des
     * constantes ; si besoin de les appliquer à des opérations, le faire de la
     * manière suivante :
       ... && exists z, z= f(x,y...) & metapredicat(x,y,z,...)
     *)

end
