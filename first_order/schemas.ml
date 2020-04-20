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
        | FNeg s -> FNeg (apply_schema_formula s predicat)
        | FOr(s,t) -> FOr(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | FAnd(s,t) -> FAnd(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | FImply(s,t) -> FImply(apply_schema_formula s predicat, apply_schema_formula t predicat)
        | FAtomic_formula(Eq(_,_)) -> schema_formula
        (* Cas spéciaux *)
        | FAtomic_formula(Relation(r,args)) ->
                        let args' = List.filter (fun v -> v <> (TV schema.groupe_variables_neutres)) args
                        in
                        if (r = schema.variable_schematique)
                        then simultaneous_substitution_formula schema.variables_libres_utilisees_predicat args' predicat
                        else schema_formula
        | FExists(v,s) -> if (v = schema.groupe_variables_neutres) 
                         then 
                           let s' = apply_schema_formula s predicat
                           and variables_neutres =  
                                 List.filter (function v -> not (List.mem v schema.variables_libres_utilisees_predicat))
                                             (SetVar.elements (free_variables_of_formula predicat))
                           in
                           List.fold_right ( fun v f -> FExists(v,f)) variables_neutres s'      
                         else 
                           FExists(v, apply_schema_formula s predicat)       
        | FForall(v,s) -> if (v = schema.groupe_variables_neutres) 
                         then 
                           let s' = apply_schema_formula s predicat
                           and variables_neutres =  
                                 List.filter (function v -> not (List.mem v schema.variables_libres_utilisees_predicat))
                                             (SetVar.elements (free_variables_of_formula predicat))
                           in
                           List.fold_right ( fun v f -> FForall(v,f)) variables_neutres s'      
                         else 
                           FForall(v, apply_schema_formula s predicat)        
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
