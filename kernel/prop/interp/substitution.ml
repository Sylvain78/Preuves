open Formula

(** Replace the list of variable lx by the list of termes lt **)
let simultaneous_substitution_var ~vars:lx ~terms:lt v = 
  (try List.assoc v (List.combine lx lt)
   with | Not_found -> v 
  )

(** Replace the list of x's by the list of terms t's  in a formula  **)
let rec simultaneous_substitution_formula_prop ~vars:lx ~terms:lt =
  function
  | (PVar _ | PMetaVar _) as f  -> simultaneous_substitution_var ~vars:lx ~terms:lt f
  | PNeg f -> PNeg (simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f )
  | PAnd (f1, f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f1,  
                  simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f2
    in
    PAnd(f'1, f'2)
  | POr(f1,f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f1,  
                  simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f2
    in
    POr(f'1, f'2)
  | PImpl(f1,f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f1,  
                  simultaneous_substitution_formula_prop ~vars:lx ~terms:lt f2
    in
    PImpl(f'1, f'2)
  | PApply_notation {
      apply_notation_prop = notation_prop;
      apply_notation_prop_params = params;
    }  -> PApply_notation {apply_notation_prop = notation_prop; 
                           apply_notation_prop_params = List.map (simultaneous_substitution_formula_prop ~vars:lx ~terms:lt) params;}

