open Formula_prop

(** Remplace la liste des variable lx par la liste des terms lt **)		
let simultaneous_substitution_var lx lt v = 
  (try List.assoc v (List.combine lx lt)
   with | Not_found -> PVar v 
  )

(** Replace the list of x's by the list of terms t's  in a formula  **)
let rec simultaneous_substitution_formula_prop lx lt =
  function
  | PVar v -> simultaneous_substitution_var lx lt v
  | PNeg f -> PNeg (simultaneous_substitution_formula_prop lx lt f )
  | PAnd (f1, f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop lx lt f1,  
                  simultaneous_substitution_formula_prop lx lt f2
    in
    PAnd(f'1, f'2)
  | POr(f1,f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop lx lt f1,  
                  simultaneous_substitution_formula_prop lx lt f2
    in
    POr(f'1, f'2)
  | PImpl(f1,f2) -> 
    let f'1,f'2 = simultaneous_substitution_formula_prop lx lt f1,  
                  simultaneous_substitution_formula_prop lx lt f2
    in
    PImpl(f'1, f'2)
