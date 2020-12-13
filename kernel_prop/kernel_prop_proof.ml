open Prop.Formula_prop

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_j*)
  | Known of int (*formula already known in the theory*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)

type kernel_proof = kernel_proof_term list

(** Replace the list of variable lx by the list of termes lt **)
let simultaneous_substitution_var lx lt (v:formula_prop) = 
  (try List.assoc v (List.combine lx lt)
   with | Not_found -> v 
  )

(** Replace the list of x's by the list of terms t's  in a formula  **)
let rec simultaneous_substitution_formula_prop lx lt =
  function
  | (PVar _ | PMetaVar _) as f  -> simultaneous_substitution_var lx lt f
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
      (**TODO apply the substitution to the notation itself, and to its semantics*)
  | PApply_notation {
      apply_notation_prop = notation_prop;
      apply_notation_prop_params = params;
    }  -> PApply_notation {apply_notation_prop = notation_prop; 
                           apply_notation_prop_params = List.map (simultaneous_substitution_formula_prop lx lt) params;}


let kernel_verif f proof th =
  (*verify formula is at the end of the proof*) 
  let rev_proof = List.rev proof
  in
  let formula_stack = ref []
  in
  let formula_from_proof_term = function
    | Known i -> List.nth th i
    | Ax (i,subst) -> 
      let axiom = List.nth (!Prop.Axioms_prop.axioms_prop) i 
      in
      let  lv,lt = List.split subst
      in
      simultaneous_substitution_var (List.map (fun i -> PVar i) lv) lt axiom.kernel_conclusion_prop
    | Cut(j,k) ->   
      let fj,fk= List.nth !formula_stack j, List.nth !formula_stack k
      in
      match fk with
      | PImpl(f,g) -> 
        if (f=fj) 
        then
          g
        else
          failwith @@ "Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")"
      | _ -> 
          failwith @@ "Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")"
  in 
  List.iter 
    (function
      | (Ax _ | Known _) as pt -> 
        formula_stack := (formula_from_proof_term pt)  :: !formula_stack
      | Cut(j,k) ->   
        let fj,fk= List.nth !formula_stack j, List.nth !formula_stack k
        in
        match fk with
        | PImpl(f,g) -> 
          if (f=fj) 
          then
            formula_stack := g :: !formula_stack
          else
            failwith ("Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")")
        | _ ->
            failwith ("Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")")
    ) 
    rev_proof;
  if  f = List.hd !formula_stack
  then
    Ok ()
  else 
    Error ("Formula " ^ (to_string_formula_prop f) ^ "is not at the end of the proof.")

