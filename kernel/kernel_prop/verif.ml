open Prop.Formula_prop
type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_j*)
  | Known of int (*formula already known in the theory*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)

type kernel_proof = 
  { 
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }

let kernel_verif ?(theory=[]) ~formula:f ~proof =
  (*verify formula is at the end of the proof*) 
  let rev_proof = List.rev proof
  in
  let formula_stack = ref []
  in
  let formula_from_proof_term = function
    | Known i -> List.nth theory i
    | Ax (i,subst) -> 
      let axiom = List.nth (!Prop.Axioms_prop.axioms_prop) i 
      in
      let  lv,lt = List.split subst
      in
      Prop.Substitution_prop.simultaneous_substitution_var (List.map (fun i -> PVar i) lv) lt axiom.kernel_conclusion_prop
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

