open Prop.Formula_prop
open Prop.Formula_tooling

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_j*)
  | Known of int (*formula already known in the theory*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)

type kernel_proof =
  {
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }

let kernel_verif ?(theory=[]) ~formula:f ~proof () =
  let formula_stack = ref []
  in
  let formula_from_proof_term theory = function
    | Known i -> List.nth theory (i-1)
    | Ax (i,subst) ->
      let axiom = List.nth (!Prop.Axioms_prop.axioms_prop) (i-1)
      in
      let  lv,lt = List.split subst
      in
      Prop.Substitution_prop.simultaneous_substitution_formula_prop (List.map (fun i -> PVar i) lv) lt axiom.kernel_conclusion_prop
    | Cut(j,k) -> 
      let rev_stack = List.rev !formula_stack
      in
      let fj,fk= List.nth rev_stack (j-1), List.nth rev_stack (k-1)
      in
      match fk with
      | PImpl(f,g) when f=fj -> g
      | _ -> failwith @@ "Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")"
  in
  List.iter
    (function proof_term ->
       formula_stack := (formula_from_proof_term theory proof_term)  :: !formula_stack
    )
    proof;
  (*verify formula is at the end of the proof*)
  if f = List.hd !formula_stack
  then
    Ok ()
  else
    Error ("Formula " ^ (to_string_formula_prop f) ^ "is not at the end of the proof.")
