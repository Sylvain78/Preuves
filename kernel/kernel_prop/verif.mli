open Prop__Formula_prop

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_j*)
  | Known of int (*formula already known in the theory*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)


type kernel_proof = 
  { 
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }
val kernel_verif :
  ?theory:Prop.Formula_prop.formula_prop list ->
  formula:Prop.Formula_prop.formula_prop ->
  proof:kernel_proof_term list ->
  unit ->
  (unit, string) result
