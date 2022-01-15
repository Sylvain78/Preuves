open Prop__Formula_prop

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_j*)
  | Known of int (*formula already known by a theorem*)
  | Hyp of int (*use of a hypothesis*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)

val printer_kernel_proof_term : Format.formatter -> kernel_proof_term -> unit

type kernel_proof = 
  { 
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }
val kernel_verif :
  ?axioms:Prop.Theorem_prop.theorem_prop list ->
  ?theorems:Prop.Theorem_prop.theorem_prop list ->
  ?hypotheses:Prop.Formula_prop.formula_prop list ->
  formula:Prop.Formula_prop.formula_prop ->
  proof:kernel_proof_term list ->
  unit ->
  (unit, string) result
