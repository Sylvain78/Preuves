open Kernel_prop_interp.Formula_prop

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_k*)
  | Th of int * (formula_prop * formula_prop) list (*instantce of theorem i, with list of simulatenous substitution for params *)
  | Known of int (*formula already known by a theorem*)
  | Hyp of int (*use of a hypothesis*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)

val printer_kernel_proof_term : Format.formatter -> kernel_proof_term -> unit

type kernel_proof = 
  { 
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }
val kernel_prop_compile_verif :
  ?axioms:Kernel_prop_interp.Theorem_prop.theorem_prop list ->
  ?theorems:Kernel_prop_interp.Theorem_prop.theorem_prop list ->
  ?hypotheses:Kernel_prop_interp.Formula_prop.formula_prop list ->
  formula:Kernel_prop_interp.Formula_prop.formula_prop ->
  proof:kernel_proof_term list ->
  unit ->
  (unit, string) result
