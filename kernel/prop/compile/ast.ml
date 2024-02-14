open Kernel_prop_interp.Formula_prop

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_k*)
  | Th of int * (formula_prop * formula_prop) list (*instantce of theorem i, with list of simulatenous substitution for params *)
  | Known of int (*formula already known by a theorem*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)
  | BeginHyp of int
  | HypDecl of formula_prop (*declaration of a hypothesis*)
  | HypUse of int (*use of a hypothesis*)
  | EndHyp

type kernel_compiled_proof =
  {
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }
