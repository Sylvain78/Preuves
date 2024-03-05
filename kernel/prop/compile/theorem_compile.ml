open Kernel
open Ast
open Kernel_prop_interp.Formula

type demonstration_compile = Demonstration of (kernel_proof_term  list * step_compile) list [@@unboxed]
and  theorem_compile = Theorem of (formula_prop, demonstration_compile) Logic.theorem_logic [@@unboxed]
and  step_compile = 
  | Single of formula_prop
  | Call of
      {
        theorem : theorem_compile;
        params :  formula_prop list
      } 
