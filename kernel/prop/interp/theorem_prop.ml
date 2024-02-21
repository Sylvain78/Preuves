open Kernel
open Formula_prop

type  demonstration_prop = Demonstration of (formula_prop list * step_prop) list [@@unboxed]
and  theorem_prop = Theorem of (formula_prop, demonstration_prop) Logic.theorem_logic [@@unboxed]
and  step_prop = 
  | Single of formula_prop
  | Call of
      {
        theorem : theorem_prop;
        params :  formula_prop list
      } 
