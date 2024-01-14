open Kernel_prop_interp.Formula_prop

type step = 
  | Step of formula_prop 
  | Call of string * formula_prop list
