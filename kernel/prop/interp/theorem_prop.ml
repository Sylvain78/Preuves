open Kernel
open Formula_prop

type demonstration_prop = formula_prop list
type theorem_prop = (formula_prop, demonstration_prop) Logic.theorem_logic
