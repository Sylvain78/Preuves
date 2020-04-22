type var_prop =
  | PVVar of int
  | PVMetaVar of string

type formula_prop =
  | PVar of var_prop
  | PNeg of formula_prop
  | PAnd of formula_prop * formula_prop
  | POr of formula_prop * formula_prop
  | PImpl of formula_prop * formula_prop
;;

val printer_formula_prop : Format.formatter -> formula_prop -> unit
val to_string_formula_prop : formula_prop -> string
