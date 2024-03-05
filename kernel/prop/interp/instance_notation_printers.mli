open Formula

exception Failed_Unification of formula_prop * formula_prop

val instance : formula_prop -> formula_prop -> (formula_prop * formula_prop) list
val get_semantique : apply_notation_prop -> formula_prop
val expand_all_notations : formula_prop -> formula_prop
val printer_formula_prop : Format.formatter -> formula_prop -> unit
val to_string_formula_prop : formula_prop -> string
val pp_formula : formula_prop Fmt.t 
