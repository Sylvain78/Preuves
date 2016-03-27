type formula_prop =
	| PVar of int
	| PNeg of formula_prop
	| PAnd of formula_prop * formula_prop
	| POr of formula_prop * formula_prop
	| PImpl of formula_prop * formula_prop
;;

val (=>.) : formula_prop -> formula_prop -> formula_prop;;
val (&&.) : formula_prop -> formula_prop -> formula_prop;;
val (||.) : formula_prop -> formula_prop -> formula_prop;;
val neg  : formula_prop -> formula_prop;;

val printer_formula_prop : Format.formatter -> formula_prop -> unit
val to_string : formula_prop -> string
