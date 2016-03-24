type pformule =
	| PVar of int
	| PNeg of pformule
	| PAnd of pformule * pformule
	| POr of pformule * pformule
	| PImpl of pformule * pformule
;;

val (=>.) : pformule -> pformule -> pformule;;
val (&&.) : pformule -> pformule -> pformule;;
val (||.) : pformule -> pformule -> pformule;;
val neg  : pformule -> pformule;;

val printer_pformule : Format.formatter -> pformule -> unit
