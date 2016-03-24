(*open Prop_parser*)

type pformule =
	| PVar of int
	| PNeg of pformule
	| PAnd of pformule * pformule
	| POr of pformule * pformule
	| PImpl of pformule * pformule
;;

let (=>.) f g = PImpl(f, g);;
let (&&.) f g = PAnd(f, g);;
let (||.) f g = POr(f, g);;
let neg f = PNeg f;;

(**
Formateurs d'affichage
*)
let printer_pformule ff f =
	let rec print_bin seq op f g =
		printer_pformule_aux ff seq f;
		Format.fprintf ff "%s" (" "^op^" ");
		printer_pformule_aux ff seq g;
	and printer_pformule_aux ff seq =
		let	print_par f =
			Format.fprintf ff "(";
			f();
			Format.fprintf ff ")";
		in
		function
		| PVar i -> Format.fprintf ff "P%d" i
		| PNeg g -> Format.fprintf ff "¬"; printer_pformule_aux ff "neg" g;
		| PAnd(f, g) ->
				if (seq = "and" ||  seq ="init")
				then
					print_bin "and" "/\\" f g
				else
					print_par (fun () -> print_bin "and" "/\\" f g)
		| POr(f, g) ->
				if (seq = "or" || seq ="init")
				then
					print_bin "or" "\\/" f g
				else
					print_par (fun () -> print_bin "or" "\\/" f g)
		| PImpl(f, g) -> if (seq ="init")
				then
					print_bin "impl" "=>" f g
				else
					print_par (fun () -> print_bin "impl" "=>" f g);
	in
	printer_pformule_aux ff "init" f;;

