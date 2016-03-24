let new_var =
	let v = ref 0
	in
	function () ->
			begin
				incr v;
				if (!v <0) then failwith "plus de variables libres dispo";
				!v
			end;;
(**union de listes*)
(*TODO rendre tail recursive*)

	let rec union l1 l2 =
		match (l1, l2) with
			([], l2) -> l2
		| (x:: r1, l2) -> if List.mem x l2 then union r1 l2 else x:: (union r1 l2);;


(** Fusionne deux listes assiociatives avec unicité sur la  première variable*)
	
	let rec fusion_unifiers u = function
		| [] -> u
		| (t1, t2):: l -> try
					let t' = snd(List.find (fun (t, t') -> t = t1) u)
					in
					if t'= t2 then fusion_unifiers u l else failwith "echec unification"
				with Not_found -> fusion_unifiers ((t1, t2):: u) l

let rec print_liste ff f = function
	| [] -> ()
	| [a] -> f ff a
	| a:: l -> f ff a; Format.fprintf ff (", "); print_liste ff f l


(*
let rec set_of_list = function
	| [] -> empty
	| v::l -> add v (set_of_list l)
*)

let rec remove_heads l = function
	| 0 -> l
	| n -> match l with h::l' -> remove_heads l' (n-1)
											| [] -> failwith "Tentative de suppression d'éléments d'une liste vide" 


