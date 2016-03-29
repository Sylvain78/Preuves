let new_var =
	let v = ref 0
	in
	function () ->
			begin
				incr v;
				if (!v <0) then failwith "plus de variables libres dispo";
				!v
			end;;


let rec print_liste ff f = function
	| [] -> ()
	| [a] -> f ff a
	| a:: l -> f ff a; Format.fprintf ff (", "); print_liste ff f l

