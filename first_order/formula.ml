open Util
open Signature
open Base_term


module Formula (Sig:SIGNATURE) =
struct
        include Term(Sig)
        
	type atomic_formula =
		| Eq of term * term
		| Relation of Sig.symbol * term list
	let (printers_relations : (Sig.symbol, Format.formatter -> atomic_formula -> unit) Hashtbl.t) = Hashtbl.create 3
	
	type formula =
		| Atomic_formula of atomic_formula
		| Neg of formula
		| And of formula * formula
		| Or of formula * formula
		| Imply  of formula * formula
		| Exists of var * formula 
		| Forall of var * formula 

        let equiv f g = And( Imply (f,g),
                             Imply (g,f)
                           )

	exception Failed_unification_atomic_formula of atomic_formula * atomic_formula
	
	(** Replace the list of x by the list of t in an atomic formula **) 
	let rec simultaneous_substitution_atomic_formula lx lt = function
		| Eq (t1, t2) -> 
			let t'1,t'2 = simultaneous_substitution_term lx lt t1,  
				      simultaneous_substitution_term lx lt t2
			in
			Eq(t'1, t'2)
		
		| Relation(s,lt') -> 
			let lt'' = List.map (simultaneous_substitution_term lx lt) lt'
			in 
			Relation(s, lt'')
			
	(** Replace the list of x's by the list of terms t's  in a formula  **)
	let rec simultaneous_substitution_formula lx lt = function
		| Atomic_formula f_atomic -> Atomic_formula (
                        simultaneous_substitution_atomic_formula lx lt f_atomic ) 
		| Neg f -> Neg (simultaneous_substitution_formula lx lt f )
		| And (f1, f2) -> 
			let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
                                      simultaneous_substitution_formula lx lt f2
			in
			And(f'1, f'2)
		 | Or(f1,f2) -> 
			let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
				      simultaneous_substitution_formula lx lt f2
			in
			Or(f'1, f'2)
		 | Imply(f1,f2) -> 
			let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
				      simultaneous_substitution_formula lx lt f2
			in
			Imply(f'1, f'2)
		(* alpha-renaming of v to enforce that v does not capture a free variable of the substituted terms
                 * TODO : find a better algorithm with only the necessary renamings. *)
		| Forall(v,f1) -> 
                                let new_v = Var(new_var()) 
                                in 
                                let f1' = simultaneous_substitution_formula [v] [(V new_v)] f1
                                in
                                Forall (new_v,simultaneous_substitution_formula lx lt f1')
		| Exists(v,f1) ->
                                let new_v = Var(new_var()) 
                                in 
                                let f1' = simultaneous_substitution_formula [v] [(V new_v)] f1
                                in
                                Exists (new_v,simultaneous_substitution_formula lx lt f1')
					 
	(** Free variables of an atomic formula. These are all the variables of the formula *)
	let free_variables_of_atomic_formula = function
		| Eq(t1,t2) -> SetVar.union (variables_term t1) (variables_term t2)
		| Relation(_, lt) -> List.fold_left SetVar.union SetVar.empty (List.map variables_term lt)

	(**s Free variables and bound variables **)
	(** A variable can be free and bound in the very same formula. **)


	(** Free variables of a formula. A variable is considered as free  if at least one of its occurence is free. **)
	let rec free_variables_of_formula = function
		| Atomic_formula f -> free_variables_of_atomic_formula f
		| Neg f -> free_variables_of_formula f
		| And(f1,f2) | Or(f1,f2) | Imply(f1,f2) -> SetVar.union (free_variables_of_formula f1) (free_variables_of_formula f2)
		| Forall(v,f) | Exists(v,f) -> SetVar.remove v (free_variables_of_formula f) 
		
	(** The occurences of variables in t are not captured during a substition at the variable x in f **)
	let rec term_free_for_var t x = function
		| Neg f ->
			term_free_for_var t x f
		| And(f,g) | Or(f,g) | Imply(f,g) -> 
			(term_free_for_var  t x f) && (term_free_for_var t x g)
		| Forall(v,f) | Exists(v,f) -> not (SetVar.mem v (variables_term t))
		| Atomic_formula f_atomic -> true

		
	
	(** Printing formatters **)
	let rec printer_first_order_atomic_formula ff = function
		| Eq (t1, t2) -> print_term ff t1;
				Format.fprintf ff " = ";
				print_term ff t2;
		| Relation(op, lt) ->
				let arite = List.length (lt)
				in
				match arite with
				| 2 -> print_term ff (List.hd lt);
						Format.fprintf ff "%s" (" "^(Sig.to_string op)^" ");
						print_term ff (List.hd (List.tl lt))
				| _ -> Format.fprintf ff "%s" ((Sig.to_string op)^"(");
						print_liste ff print_term lt;
						Format.fprintf ff "%s" (")")
	
	let printer_first_order_formula ff f =
		let rec print_bin seq op f g =
			printer_first_order_formula_aux ff seq f;
			Format.fprintf ff "%s" (" "^op^" ");
			printer_first_order_formula_aux ff seq g;
		and printer_first_order_formula_aux ff seq =
                        let print_par f =
				Format.fprintf ff "(";
				f();
				Format.fprintf ff ")";
			in
			function
                        | Neg g -> Format.fprintf ff "\\lnot "; print_par (fun () -> printer_first_order_formula_aux ff "neg" g);
			| And(f, g) -> begin
						match f, g with
						| Imply(h1, h2), Imply(h2', h1') ->
								if (h1 = h1' && h2 = h2')
								then print_bin "equiv" "<=>" h1 h2
								else begin
									if seq = "and" || seq ="init" || (seq ="forall") || (seq ="exists")
									then
										print_bin "and" "\\land" f g
									else
										print_par (fun () -> print_bin "and" "\\land" f g)
								end
						| _ ->
								if seq = "and" || seq ="init" || (seq ="forall") || (seq ="exists")
								then
									print_bin "and" "\\land" f g
								else
									print_par (fun () -> print_bin "and" "\\land" f g)
					end
			| Or(f, g) ->
					if seq = "or" || seq ="init" || (seq ="forall") || (seq ="exists")
					then
						print_bin "or" "\\lor" f g
					else
						print_par (fun () -> print_bin "or" "\\lor" f g)
			| Imply(f, g) -> if (seq ="init") || (seq ="forall") || (seq ="exists")
					then
						print_bin "impl" "=>" f g
					else
						print_par (fun () -> print_bin "impl" "=>" f g);
			| Forall(Var i, f) ->
					if (seq ="init")
					then
						begin
                                                        Format.fprintf ff "\\forall X_%d, " i;
							printer_first_order_formula_aux ff "forall" f;
						end
					else
					if (seq = "forall")
					then
						begin
                                                        Format.fprintf ff "X_%d, " i;
							printer_first_order_formula_aux ff "forall" f;
						end
					else
						begin
							print_par (fun () -> Format.fprintf ff "\\forall X_%d, " i;printer_first_order_formula_aux ff "forall" f);
						end
			| Forall(Metavar i, f) ->
					if (seq ="init")
					then
						begin
                                                        Format.fprintf ff "\\forall %s, " i;
							printer_first_order_formula_aux ff "forall" f;
						end
					else
					if (seq = "forall")
					then
						begin
                                                        Format.fprintf ff ",%s" i;
							printer_first_order_formula_aux ff "forall" f;
						end
					else
						begin
							print_par (fun () -> Format.fprintf ff "\\forall %s, " i;printer_first_order_formula_aux ff "forall" f);
						end
			| Exists(Var i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "\\exists X_%d, " i;
							printer_first_order_formula_aux ff "exists" f;
						end
					else
					if (seq = "exists")
					then
						begin
							Format.fprintf ff "X_%d, " i;
							printer_first_order_formula_aux ff "exists" f;
						end
					else
						begin
							print_par (fun () -> Format.fprintf ff "\\exists X_%d, " i;printer_first_order_formula_aux ff "exists" f);
						end
			| Exists(Metavar i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "\\exists %s, " i;
							printer_first_order_formula_aux ff "exists" f;
						end
					else
					if (seq = "exists")
					then
						begin
							Format.fprintf ff "%s, " i;
							printer_first_order_formula_aux ff "exists" f;
						end
					else
						begin
							print_par (fun () -> Format.fprintf ff "\\exists %s, " i;printer_first_order_formula_aux ff "exists" f);
						end
		    | Atomic_formula f -> printer_first_order_atomic_formula ff f
		
		in
		printer_first_order_formula_aux ff "init" f

end
