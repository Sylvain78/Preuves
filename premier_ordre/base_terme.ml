open Signature

module type TERME = functor (Sig:SIGNATURE) -> 
	sig
		type var =
		| Var of int
		| Metavar of string
		
		module SetVar : (Set.S with type elt = var) 
		
		type terme
		val printers_constantes : (Sig.symbole, Format.formatter -> unit) Hashtbl.t
		val printers_operations : (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
		val printers_relations : (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
		val variables_terme : terme -> SetVar.t
		val substitution_simultanee_terme : var list -> terme list -> terme -> terme
		val print_terme : Format.formatter -> terme -> unit
	end

module Terme = functor (Sig:SIGNATURE) -> 
(struct
type var =
	| Var of int
	| Metavar of string (* TODO Vérifier si metavar toujours utiles *)
	
	type terme =
	| V of var
	| Constante of Sig.symbole
	| Operation of Sig.symbole * terme list
		
	let printers_constantes = Hashtbl.create 3;;
	let printers_operations = Hashtbl.create 3;;
	let printers_relations = Hashtbl.create 3;;
	(**Comparaison de variables, les variables précèdent les métavariables **)
	let compare_var v1 v2 =
		match v1,v2 with
			| Var i1, Var i2 -> (i2-i1)
			| Metavar v1, Metavar v2 -> String.compare v1 v2
			| Metavar _, Var _ -> 1
			| Var _, Metavar _ -> -1
		  	
	
	(** Ensemble de variables d'un terme **)
	module SetVar = Set.Make (struct type t = var let compare = compare_var end)
	
	
	(** Ensemble des variables d'un terme **)
	let rec variables_terme = function
		| V(Var _ as t) | V(Metavar _ as t) -> SetVar.singleton t
		| Constante _ -> SetVar.empty
		| Operation(_, lt) -> let liste_vars = List.map (variables_terme) lt
				in
				List.fold_left SetVar.union SetVar.empty liste_vars

		
	(** Remplace la liste des variable lx par la liste des termes lt **)		
	let rec substitution_simultanee_terme lx lt = function
		| Constante _ as c -> c
		| V x' as v -> 
		   (try List.assoc x' (List.combine lx lt)
                    with | Not_found -> v 
                   )
		| Operation(s,lt') -> 
                    let lt'' = List.map (substitution_simultanee_terme lx lt) lt'
		    in 
                    Operation(s,lt'')  
	
	(** Algorithme de Robinson **)
	type substitution = terme -> terme			
	
	let unifier_terme, unifier_liste_terme =
		let rec unifier_aux : (terme * terme) list * substitution -> substitution  = function
			| [ ],mu -> mu (* mu est la substitution *)
			| ((V var1 as x,u1)::lt),mu ->
				if (x = u1) then 
					unifier_aux (lt,mu)
				else
					if SetVar.mem var1 (variables_terme u1) then
						failwith "unification circulaire"
					else
						let mu1 = fun u -> substitution_simultanee_terme [var1] [u1] u
						in 
						let l1,l2 = List.split lt
						in
						let l1',l2' = List.map mu1 l1, List.map mu1 l2
						in
						unifier_aux ((List.combine l1' l2'),(fun u -> mu1 (mu u)))
			| ((u1, (V x1 as x))::lt),mu -> unifier_aux (((x,u1)::lt),mu)
			| (Constante c1, Constante c2)::lt,mu -> if c1 = c2 then
														mu
													 else 
														failwith "constantes non unifiables"
			| ((Operation(o1,l1)),(Operation(o2, l2)))::lt,mu -> 
				if (o1 = o2) && (List.length l1 = List.length l2) then
					unifier_aux ((List.combine l1 l2)@lt,mu)
				else
					failwith "operations non unifiables"
			| _ -> failwith "termes non unifiables"
		in 
			(fun t u -> unifier_aux ([(t,u)],(fun x -> x))),
			(fun l   -> unifier_aux       (l,(fun x -> x)))
		
		
	
	
	
	

	(** Formateurs d'affichage **)
	let rec print_terme ff = function
		| V(Var i) -> Format.fprintf ff "X%u" i
		| V(Metavar s) -> Format.fprintf ff "%s" s
		| Constante c -> (Hashtbl.find printers_constantes c) ff
		| Operation(op, _) as terme -> (Hashtbl.find printers_operations op) ff terme
end)

