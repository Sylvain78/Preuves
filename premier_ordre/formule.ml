open Util
open Signature
open Terme



module Formule (Sig:SIGNATURE)(*: (FORMULE)*) =
struct
        include Terme(Sig)
        
	type formule_atomique =
		| Eq of terme * terme
		| Relation of Sig.symbole * terme list
	let (printers_relations : (Sig.symbole, Format.formatter -> formule_atomique -> unit) Hashtbl.t) = Hashtbl.create 3
	
	type formule =
		| Formule_atomique of formule_atomique
		| Neg of formule
		| And of formule * formule
		| Or of formule * formule
		| Imply  of formule * formule
		| Exists of var * formule 
		| Forall of var * formule 
	
	exception Echec_unification_formule_atomique of formule_atomique * formule_atomique
	
	(**	Ensemble des variables (libres) d'une formule atomique **)
	let rec portee_atomique = function
		| Eq(t1, t2) -> let libres1 = variables_terme t1
				and libres2 = variables_terme t2
				in
				SetVar.union libres1 libres2,
				[]
		| Relation(s, lt) -> let liste_libre = List.map (variables_terme) lt
				in
				List.fold_left SetVar.union SetVar.empty liste_libre,
				[]
	
	(** Remplace la liste des x par la liste des t dans une formule atomique **)
	let rec substitution_simultanee_formule_atomique lx lt = function
		| Eq (t1, t2) -> 
			let t'1,t'2 = substitution_simultanee_terme lx lt t1,  
				      substitution_simultanee_terme lx lt t2
			in
			Eq(t'1, t'2)
		
		| Relation(s,lt') -> 
			let lt'' = List.map (substitution_simultanee_terme lx lt) lt'
			in 
			Relation(s, lt'')
			
	(** Remplace x par t dans une formule  **)
	let rec substitution_simultanee lx lt = function
		| Formule_atomique f_atomique -> Formule_atomique (
                        substitution_simultanee_formule_atomique lx lt f_atomique ) 
		| Neg f -> Neg (substitution_simultanee lx lt f )
		| And (f1, f2) -> 
			let f'1,f'2 = substitution_simultanee lx lt f1,  
                                      substitution_simultanee lx lt f2
			in
			And(f'1, f'2)
		 | Or(f1,f2) -> 
			let f'1,f'2 = substitution_simultanee lx lt f1,  
				      substitution_simultanee lx lt f2
			in
			Or(f'1, f'2)
		 | Imply(f1,f2) -> 
			let f'1,f'2 = substitution_simultanee lx lt f1,  
				      substitution_simultanee lx lt f2
			in
			Imply(f'1, f'2)
		(*alpha-renommage de v si v capture une variable libre des termes substitués*)
		| Forall(v,f1) as f -> if (List.mem v lx) 
                                       then
                                       f
		                       else
                                        let vars_lt = 
                                          List.fold_right (fun t s -> SetVar.union (variables_terme t) s) lt SetVar.empty 
                                        in
                                        if (SetVar.mem v vars_lt) 
                                        then 
                                                let new_v = Var(new_var()) 
                                                in 
                                                let f1' = substitution_simultanee [v] [(V new_v)] f1
                                                in
                                                Forall (new_v,substitution_simultanee lx lt f1')
                                        else
                                                Forall (v,substitution_simultanee lx lt f1)  
		| Exists(v,f1) as f -> if (List.mem v lx) 
                                       then
                                       f
		                       else
                                        let vars_lt = 
                                          List.fold_right (fun t s -> SetVar.union (variables_terme t) s) lt SetVar.empty 
                                        in
                                        if (SetVar.mem v vars_lt) 
                                        then 
                                                let new_v = Var(new_var()) 
                                                in 
                                                let f1' = substitution_simultanee [v] [(V new_v)] f1
                                                in
                                                Exists (new_v,substitution_simultanee lx lt f1')
                                        else
                                                Exists (v,substitution_simultanee lx lt f1)  
					 
	(** Variables libres d'une formule atomique. Ce sont toutes les variables de la formule **)
	let variables_libres_formule_atomique = function
		| Eq(t1,t2) -> SetVar.union (variables_terme t1) (variables_terme t2)
		| Relation(_, lt) -> List.fold_left SetVar.union SetVar.empty (List.map variables_terme lt)

	(**s Variables libres et variables liées**)
	(** Une variable peut être libre et liée dans la même formule. **)


	(** Variables libres d'une formule. Une variable est considérée comme libre si au moins une occurence est libre. **)
	let rec variables_libres_formule = function
		| Formule_atomique f -> variables_libres_formule_atomique f
		| Neg f -> variables_libres_formule f
		| And(f1,f2) | Or(f1,f2) | Imply(f1,f2) -> SetVar.union (variables_libres_formule f1) (variables_libres_formule f2)
		| Forall(v,f) | Exists(v,f) -> SetVar.remove v (variables_libres_formule f) 
		
	(** Variables liées d'une formule. Une variable est considérée comme liée si au moins une occurence est liée. **)	
	let rec variables_liees_formule = function
		| Forall(v,f) | Exists(v,f) -> SetVar.add v (variables_liees_formule f)
		| Neg f -> variables_liees_formule f
		| And(f1,f2) | Or(f1,f2) | Imply(f1,f2) -> SetVar.union (variables_liees_formule f1) (variables_liees_formule f2)
  		| Formule_atomique f -> SetVar.empty (*aucune variable liée dans une formule atomique*)

	
	(** Les occurences des variables de t ne sont pas capturées lors d'une substitution à x dans f **)
	let rec terme_libre_pour_var t x = function
		| Neg f ->
			terme_libre_pour_var t x f
		| And(f,g) | Or(f,g) | Imply(f,g) -> 
			(terme_libre_pour_var t x f) && (terme_libre_pour_var t x g)
		| Forall(v,f) | Exists(v,f) -> not (SetVar.mem v (variables_terme t))
		| Formule_atomique f_atomique -> true

	(* Unification par algorithme de Robinson *)
	let unifieur_formule_atomique f g = 
		let rec unifier_aux : (formule_atomique * formule_atomique) list * substitution -> substitution = function
			| [],mu -> mu
			| [Eq(t1,t2),Eq(u1,u2)],mu ->
				(fun u->(unifier_liste_terme [(t1,u1);(t2,u2)]) (mu u) : substitution) 
			| [Relation(r1, lt1),Relation(r2, lt2)],mu ->
				if r1=r2 && (List.length lt1 = List.length lt2) then 
					(fun u -> unifier_liste_terme (List.combine lt1 lt2) (mu u))
				else
					failwith "Opérations non unifiables"
			| ((f,g) :: l),mu -> 
				let tau = unifier_aux ([(f,g)],mu)
				in
				unifier_aux (l,(fun u -> tau (mu u)))
		in
		unifier_aux ([(f,g)],(fun x->x))
		
	let application_unifieur_atomique unifieur = function
		| Eq(t1,t2) -> Eq (unifieur t1, unifieur t2)
		| Relation(r, args) -> Relation(r,List.map unifieur args)

	(** Pendant logique de unifieur_formule **)
        (*TODO : Fonction à supprimmer*)

	let rec application_unifieur unifieur = function
		| Formule_atomique(f) -> Formule_atomique(application_unifieur_atomique unifieur f) 
		| Neg f -> Neg (application_unifieur unifieur f)
		| And(f,g) -> And(application_unifieur unifieur f, application_unifieur unifieur g)  
		| Or(f,g) -> Or(application_unifieur unifieur f, application_unifieur unifieur g)
		| Imply(f,g) -> Imply(application_unifieur unifieur f, application_unifieur unifieur g)
		| Forall(v,f) -> Forall(v, application_unifieur (fun v' -> if v' = V v then V v else unifieur v') f) (*Pas de substitution sur une variable liée*)
		| Exists(v,f) -> Exists(v, application_unifieur (fun v' -> if v' = V v then V v else unifieur v') f) (*Pas de substitution sur une variable liée*)
		
	(** Opérateurs standards *)
	let (=>) f g = Imply(f, g)
	let (<=) f g = g => f
	let (&&) f g = And(f, g)
	let (||) f g = Or(f, g)
	let neg f = Neg f
	let (<=>) f g = And(Imply(f, g), Imply(g, f))
	let (?&) = function (v, f) -> Exists(v, f)
	let (?@) = function (v, f) -> Forall(v, f)
	let (^=) a b = Formule_atomique(Eq(a, b))
	let (^!=) a b = neg (Formule_atomique(Eq(a, b)))
	
	(** Formateurs d'affichage **)
	let rec printer_formule_atomique_premier_ordre ff = function
		| Eq (t1, t2) -> print_terme ff t1;
				Format.fprintf ff " = ";
				print_terme ff t2;
		| Relation(op, lt) ->
				let arite = List.length (lt)
				in
				match arite with
				| 2 -> print_terme ff (List.hd lt);
						Format.fprintf ff "%s" (" "^(Sig.to_string op)^" ");
						print_terme ff (List.hd (List.tl lt))
				| _ -> Format.fprintf ff "%s" ((Sig.to_string op)^"(");
						print_liste ff print_terme lt;
						Format.fprintf ff "%s" (")")
	
	let printer_formule_premier_ordre ff f =
		let rec print_bin seq op f g =
			Format.fprintf ff " ";
			printer_formule_premier_ordre_aux ff seq f;
			Format.fprintf ff "%s" (" "^op^" ");
			printer_formule_premier_ordre_aux ff seq g;
		and printer_formule_premier_ordre_aux ff seq =
			let	print_par f =
				Format.fprintf ff "(";
				f();
				Format.fprintf ff ")";
			in
			function
			| Neg g -> Format.fprintf ff "ï¿½"; printer_formule_premier_ordre_aux ff "neg" g;
			| And(f, g) -> begin
						match f, g with
						| Imply(h1, h2), Imply(h2', h1') ->
								if (h1 = h1' & h2 = h2')
								then print_bin "equiv" "<=>" h1 h2
								else begin
									if seq = "and" or seq ="init" or (seq ="forall") or (seq ="exists")
									then
										print_bin "and" "/\\" f g
									else
										print_par (fun () -> print_bin "and" "/\\" f g)
								end
						| _ ->
								if seq = "and" or seq ="init" or (seq ="forall") or (seq ="exists")
								then
									print_bin "and" "/\\" f g
								else
									print_par (fun () -> print_bin "and" "/\\" f g)
					end
			| Or(f, g) ->
					if seq = "or" or seq ="init" or (seq ="forall") or (seq ="exists")
					then
						print_bin "or" "\\/" f g
					else
						print_par (fun () -> print_bin "or" "\\/" f g)
			| Imply(f, g) -> if (seq ="init") or (seq ="forall") or (seq ="exists")
					then
						print_bin "impl" "=>" f g
					else
						print_par (fun () -> print_bin "impl" "=>" f g);
			| Forall(Var i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "forall X%d" i;
							printer_formule_premier_ordre_aux ff "forall" f;
						end
					else
					if (seq = "forall")
					then
						begin
							Format.fprintf ff ",X%d" i;
							printer_formule_premier_ordre_aux ff "forall" f;
						end
					else
						begin
							Format.fprintf ff "forall X%d" i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "forall" f);
						end
			| Forall(Metavar i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "forall %s" i;
							printer_formule_premier_ordre_aux ff "forall" f;
						end
					else
					if (seq = "forall")
					then
						begin
							Format.fprintf ff ",%s" i;
							printer_formule_premier_ordre_aux ff "forall" f;
						end
					else
						begin
							Format.fprintf ff "forall %s" i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "forall" f);
						end
			| Exists(Var i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "exists X%d" i;
							printer_formule_premier_ordre_aux ff "exists" f;
						end
					else
					if (seq = "exists")
					then
						begin
							Format.fprintf ff ",X%d " i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "exists" f);
						end
					else
						begin
							Format.fprintf ff " exists X%d " i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "exists" f);
						end
			| Exists(Metavar i, f) ->
					if (seq ="init")
					then
						begin
							Format.fprintf ff "exists %s" i;
							printer_formule_premier_ordre_aux ff "exists" f;
						end
					else
					if (seq = "exists")
					then
						begin
							Format.fprintf ff ",%s " i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "exists" f);
						end
					else
						begin
							Format.fprintf ff " exists %s " i;
							print_par (fun () -> printer_formule_premier_ordre_aux ff "exists" f);
						end
		    | Formule_atomique f -> printer_formule_atomique_premier_ordre ff f
		
		in
		printer_formule_premier_ordre_aux ff "init" f

end
