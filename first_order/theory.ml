open Util
open Signature
open Formula
open Schemas
module Theory(Sig:SIGNATURE) =
struct
	
	include First_order_axioms.Axioms(Sig) 
		
        module S = Schema(Sig)	
        include S
        (**Création schéma*)
	(*Exemple pour séparation*)
	(* schema "separation" "f" ["x"] "c" ["a","b"] (?@)(a,(?@)("c",(?&)(b,(?@)(x,x&=b <=>(x&=a && f(x,c)))) ))*)
	
	type formula_parametre_schema = {
		nom_formula : Sig.symbole;
		variables : var list;
		alias_variables_muettes : var;
		}
		

        type theoreme = 
                {
                        nom_theoreme : string;
                        parametres : var list;
                        premisses : formula list;
                        preuve : preuve;
                        conclusion : formula;
                }
        
        and  term_preuve = | TPAxiome of formula * theoreme
                            | TPInstanceSchema of formula * (schema * formula)
                            | TPFormula of formula
                            | TPTheoreme of formula * (theoreme * (term list)(*parametres*) * (formula list)(* premisses*))

        and  preuve = term_preuve list 

        let term_preuve_vers_formula  = function
        | TPFormula f -> f
        | TPAxiome (f,_) -> f
        | TPInstanceSchema(f,_) -> f
        | TPTheoreme(f,_) -> f

	type theorie =
		{
			axiomes : theoreme list; (** Un axiome est un théorème sans prémisses *)
			schemas : schema list;
			constantes : (Sig.symbole,formula) Hashtbl.t;
			operations : (Sig.symbole,formula) Hashtbl.t;
			relations  : (Sig.symbole,(var list * formula)) Hashtbl.t;
                        theoremes : theoreme list ref
		}


        (** Les schémas de preuve seront vérifiés au moment de la vérification de cohérence, comme pour les théorèmes *)	
	let is_axiome_theorie th = function
        | TPAxiome (formula,axiome)  -> (List.mem axiome th.axiomes) & (formula = axiome.conclusion)
        | _ -> false
	
	let is_generalisation f p =
		match f with
		| Forall(v, g) -> List.exists (fun  tp_f -> term_preuve_vers_formula tp_f = g) p
		| _ -> false
	
	let coupure f p =
		List.exists (function  tp -> 
                        match term_preuve_vers_formula tp 
                        with
                        | Imply(g1, g2) -> g2 = f & List.mem g1 (List.map term_preuve_vers_formula p) | _ -> false) p
	
	let verification_preuve ~theorie ~hypotheses:hyp ~theoreme ~proof:(preuve:preuve) =
		(* f est bien à la fin de la preuve *)
		let is_fin_preuve f t =
			let rev_t = List.rev t
			in
			try
                          f = List.hd rev_t
			with
			| Failure _ -> false
		in
		
		if not(is_fin_preuve theoreme preuve)
		then failwith "la formula n'est pas à la fin de la preuve !!"
		else
			let rec verif t = function
				| [] -> true
				| (TPFormula f_i):: p -> (List.exists 
                                        (fun f -> 
                                                if (f_i = f)
                                                then 
                                                        begin 
                                                                print_string "HYP : "; printer_first_order_formula Format.std_formatter f;Format.print_newline();
                                                                true;
                                                        end
                                                else false)
                                        t
                                    or is_generalisation f_i p
				    or (coupure f_i p)
                                    or is_axiome_premier_ordre f_i) 
                                  & (verif t p)
                                | TPAxiome _ as th_ax :: p-> is_axiome_theorie theorie th_ax 
						        & (verif t p)
                                | TPInstanceSchema (f,(s,formula_schematique))  :: p ->  (f = apply_schema s formula_schematique) & (verif t p)
                                | TPTheoreme  (f , (theoreme, parametres, premisses)) :: preuve -> (f = theoreme.conclusion) & 
                                                                                              (verif t preuve) & 
                                                                                              (List.for_all (fun p -> let premisse = substitution_simultanee theoreme.parametres parametres p
                                                                                                                      in
                                                                                                                      List.mem premisse (List.map term_preuve_vers_formula preuve)
                                                                                                            ) 
                                                                                                            premisses)
                                
			in verif hyp (List.rev preuve)
(******************************************************************************)

        let apply_theoreme theoreme params =
               (substitution_simultanee theoreme.parametres params) theoreme.conclusion,
               List.map (fun tp -> substitution_simultanee theoreme.parametres params (term_preuve_vers_formula tp)) theoreme.preuve

(******************************************************************************)



	(** Introduction de nouvelles constantes *)
	let intro_symbole_constante th f symb printer_symb_ascii printer_symb_latex =
		let def =
			let vl = SetVar.elements (free_variables_of_formula f)
			in
			(* Contrôle *)
			let v =
				match vl with [Var v] -> v | _ -> failwith "Définition avec zéro ou plusieurs variables libres"
			in
			(?@)(Var v, (V(Var v) ^= Constant symb) <=> f)
		in
		Hashtbl.add th.constantes symb def; 
		Hashtbl.add printers_constants symb printer_symb_latex
	
	
	(** Introduction de nouvelles opérations *)
	let intro_symbole_operation th def_op var symb arite printer_op_latex =
		let def op =
			let vl = SetVar.elements (free_variables_of_formula def_op)
			in
			(* Contrôle *)
			if (not (List.mem var vl)) then failwith "La variable libre ne l'est pas ...";
			let l =
				match vl with
				| [] -> failwith "Définition d'une opération sans variables libres"
				| _ -> let l' = List.filter (fun v-> v <> var) vl in List.map (fun v -> V v) l'
			in
			if (List.length l <> arite) then failwith ("Arité incorrecte pour définition de l'opération "^(Sig.to_string symb));
			let def_operation = (?@)(var, (V(var) ^= Operation(symb, l)) <=> def_op)
			in
			List.fold_right ( let fct = function  (V t) -> (fun f -> ?@(t,f)) | _ -> (fun f -> f) in fct) l def_operation
		in
		Hashtbl.add th.operations symb (def def_op);
		Hashtbl.add printers_operations symb printer_op_latex
	
	(** Introduction de nouvelles relations *)
	let intro_symbole_relation th def_rel symb arite printer_rel_latex =
                let vl = SetVar.elements (free_variables_of_formula def_rel)
                in
		let def =
			(* Contrôle *)
			if (List.length vl <> arite) then failwith ("Arité incorrecte pour définition de la relation "^(Sig.to_string symb));
			
			List.fold_right (fun v f -> (?@)(v, f)) 
                                        vl 
                                        (Atomic_formula(Relation(symb, List.map (fun v -> V v) vl)) <=> def_rel)
		in
		Hashtbl.add th.relations symb (vl,def);
		Hashtbl.add printers_relations symb printer_rel_latex
		(*
		let formula_of_string s =
			Parser.start Lexer.token (Lexing.from_string s);
		*)
		
end
