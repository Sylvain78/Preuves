open Util
open Signature
open Formule
open Schemas
module Theorie(Sig:SIGNATURE) =
struct
	
	include Axiomes_premier_ordre.Axiomes(Sig) 
		
        module S = Schema(Sig)	
        include S
        (**Création schéma*)
	(*Exemple pour séparation*)
	(* schema "separation" "f" ["x"] "c" ["a","b"] (?@)(a,(?@)("c",(?&)(b,(?@)(x,x&=b <=>(x&=a && f(x,c)))) ))*)
	
	type formule_parametre_schema = {
		nom_formule : Sig.symbole;
		variables : var list;
		alias_variables_muettes : var;
		}
		

        type theoreme = 
                {
                        nom_theoreme : string;
                        parametres : var list;
                        premisses : formule list;
                        preuve : preuve;
                        conclusion : formule;
                }
        
        and  terme_preuve = | TPAxiome of formule * theoreme
                            | TPInstanceSchema of formule * (schema * formule)
                            | TPFormule of formule
                            | TPTheoreme of formule * (theoreme * (terme list)(*parametres*) * (formule list)(* premisses*))

        and  preuve = terme_preuve list 

        let terme_preuve_vers_formule  = function
        | TPFormule f -> f
        | TPAxiome (f,_) -> f
        | TPInstanceSchema(f,_) -> f
        | TPTheoreme(f,_) -> f

	type theorie =
		{
			axiomes : theoreme list; (** Un axiome est un théorème sans prémisses *)
			schemas : schema list;
			constantes : (Sig.symbole,formule) Hashtbl.t;
			operations : (Sig.symbole,formule) Hashtbl.t;
			relations  : (Sig.symbole,(var list * formule)) Hashtbl.t;
                        theoremes : theoreme list ref
		}


        (** Les schémas de preuve seront vérifiés au moment de la vérification de cohérence, comme pour les théorèmes *)	
	let is_axiome_theorie th = function
        | TPAxiome (formule,axiome)  -> (List.mem axiome th.axiomes) & (formule = axiome.conclusion)
        | _ -> false
	
	let is_generalisation f p =
		match f with
		| Forall(v, g) -> List.exists (fun  tp_f -> terme_preuve_vers_formule tp_f = g) p
		| _ -> false
	
	let coupure f p =
		List.exists (function  tp -> 
                        match terme_preuve_vers_formule tp 
                        with
                        | Imply(g1, g2) -> g2 = f & List.mem g1 (List.map terme_preuve_vers_formule p) | _ -> false) p
	
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
		then failwith "la formule n'est pas à la fin de la preuve !!"
		else
			let rec verif t = function
				| [] -> true
				| (TPFormule f_i):: p -> (List.exists 
                                        (fun f -> 
                                                if (f_i = f)
                                                then 
                                                        begin 
                                                                print_string "HYP : "; printer_formule_premier_ordre Format.std_formatter f;Format.print_newline();
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
                                | TPInstanceSchema (f,(s,formule_schematique))  :: p ->  (f = apply_schema s formule_schematique) & (verif t p)
                                | TPTheoreme  (f , (theoreme, parametres, premisses)) :: preuve -> (f = theoreme.conclusion) & 
                                                                                              (verif t preuve) & 
                                                                                              (List.for_all (fun p -> let premisse = substitution_simultanee theoreme.parametres parametres p
                                                                                                                      in
                                                                                                                      List.mem premisse (List.map terme_preuve_vers_formule preuve)
                                                                                                            ) 
                                                                                                            premisses)
                                
			in verif hyp (List.rev preuve)
(******************************************************************************)

        let apply_theoreme theoreme params =
               (substitution_simultanee theoreme.parametres params) theoreme.conclusion,
               List.map (fun tp -> substitution_simultanee theoreme.parametres params (terme_preuve_vers_formule tp)) theoreme.preuve

(******************************************************************************)



	(** Introduction de nouvelles constantes *)
	let intro_symbole_constante th f symb printer_symb_ascii printer_symb_latex =
		let def =
			let vl = SetVar.elements (variables_libres_formule f)
			in
			(* Contrôle *)
			let v =
				match vl with [Var v] -> v | _ -> failwith "Définition avec zéro ou plusieurs variables libres"
			in
			(?@)(Var v, (V(Var v) ^= Constante symb) <=> f)
		in
		Hashtbl.add th.constantes symb def; 
		Hashtbl.add printers_constantes symb printer_symb_latex
	
	
	(** Introduction de nouvelles opérations *)
	let intro_symbole_operation th def_op var symb arite printer_op_latex =
		let def op =
			let vl = SetVar.elements (variables_libres_formule def_op)
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
                let vl = SetVar.elements (variables_libres_formule def_rel)
                in
		let def =
			(* Contrôle *)
			if (List.length vl <> arite) then failwith ("Arité incorrecte pour définition de la relation "^(Sig.to_string symb));
			
			List.fold_right (fun v f -> (?@)(v, f)) 
                                        vl 
                                        (Formule_atomique(Relation(symb, List.map (fun v -> V v) vl)) <=> def_rel)
		in
		Hashtbl.add th.relations symb (vl,def);
		Hashtbl.add printers_relations symb printer_rel_latex
		(*
		let formule_of_string s =
			Parser.start Lexer.token (Lexing.from_string s);
		*)
		
end
