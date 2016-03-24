open Axiomes_prop
open Formule_prop
(*
let (read_formule : string -> (pformule * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
	Prop_parser.formule lexbuf
*)
exception Echec_Unification of pformule * pformule

let instance f g =
	(**	@param l liste des PVariables de g déjà instanciées dans f *)
	let rec instance_aux l f =
		function
		| PVar i as g -> begin
					try
						let (v, t) = List.find (fun (v1, t1) -> v1 = g) l
						in
						if (t = f) then l
						else raise (Echec_Unification(f, g))
					with Not_found -> (g, f)::l (*g=Xi est lié à f*)
				end
		| PNeg g1 as g -> begin
					match f with
					| PNeg f1 -> instance_aux l f1 g1
					| _ -> raise (Echec_Unification(f, g))
				end
		| PAnd(g1, g2) as g -> begin
					match f with
					| PAnd(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Echec_Unification(f, g))
				end
		| POr(g1, g2) as g -> begin
					match f with
					| POr(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Echec_Unification(f, g))
				end
		| PImpl(g1, g2) as g -> begin
					match f with
					| PImpl(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Echec_Unification(f, g))
				end
	
	in
	try  
		(instance_aux [] f g) <> []
	with _ -> false

let coupure f p =
	List.exists (function | PImpl(g1, g2) -> g2 = f && List.mem g1 p | _ -> false) p

let theoremes_prop = ref []

exception Demonstration_invalide of pformule * pformule list

let rec verif t = function
        | [] -> true
        | f_i:: p ->
                if 
                (List.mem f_i t (*Formule déjà présente*)
                                (*instance d'un axiome ou d'un théorème*)
                        || (List.exists (fun a -> instance f_i a.axiome_prop) 
                                        (axiomes_prop @ !theoremes_prop)) 
                        || (coupure f_i p)) (*coupure*)
                then verif t p
                else raise (Demonstration_invalide (f_i,List.rev p))

let verification_preuve ~hyp:hypotheses f ~proof: preuve =
	(* f est bien à la fin de la preuve *)
	let is_fin_preuve f t =
		let rev_t = List.rev t
		in
		try
			f = List.hd rev_t
		with
		| Failure _ -> false
	in
	
	if not(is_fin_preuve f preuve)
	then failwith "la formule n'est pas à la fin de la preuve !!"
	else
		verif hypotheses (List.rev preuve)
;;

theoremes_prop := {nom_axiome_prop="C8 Bourbaki"; axiome_prop=(x1=>.x1);}::!theoremes_prop;;
theoremes_prop := {nom_axiome_prop="???"; axiome_prop=((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)));}::!theoremes_prop;;
theoremes_prop := {nom_axiome_prop="contraposée"; axiome_prop=(((neg x1)=>.(neg x2))=>.(x2=>.x1));}::!theoremes_prop;;
theoremes_prop := {nom_axiome_prop="S1 Bourbaki"; axiome_prop=((x1 ||.x1)=>.x1);}::!theoremes_prop;;
theoremes_prop := {nom_axiome_prop="tiers-exclus"; axiome_prop=(x1 ||. neg x1);}::!theoremes_prop;;

(*TODO Decomment when proved *)
(*let 
        a,b,c=x1,x2,x3
        in
        let a_entraine_c = (a=>.c)
        and b_entraine_c = (b=>.c) in
theoremes_prop := {nom_axiome_prop="???????"; axiome_prop=(a_entraine_c=>.(a=>.b_entraine_c));}::!theoremes_prop;;
*)	

