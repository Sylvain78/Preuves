open Axioms_prop
open Formula_prop
(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
	Prop_parser.formule lexbuf
*)
exception Failed_Unification of formula_prop * formula_prop

let instance f g =
	(**	@param l list of PVariables of g already instanciated in f *)
	let rec instance_aux l f =
		function
		| PVar i as g -> begin
					try
						let (v, t) = List.find (fun (v1, t1) -> v1 = g) l
						in
						if (t = f) then l
						else raise (Failed_Unification(f, g))
					with Not_found -> (g, f)::l (*g=Xi bound to f*)
				end
		| PNeg g1 as g -> begin
					match f with
					| PNeg f1 -> instance_aux l f1 g1
					| _ -> raise (Failed_Unification(f, g))
				end
		| PAnd(g1, g2) as g -> begin
					match f with
					| PAnd(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Failed_Unification(f, g))
				end
		| POr(g1, g2) as g -> begin
					match f with
					| POr(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Failed_Unification(f, g))
				end
		| PImpl(g1, g2) as g -> begin
					match f with
					| PImpl(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
					| _ -> raise (Failed_Unification(f, g))
				end
	
	in
	try  
		(instance_aux [] f g) <> []
	with _ -> false

let cut f p =
	List.exists (function | PImpl(g1, g2) -> g2 = f && List.mem g1 p | _ -> false) p

let theorems_prop = ref []

exception Invalid_demonstration of formula_prop * formula_prop list;;
Printexc.register_printer (function Invalid_demonstration(f,t) -> 
        Some("Invalid demonstration: " ^ (to_string f) ^ "\n[[\n" ^
                (List.fold_left  (fun acc f-> acc ^ (to_string f) ^ "\n") ""  t) ^ "\n]]\n") 
                                        | _ -> None)
;;
let rec verif t = function
        | [] -> true
        | f_i:: p ->
                if 
                (List.mem f_i t (*Formue already present *)
                                (*instance of an axiom or a theorem*)
                        || (List.exists (fun a -> instance f_i a.axiom_prop) 
                                        (axioms_prop @ !theorems_prop)) 
                        || (cut f_i p)) (*cut*)
                then verif t p
                else raise (Invalid_demonstration (f_i,List.rev p))

let proof_verification ~hyp:hypotheses f ~proof: proof =
	(* f is at the end of the proof *)
	let is_end_proof f t =
		let rev_t = List.rev t
		in
		try
			f = List.hd rev_t
		with
		| Failure _ -> false
	in
	
	if not(is_end_proof f proof)
	then failwith "Formula is not at the end of the proof"
	else
		verif hypotheses (List.rev proof)
;;

(* |- F=>F *)
proof_verification ~hyp:[] (x1=>.x1) 
~proof:[
	(x1 =>.((x1 =>. x1)=>.x1)) =>.
	(( x1 =>. (x1 =>. x1)) =>. (x1 =>. x1));
	x1=>.((x1=>.x1)=>.x1);
	(x1 =>. (x1 =>. x1)) =>. (x1 =>. x1);
	x1=>.(x1=>.x1);
	x1=>.x1
];;

theorems_prop := {name_axiom_prop="C8 Bourbaki"; axiom_prop=(x1=>.x1);}::!theorems_prop;;

(* |- (F=>.G)=>.(G=>.H)=>.(F=>.H)*)
proof_verification ~hyp:[] ((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))
~proof:[
	(x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3));
	((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3)))=>.((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))))=>.(((x2=>.x3)=>.(x1=>.(x2=>.x3)))=>.((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3))));
	(((x2=>.x3)=>.(x1=>.(x2=>.x3)))=>.((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>. (x1=>.(x2=>.x3)));
	((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3)));
	((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3)))=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)));
	(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)));
	(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)))=>.((x1=>.x2)=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3))));	
	((x1=>.x2)=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3))));
                        
	(*k*)
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)));
	
	(*s*)
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))) =>.
	(((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)))=>.((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3))));
	
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)))=>.((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)));
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))
];;
theorems_prop := {name_axiom_prop="???"; axiom_prop=((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)));}::!theorems_prop;;

(*non A =>. non B |- B =>. A*)
let h = ((neg (neg x2))=>.(neg (neg x1)))	
and a_ou_b =((neg (neg x1))=>. x1)
and i = ((neg (neg x2))=>. x1)	
and a2=	(x2=>.neg (neg x2))
in
proof_verification ~hyp:[] (((neg x1)=>.(neg x2))=>.(x2=>.x1))
~proof:[

a_ou_b;
a_ou_b=>.(h=>.a_ou_b);
h=>.a_ou_b;
h =>.(a_ou_b=>.i);
(h =>.(a_ou_b=>.i))=>.((h=>.a_ou_b)=>.(h=>.i));
((h=>.a_ou_b)=>.(h=>.i));
h=>.i;
a2;
a2=>.(h=>.a2);
h=>.a2;
a2=>.(i=>.(x2=>.x1));
(a2=>.(i=>.(x2=>.x1)))=>. (h=>.(a2=>.(i=>.(x2=>.x1))));
(h=>.(a2=>.(i=>.(x2=>.x1))));
(h=>.(a2=>.(i=>.(x2=>.x1)))) =>. ((h=>.a2)=>.(h=>.(i=>.(x2=>.x1))));
(h=>.a2)=>.(h=>.(i=>.(x2=>.x1)));
h=>.(i=>.(x2=>.x1));
(h=>.(i=>.(x2=>.x1)))=>.((h=>.i)=>.(h=>.(x2=>.x1)));
(h=>.i)=>.(h=>.(x2=>.x1));
h=>.(x2=>.x1);
(((neg x1)=>.(neg x2))=>. h);
(((neg x1)=>.(neg x2))=>. h)=>.((h=>.(x2=>.x1))=>.(((neg x1)=>.(neg x2))=>.(x2=>.x1)));
((h=>.(x2=>.x1))=>.(((neg x1)=>.(neg x2))=>.(x2=>.x1)));
(((neg x1)=>.(neg x2))=>.(x2=>.x1));
];;
theorems_prop := {name_axiom_prop="contraposition"; axiom_prop=(((neg x1)=>.(neg x2))=>.(x2=>.x1));}::!theorems_prop;;

(* |- F ou F =>. F *)
proof_verification ~hyp:[] ((x1 ||. x1)=>.x1)
~proof:[
((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1));
((neg x1)=>. ((x1 ||. x1) =>. x1));
((neg x1)=>. ((x1 ||. x1) =>. x1))=>.((((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1)))=>.((neg x1)=>.((neg x1) =>. neg (x1||.x1))));
((((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1)))=>.((neg x1)=>.((neg x1) =>. neg (x1||.x1))));
((neg x1)=>.((neg x1) =>. neg (x1||.x1)));
((neg x1)=>.((neg x1) =>. neg (x1||.x1)))=>. (((neg x1) =>. (neg x1))=>.((neg x1)=>.(neg (x1||.x1))));
((neg x1) =>. (neg x1));
(((neg x1) =>. (neg x1))=>.((neg x1)=>.(neg (x1||.x1))));
((neg x1)=>.(neg (x1||.x1)));
((neg x1)=>.(neg (x1||.x1)))=>. ((x1||.x1) =>.x1);
(x1||.x1) =>. x1;
];;
theorems_prop := {name_axiom_prop="[Bourbaki]S1"; axiom_prop=((x1 ||.x1)=>.x1);}::!theorems_prop;;

(*|- A ou neg A*)
let z = x1 ||. neg x1
and tout = neg (x1=>.x1)
in
proof_verification ~hyp:[] (z)
~proof:[

(x1=>.x1);(**)
(x1=>.x1) =>. (neg tout); (**)
neg tout;(*OK*)
 
(neg z)=>.(neg z);(*OK*)

x1=>.z;(**)
(x1=>.z)=>.((neg z) =>. (x1=>.z));(**)
(neg z)=>.(x1=>.(z));(*OK*)

((x1=>.z)=>.((neg z)=>.(neg x1))); (**)
((x1=>.z)=>.((neg z)=>.(neg x1))) =>. ((neg z)=>. ((x1=>.z)=>.((neg z)=>.(neg x1)))); (**)
(neg z)=>.((x1=>.z)=>.((neg z)=>.(neg x1))); (*OK*)

(x1=>.z)=>.((neg z) =>. neg x1);(**)
((neg z) =>. neg x1);(**)
((neg z) =>. neg x1)=>. ((neg z)=>.((neg z) =>. neg x1));(**)
(neg z)=>.((neg z)=>.(neg x1));(*OK*)

((neg z)=>.((neg z)=>.(neg x1)))=>.(((neg z)=>.(neg z))=>.((neg z)=>.(neg x1)));(**)
((neg z)=>.(neg z))=>.((neg z)=>.(neg x1));(**)
(neg z)=>.(neg x1);(*OK*)

(neg x1)=>. z;(**)
((neg x1)=>. z)=>. ((neg z)=>.((neg x1)=>. z));(**)
(neg z)=>.((neg x1)=>.(z));(*OK*)
((neg z)=>.((neg x1)=>.(z)))=>.(((neg z)=>. (neg x1))=>. ((neg z)=>. z));(**)
((neg z)=>. (neg x1))=>. ((neg z)=>. z);(**)
(neg z)=>.(z);(*OK*)

(neg z)=>.((neg tout)=>.(neg z));(*OK*)

((neg tout)=>.(neg z))=>.((z)=>.(tout));(**)
(((neg tout)=>.(neg z))=>.((z)=>.(tout)))=>.
((neg z)=>. (((neg tout)=>.(neg z))=>.((z)=>.(tout))));(**)

(neg z)=>.(((neg tout)=>.(neg z))=>.((z)=>.(tout)));(*OK*)
((neg z)=>.(((neg tout)=>.(neg z))=>.((z)=>.(tout))))=>.
(((neg z)=>.((neg tout)=>.(neg z)))=>.((neg z)=>.(z=>.tout)));(**)
(((neg z)=>.((neg tout)=>.(neg z)))=>.((neg z)=>.(z=>.tout)));(**)
(neg z)=>.((z)=>.(tout));(*OK*)
((neg z)=>.((z)=>.(tout)))=>.
(((neg z)=>.z) =>. ((neg z) =>. tout));(**)
(((neg z)=>.z) =>. ((neg z) =>. tout));(**)
(neg z)=>.(tout);(*OK*)
((neg z)=>.(tout))=>.((neg tout)=>.(neg(neg z)));(*OK*)
(neg tout)=>.(neg(neg z));(*OK*)
(neg(neg z))=>.(z);(*OK*)
neg(neg z);(*OK*)
z
];;
theorems_prop := {name_axiom_prop="Excluded middle"; axiom_prop=(x1 ||. neg x1);}::!theorems_prop;;

