open Signature 
open Util
open Formula_prop
open Axioms_prop
open Proof_prop

module Axioms (Sig:SIGNATURE)=
struct
	include Formula.Formula(Sig)
	
	exception Failed_Unification of formula * formula_prop
	
	
	(** f is an instance of a propositionnal axiom **)
	let is_instance_axiom_prop (f: formula) =
		(**  @param l list of variables of g already instanciated in f *)
		let rec instance_aux (l: (formula_prop * formula) list) f prop=
				match prop with
				| PVar i as g -> begin
							try
							(* Vi already bound to t *)
								let (v, t) = List.find (fun (v1, t1) -> v1 = g) l
								in
								(* we find the same bound again, ok *)
								if (t = f) then l
								else raise (Failed_Unification(f, g))
							with Not_found -> (*new bound*)(g, f)::l (*g=Vi is bound to f*)
						end
				| PNeg g1 as g -> begin
							match f with
							| Neg f1 -> instance_aux l f1 g1
							| _ -> raise (Failed_Unification(f, g))
						end
				| PAnd(g1, g2) as g -> begin
							match f with
							| And(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
							| _ -> raise (Failed_Unification(f, g))
						end
				| POr(g1, g2) as g -> begin
							match f with
							| Or(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
							| _ -> raise (Failed_Unification(f, g))
						end
				| PImpl(g1, g2) as g -> begin
							match f with
							| Imply(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
							| _ -> raise (Failed_Unification(f, g))
						end
			
		
		in
		List.exists (fun a ->
			let is_instance = 
				try (instance_aux [] f a.axiom_prop) <> []
				with Failed_Unification _ -> false 
			in
			if (is_instance)
			then
				begin
					print_string a.name_axiom_prop;
					print_string " : ";printer_first_order_formula Format.std_formatter f;Format.print_newline();
					true;
				end
			else
				false
			) axioms_prop
	
	(** Independance axiom on a quantified variable not free *)
	let is_independance_quantifier f =
		match f with (* v1 is not free in f1 *)
		| Imply((Forall(v1, Imply(f1, g1))), (Imply(f2, (Forall(v2, g2))))) -> 
			v1 = v2 & f1 = f2 & g1 = g2  
			& not (SetVar.mem v1 (free_variables_of_formula f1))
		| _ -> false
	(** Elimination axiom of the universal quantifier **)
	let is_forall_elim formula =
		match formula with
		| Imply(Forall(v, f), g) -> 
                        let rec find_term_instance_v f g= 
                         match f,g with 
                            | Atomic_formula(Eq(f1,f2)),Atomic_formula(Eq(g1,g2)) -> 
                                            if (f1 = V v) 
                                            then g1
                                            else if (f2 = V v) 
                                                 then g2
                                                 else raise Not_found
                            | Atomic_formula(Relation(rf,lf)), Atomic_formula(Relation(rg,lg)) ->
                             if (rf=rg) 
                             then List.assoc (V v) (List.combine lf lg)
                             else raise Not_found
                            | Neg f, Neg g  -> find_term_instance_v f g
                            | Or(f1,f2),Or(g1,g2)
                            | And(f1,f2),And(g1,g2)
                            | Imply(f1,f2),Imply(g1,g2) -> 
                                (try find_term_instance_v f1 g1
                                with Not_found -> find_term_instance_v f2 g2)
                            | Forall(v',f'),Forall(v'',f'') 
                            | Exists(v',f'),Exists(v'',f'') -> 
                                (* v lié,  on cherche une occurence libre*)
                                if (Pervasives.(||) (v' = v) (v'' = v))
                                then raise Not_found
                                else find_term_instance_v f' (simultaneous_substitution_formula [v''] [V v'] f'')
                            | _ -> raise Not_found
                        in
                        (try 
                          let t = find_term_instance_v f g
		  	  in
                          (* Vérification *)
                          let f' = simultaneous_substitution_formula [v] [t] f
			  in
			  f'=g & (term_free_for_var t v f)
                        with Not_found -> false)
		| _ -> false
	
	let is_equiv_exists_forall =
		function
		| And(Imply(Exists(v, Neg f), Neg Forall(v', g)),
		Imply(Neg (Forall(v'', g')), Exists(v''', Neg f'))) -> v = v' & v'= v'' & v''= v''' & f = g & f = f' & g = g'
		| _ -> false
	
	let is_equality_axiom f =
		let x1 = V(Var (1))
		and x2 = V(Var (2))
		and x3 = V(Var (3))
		in
		f = x1 ^= x1
		or f = ((Atomic_formula (Eq(x1, x2))) => (Atomic_formula (Eq(x2, x1))))
		or f = (((Atomic_formula (Eq(x1, x2))) &&& (Atomic_formula (Eq(x2, x3)))) => (Atomic_formula (Eq(x1, x3))))
	
	let verif_arite_et arite f =
		let rec verif_arite_et_aux i arite f =
			if i = arite
			then
				f = Atomic_formula(Eq(V(Var arite), V(Var (2 * arite))))
			else
				match f with
				| And ((Atomic_formula(Eq(V(Var i), V(Var j)))), g) -> j = arite + 1 & verif_arite_et_aux (i + 1) arite g
				| _ -> false
		in
		verif_arite_et_aux 1 arite f
	
	let is_equality_op_axiom = function
		| Imply(f, g) -> begin
					match g with
					| Atomic_formula (Eq(Operation(s,lt), Operation(s', lt'))) ->
							let arite = List.length lt 
							in
							s = s' & (List.length lt = List.length lt')
							& (let lvk = ref []
								in
								for i = arite downto 1 do lvk := (V(Var i))::!lvk done;
								lt = !lvk)
							& (let lvk' = ref []
								in
								for i = 2 * arite downto arite + 1 do lvk' := (V(Var i))::!lvk' done;
								lt' = !lvk')
							& verif_arite_et arite f
					| _ -> false
				end
		| _ -> false
	
	let is_equiv_rel_axiom = function
		| Imply(f, g) -> begin
					match g with
					| And (Imply(Atomic_formula (Relation(r, lt)), Atomic_formula (Relation(r', lt'))),
					Imply(Atomic_formula (Relation(r1, lt1)), Atomic_formula (Relation(r1', lt1')))) ->
							let arite,arite',arite1,arite1' =
								List.length lt, List.length lt', List.length lt1, List.length lt1'
							in
							r = r' & r'= r1 & r1 = r1'
							& arite = arite' & arite'= arite1 & arite1 = arite1'
							& (let lvk = ref []
								in
								for i = arite downto 1 do lvk := (V (Var i))::!lvk done;
								lt = !lvk)
							& (let lvk' = ref []
								in
								for i = 2 * arite downto arite + 1 do lvk' := (V(Var i))::!lvk' done;
								lt' = !lvk')
							& verif_arite_et arite f
					| _ -> false
				end
		| _ -> false
	
	let is_axiome_premier_ordre f =
		is_instance_axiom_prop f
		or
		is_independance_quantifier f
		or
		is_forall_elim f
		or
		is_equiv_exists_forall f
		or
		is_equality_axiom f
		or
		is_equality_op_axiom f
		or
		is_equiv_rel_axiom f
	
end
