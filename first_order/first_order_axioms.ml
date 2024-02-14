open Signature 
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Theory.Prop
open First_order_parser

module Axioms (Sig:SIGNATURE)=
struct
  module F =  Formula.Formula(Sig)
  open F
  include Parser(Sig)

  exception Failed_Unification of formula * formula_prop


  (** f is an instance of a propositionnal axiom **)
  let is_instance_axiom_prop (f: formula) =
    (*  l : list of variables of g already instanciated in f *)
    let rec instance_aux (l: (formula_prop * formula) list) f prop=
      match prop with
      | PVar i as g -> begin
          try
            (* Vi already bound to t *)
            let (_, t) = List.find (fun (v1, _) -> v1 = g) l
            in
            (* we find the same bound again, ok *)
            if (t = f) then l
            else raise (Failed_Unification(f, g))
          with Not_found -> (*new bound*)(g, f)::l (*g=Vi is bound to f*)
        end
      | PNeg g1 as g -> begin
          match f with
          | FNeg f1 -> instance_aux l f1 g1
          | _ -> raise (Failed_Unification(f, g))
        end
      | PAnd(g1, g2) as g -> begin
          match f with
          |FAnd(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
          | _ -> raise (Failed_Unification(f, g))
        end
      | POr(g1, g2) as g -> begin
          match f with
          | FOr(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
          | _ -> raise (Failed_Unification(f, g))
        end
      | PImpl(g1, g2) as g -> begin
          match f with
          | FImply(f1, f2) -> instance_aux (instance_aux l f2 g2) f1 g1
          | _ -> raise (Failed_Unification(f, g))
        end
    in
    List.exists (fun a ->
        let is_instance = 
          try (instance_aux [] f a.conclusion) <> []
          with Failed_Unification _ -> false 
        in
        if (is_instance)
        then
          begin
            print_string a.name;
            print_string " : ";printer_first_order_formula Format.std_formatter f;Format.print_newline();
            true;
          end
        else
          false
      ) !axioms

  (** Independance axiom on a quantified variable not free *)
  let is_independance_quantifier f =
    match f with (* v1 is not free in f1 *)
    | FImply((FForall(v1, FImply(f1, g1))), (FImply(f2, (FForall(v2, g2))))) -> 
      v1 = v2 && f1 = f2 && g1 = g2  
      && not (SetVar.mem v1 (free_variables_of_formula f1))
    | _ -> false
  
  (** Elimination axiom of the universal quantifier **)
  let is_forall_elim formula =
    match formula with
    | FImply(FForall(v, f), g) -> 
      let rec find_term_instance_v f g= 
        match f,g with 
        | FAtomic_formula(Eq(f1,f2)),FAtomic_formula(Eq(g1,g2)) -> 
          if (f1 = TV v) 
          then g1
          else if (f2 = TV v) 
          then g2
          else raise Not_found
        | FAtomic_formula(Relation(rf,lf)), FAtomic_formula(Relation(rg,lg)) ->
          if (rf=rg) 
          then List.assoc (TV v) (List.combine lf lg)
          else raise Not_found
        | FNeg f, FNeg g  -> find_term_instance_v f g
        | FOr(f1,f2), FOr(g1,g2)
        | FAnd(f1,f2), FAnd(g1,g2)
        | FImply(f1,f2), FImply(g1,g2) -> 
          (try find_term_instance_v f1 g1
           with Not_found -> find_term_instance_v f2 g2)
        | FForall(v',f'),FForall(v'',f'') 
        | FExists(v',f'),FExists(v'',f'') -> 
          (* v lié,  on cherche une occurence libre*)
          if (Stdlib.(||) (v' = v) (v'' = v))
          then raise Not_found
          else find_term_instance_v f' (simultaneous_substitution_formula [v''] [TV v'] f'')
        | _ -> raise Not_found
      in
      (try 
         let t = find_term_instance_v f g
         in
         (* Vérification *)
         let f' = simultaneous_substitution_formula [v] [t] f
         in
         f'=g && (term_free_for_var t v f)
       with Not_found -> false)
    | _ -> false

  let is_equiv_exists_forall =
    function
    |FAnd(FImply(FExists(v, FNeg f), FNeg FForall(v', g)),
          FImply(FNeg (FForall(v'', g')), FExists(v''', FNeg f'))) -> v = v' && v'= v'' && v''= v''' && f = g && f = f' && g = g'
    | _ -> false

  let is_equality_axiom f =
    f = formula_from_string "x_1 = x_1"
    || f = formula_from_string "(x_1 = x_2) \\implies (x_2 = x_1)" 
    || f = formula_from_string "((x_1 = x_2) \\land (x_2 = x_3)) \\implies (x_1 = x_3)"

  let verif_arite_et arite f =
    let rec verif_arite_et_aux i arite f =
      if i = arite
      then
        f = FAtomic_formula(Eq(TV(Var arite), TV(Var (2 * arite))))
      else
        match f with
        |FAnd ((FAtomic_formula(Eq(TV(Var i), TV(Var j)))), g) -> j = arite + 1 && verif_arite_et_aux (i + 1) arite g
        | _ -> false
    in
    verif_arite_et_aux 1 arite f

  let is_equality_op_axiom = function
    | FImply(f, g) -> begin
        match g with
        | FAtomic_formula (Eq(TOperation(s,lt), TOperation(s', lt'))) ->
          let arite = List.length lt 
          in
          s = s' && (List.length lt = List.length lt')
          && (let lvk = ref []
              in
              for i = arite downto 1 do lvk := (TV(Var i))::!lvk done;
              lt = !lvk)
          && (let lvk' = ref []
              in
              for i = 2 * arite downto arite + 1 do lvk' := (TV(Var i))::!lvk' done;
              lt' = !lvk')
          && verif_arite_et arite f
        | _ -> false
      end
    | _ -> false

  let is_equiv_rel_axiom = function
    | FImply(f, g) -> begin
        match g with
        |FAnd (FImply(FAtomic_formula (Relation(r, lt)), FAtomic_formula (Relation(r', lt'))),
               FImply(FAtomic_formula (Relation(r1, lt1)), FAtomic_formula (Relation(r1', lt1')))) ->
          let arite,arite',arite1,arite1' =
            List.length lt, List.length lt', List.length lt1, List.length lt1'
          in
          r = r' && r'= r1 && r1 = r1'
          && arite = arite' && arite'= arite1 && arite1 = arite1'
          && (let lvk = ref []
              in
              for i = arite downto 1 do lvk := (TV (Var i))::!lvk done;
              lt = !lvk)
          && (let lvk' = ref []
              in
              for i = 2 * arite downto arite + 1 do lvk' := (TV(Var i))::!lvk' done;
              lt' = !lvk')
          && verif_arite_et arite f
        | _ -> false
      end
    | _ -> false

  let is_axiome_premier_ordre f =
    is_instance_axiom_prop f
    ||
    is_independance_quantifier f
    ||
    is_forall_elim f
    ||
    is_equiv_exists_forall f
    ||
    is_equality_axiom f
    ||
    is_equality_op_axiom f
    ||
    is_equiv_rel_axiom f

end
