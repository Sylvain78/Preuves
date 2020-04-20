open Util
open Signature
open Base_term


module Formula (Sig:SIGNATURE) =
struct
  module Bt=Term(Sig)
  include  Bt
  type atomic_formula =
    | Eq of term * term
    | Relation of Sig.symbol * term list
  let (printers_relations : (Sig.symbol, Format.formatter -> atomic_formula -> unit) Hashtbl.t) = Hashtbl.create 3

  type formula =
    | FAtomic_formula of atomic_formula
    | FNeg of formula
    | FAnd of formula * formula
    | FOr of formula * formula
    | FImply  of formula * formula
    | FExists of var * formula 
    | FForall of var * formula 

  let equiv f g = FAnd( FImply (f,g),
                        FImply (g,f)
                      )

  exception Failed_unification_atomic_formula of atomic_formula * atomic_formula
  (** Free variables of an atomic formula. These are all the variables of the formula *)
  let free_variables_of_atomic_formula = function
    | Eq(t1,t2) -> SetVar.union (variables_term t1) (variables_term t2)
    | Relation(_, lt) -> List.fold_left SetVar.union SetVar.empty (List.map variables_term lt)

  (**s Free variables and bound variables **)
  (** A variable can be free and bound in the very same formula. **)


  (** Free variables of a formula. A variable is considered as free  if at least one of its occurence is free. **)
  let rec free_variables_of_formula = function
    | FAtomic_formula f -> free_variables_of_atomic_formula f
    | FNeg f -> free_variables_of_formula f
    | FAnd(f1,f2) | FOr(f1,f2) | FImply(f1,f2) -> SetVar.union (free_variables_of_formula f1) (free_variables_of_formula f2)
    | FForall(v,f) | FExists(v,f) -> SetVar.remove v (free_variables_of_formula f) 

  (** Replace the list of x by the list of t in an atomic formula **) 
  let simultaneous_substitution_atomic_formula lx lt = function
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
  let rec simultaneous_substitution_formula lx lt =
    function
    | FAtomic_formula f_atomic -> FAtomic_formula (
        simultaneous_substitution_atomic_formula lx lt f_atomic ) 
    | FNeg f -> FNeg (simultaneous_substitution_formula lx lt f )
    | FAnd (f1, f2) -> 
      let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
                    simultaneous_substitution_formula lx lt f2
      in
      FAnd(f'1, f'2)
    | FOr(f1,f2) -> 
      let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
                    simultaneous_substitution_formula lx lt f2
      in
      FOr(f'1, f'2)
    | FImply(f1,f2) -> 
      let f'1,f'2 = simultaneous_substitution_formula lx lt f1,  
                    simultaneous_substitution_formula lx lt f2
      in
      FImply(f'1, f'2)
    (* alpha-renaming of v to enforce that v does not capture a free variable of the substituted terms *)
    | FForall(v,f1) ->
      (*v captured in the lx*)
      if List.mem v lx 
      then  
        let (lx',lt') = List.split(List.remove_assoc v (List.combine lx lt))
        in
        FForall(v, simultaneous_substitution_formula lx' lt' f1)
      else (*if lt from (free_vars of f1 intersect lx ) contains v as a free variable then v will be captured, so renaming*)
        let free_vars_of_f1_intersect_lx = SetVar.inter (free_variables_of_formula f1) (SetVar.of_list lx)
        and lx_to_lt = List.combine lx lt
        in
        let lt_concerned =  List.map (fun v -> List.assoc v lx_to_lt) (SetVar.elements free_vars_of_f1_intersect_lx)
        in
        if 
          List.exists (fun sv -> SetVar.mem v sv)  (List.map variables_term lt_concerned)
        then
          let  new_v = Var(new_var())
          in
          FForall(new_v, simultaneous_substitution_formula lx lt (simultaneous_substitution_formula [v] [(TV new_v)] f1))
        else (*it is safe to do forall(v, simultaneous_substitution_formula lx lt f1*)
          FForall(v, simultaneous_substitution_formula lx lt f1)
    (* alpha-renaming of v to enforce that v does not capture a free variable of the substituted terms *)
    | FExists(v,f1) ->
      (*v captured in the lx*)
      if List.mem v lx 
      then  
        let (lx',lt') = List.split(List.remove_assoc v (List.combine lx lt))
        in
        FExists(v, simultaneous_substitution_formula lx' lt' f1)
      else (*if lt from (free_vars of f1 intersect lx ) contains v as a free variable then v will be captured, so renaming*)
        let free_vars_of_f1_intersect_lx = SetVar.inter (free_variables_of_formula f1) (SetVar.of_list lx)
        and lx_to_lt = List.combine lx lt
        in
        let lt_concerned =  List.map (fun v -> List.assoc v lx_to_lt) (SetVar.elements free_vars_of_f1_intersect_lx)
        in
        if 
          List.exists (fun sv -> SetVar.mem v sv)  (List.map variables_term lt_concerned)
        then
          let  new_v = Var(new_var())
          in
          FExists(new_v, simultaneous_substitution_formula lx lt (simultaneous_substitution_formula [v] [(TV new_v)] f1))
        else (*it is safe to do forall(v, simultaneous_substitution_formula lx lt f1*)
          FExists(v, simultaneous_substitution_formula lx lt f1)


  (** The occurences of variables in t are not captured during a substition at the variable x in f **)
  let rec term_free_for_var t x = function
    | FNeg f ->
      term_free_for_var t x f
    | FAnd(f,g) | FOr(f,g) | FImply(f,g) -> 
      (term_free_for_var  t x f) && (term_free_for_var t x g)
    | FForall(v,f) | FExists(v,f) -> not (SetVar.mem v (variables_term t))
    | FAtomic_formula f_atomic -> true



  (** Printing formatters **)
  let printer_first_order_atomic_formula ff = function
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
      | FNeg g -> Format.fprintf ff "\\lnot "; print_par (fun () -> printer_first_order_formula_aux ff "neg" g);
      | FAnd(f, g) -> begin
          match f, g with
          | FImply(h1, h2), FImply(h2', h1') ->
            if (h1 = h1' && h2 = h2')
            (**TODO   TESTER ALPHA EQUIV????? **)
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
      | FOr(f, g) ->
        if seq = "or" || seq ="init" || (seq ="forall") || (seq ="exists")
        then
          print_bin "or" "\\lor" f g
        else
          print_par (fun () -> print_bin "or" "\\lor" f g)
      | FImply(f, g) -> if (seq ="init") || (seq ="forall") || (seq ="exists")
        then
          print_bin "impl" "=>" f g
        else
          print_par (fun () -> print_bin "impl" "=>" f g);
      | FForall(Var i, f) ->
        if (seq ="init")
        then
          begin
            Format.fprintf ff "\\forall ";
            print_term ff (TV (Var i));
            Format.fprintf ff ", ";
            printer_first_order_formula_aux ff "forall" f;
          end
        else
        if (seq = "forall")
        then
          begin
            print_term ff (TV (Var i));
            Format.fprintf ff ", ";
            printer_first_order_formula_aux ff "forall" f;
          end
        else
          begin
            print_par (fun () -> Format.fprintf ff "\\forall "; print_term ff (TV (Var i)); Format.fprintf ff ", ";
                        printer_first_order_formula_aux ff "forall" f);
          end
      | FForall(Metavar i, f) ->
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
            Format.fprintf ff "%s, " i;
            printer_first_order_formula_aux ff "forall" f;
          end
        else
          begin
            print_par (fun () -> Format.fprintf ff "\\forall %s, " i;printer_first_order_formula_aux ff "forall" f);
          end
      | FExists(Var i, f) ->
        if (seq ="init")
        then
          begin
            Format.fprintf ff "\\exists ";
            print_term ff (TV (Var i));
            Format.fprintf ff ", ";
            printer_first_order_formula_aux ff "exists" f;
          end
        else
        if (seq = "exists")
        then
          begin
            print_term ff (TV (Var i));
            Format.fprintf ff ", ";
            printer_first_order_formula_aux ff "exists" f;
          end
        else
          begin
            print_par (fun () -> Format.fprintf ff "\\exists "; print_term ff (TV (Var i)); Format.fprintf ff ", ";
                        printer_first_order_formula_aux ff "exists" f);
          end
      | FExists(Metavar i, f) ->
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
      | FAtomic_formula f -> printer_first_order_atomic_formula ff f

    in
    printer_first_order_formula_aux ff "init" f

end
