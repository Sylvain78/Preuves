open Kernel.Logic
open Formula

module Prop:(LOGIC
             with type formula = formula_prop
              and type notation = notation_prop
              and type demonstration = Theorem.demonstration_prop
              and type theorem = Theorem.theorem_prop
            ) =
struct



  include Axioms
  include Instance_notation_printers
  include Theorem


  (*TODO open Substitution*)
  include (Parser : sig
             val formula_from_string : string -> Formula.formula_prop
             val notation_from_string : string -> Formula.notation_prop
             (* TODO one day ...
              * val save_parser : string -> unit
              * *)
           end)

(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Parser.pp ()) s
        in
Parser.formule lexbuf
*)

  (* Equivalence of formulas, modulo notations*)
  let rec equiv_notation f g =
    match f, g
    with
    | PVar v1, PVar v2 -> v1=v2
    | PMetaVar v1, PMetaVar v2 -> v1=v2
    | PNeg f1 , PNeg g1 -> equiv_notation f1 g1
    | PAnd(f1, f2) , PAnd(g1, g2)
    | POr(f1, f2) , POr(g1, g2)
    | PImpl(f1, f2) , PImpl(g1, g2)
    | PImpl(f1, f2), POr(PNeg g1, g2)
    | POr(PNeg f1, f2),PImpl(g1, g2) ->  (equiv_notation f2 g2) && (equiv_notation f1 g1)
    | PApply_notation {apply_notation_prop=apply_notation_prop_f; apply_notation_prop_params = apply_notation_prop_params_f},
      PApply_notation {apply_notation_prop=apply_notation_prop_g; apply_notation_prop_params=apply_notation_prop_params_g} ->
      if (apply_notation_prop_f.notation_prop_name = apply_notation_prop_g.notation_prop_name)
      then
        List.for_all2 (fun f -> fun g -> equiv_notation f g) apply_notation_prop_params_f apply_notation_prop_params_g
      else
        false
    | PApply_notation f, g ->
      let f' = get_semantique f in
      equiv_notation f' g
    | f,  PApply_notation g ->
      let g' = get_semantique g in
      equiv_notation f g'
    | _ -> false


  let cut f p =
    List.exists (function | PImpl(g1, g2) -> g2 = f && List.mem g1 p
                          | PApply_notation n ->
                            begin
                              match get_semantique n
                              with
                              | PImpl(g1,g2) -> g2 = f && List.mem g1 p
                              | PApply_notation _ -> failwith "cut : get_semantique evaluates to another notation"
                              | _ -> false
                            end
                          | _ -> false) p


  type formula = formula_prop
  type notation = notation_prop
  type step = step_prop =
      Single of formula
    | Call of { theorem : theorem; params : formula list; }
  and demonstration = demonstration_prop = Demonstration of (formula list * step) list [@@unboxed]
  and theorem = theorem_prop = Theorem of (formula, demonstration) Kernel.Logic.theorem_logic [@@unboxed]
  type theorem_unproved = (formula, step list) Kernel.Logic.theorem_logic

  module Theorems =
  struct
    type t = theorem
    let (theorems : t Dynarray.t) = Dynarray.create()
    let get_theorems () = Dynarray.to_list theorems
    let add_theorem th = Dynarray.add_last theorems th
    let find_by_name ~name =
      let limit = Dynarray.length theorems - 1
      in
      let rec find_aux index  =
        if (index > limit)
        then
          failwith ("Theorem " ^ name ^ " not found.")
        else
          let theorem =
            match Dynarray.get theorems index
            with Theorem theorem -> theorem
          in
          if theorem.name = name
          then
            Theorem theorem,index
          else
            find_aux (index+1)
      in
      find_aux 0
    let invalidate_theorem theorem_name =
      let theorem =
        match fst(find_by_name ~name:theorem_name) with
        | Theorem theorem -> theorem
      in theorem.kind <- KInvalid

  end

  exception Invalid_demonstration of theorem_unproved
  exception Premisses_not_verified of formula list

  let empty_demonstration = Demonstration []
  let axioms = axioms_prop
  let add_axiom ax = axioms := ax :: !axioms
  let string_to_formula s =
    try
      formula_from_string s
    with Dyp.Syntax_error -> failwith ("Unparsable formula : $" ^ s ^ "$")
  let formula_to_string = to_string_formula_prop
  let printer_formula = printer_formula_prop
  let string_to_notation = notation_from_string
  let printer_step ff = function
    | Single f -> Format.fprintf ff "Single(%a)" printer_formula f
    | Call{theorem=Theorem theorem; params} ->
      let print_formula_list = (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_char out  ',') printer_formula out l)
      in
      Format.fprintf ff "Call(%s,%a)[%a]" theorem.name
        print_formula_list  params
        print_formula_list
        (match theorem.demonstration
         with Demonstration  l ->
           List.map (function f -> Substitution.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params f)
             (List.flatten (List.map fst l))
        )
  let printer_demonstration ff (Demonstration d) =
    (Format.pp_print_list ~pp_sep:Format.pp_print_newline printer_step) ff (snd @@ List.split d)

  let print_invalid_demonstration =  (function
      | Invalid_demonstration {conclusion=f;premisses=hypotheses;demonstration=demo;_} ->
        (*Printexc.print_backtrace stderr; flush stderr;*)
        Some (
          Format.fprintf Format.str_formatter "Invalid demonstration of %a\n\ntheorems:\n%a\n\nhypotheses:%a\n\ndemonstration:%a\n\n" printer_formula f
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_string out  ",\n") (fun out (Theorem t) -> Format.pp_print_string out (t.name^(Kernel.Logic.kind_to_string t.kind))) out l) (Theorems.get_theorems())
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_string out  ",\n") printer_formula  out l) hypotheses
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_string out  ",\n") printer_step  out l) demo ;
          Format.flush_str_formatter()
        )
      | Premisses_not_verified lf -> Some (
          Format.fprintf Format.str_formatter "[$%a$]"
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_string out  "$,$\n") printer_formula  out l) lf;
          Format.flush_str_formatter()
        )

(*

          "Invalid demonstration of " ^ (to_string_formula_prop f) ^ "\n" ^
             "theorems:(" ^
             (List.fold_right (fun th s -> th.name^","^s) theorems "") ^
             ")" ^
             "hypotheses:(" ^
             (List.fold_right (fun hyp s -> (to_string_formula_prop hyp)^","^s) hypotheses "") ^
             ")" ^
             "demonstration:[[\n" ^
             (List.fold_left  (fun acc f1-> acc ^ (to_string_formula_prop f1) ^ "\n") ""  demo) ^ "]]\n"*)
      | _ -> None);;
  Printexc.register_printer (print_invalid_demonstration)

  let is_instance_axiom f =
    List.exists (function Theorem axiom -> try ignore (instance f axiom.conclusion);true  with Failed_Unification _ -> false) !axioms_prop

  let compile ~keep_calls ?(hypotheses=[]) ~demonstration () =
    let rec compile_aux ~keep_calls ?(hypotheses=[]) ~demonstration ()   =
      let subst = Substitution.simultaneous_substitution_formula_prop
      in
      match demonstration
      with
      | [] ->  []
      | Single f as step:: l ->  ([f],step) :: (compile_aux ~keep_calls ~hypotheses ~demonstration:l ())
      | Call {theorem = Theorem theorem ; params } as step :: l ->
        if (theorem.kind = KInvalid)
        then
          (compile_aux ~keep_calls ~hypotheses ~demonstration:l ())
        else
          match keep_calls with
          | Keep_Calls ->  ([(Substitution.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params theorem.conclusion)],step)
                           :: (compile_aux ~keep_calls ~hypotheses ~demonstration:l ())
          | Expand_Calls -> (List.map (fun f ->subst  ~vars:theorem.params ~terms:params f)
                               (theorem.premisses @ (List.flatten @@ fst @@ List.split (match theorem.demonstration with Demonstration d -> d))),
                             step)
                            :: (compile_aux ~keep_calls ~hypotheses ~demonstration:l ())
    in
    Demonstration (compile_aux ~keep_calls ~hypotheses ~demonstration ())

  let rec verif_prop ~keep_calls ~name ~(hypotheses:formula list) ~(proved:(formula list * step) list) ~(to_prove:demonstration ) ~(original_proof:theorem_unproved) =
    let verif_formula hypotheses proved f =
      (*Formula is an hypothesis*)
      List.mem f hypotheses
      (*Formula already present *)
      || List.mem f (List.flatten @@ fst @@ List.split proved)
      (*Formula is an instance of a theorem or axiom *)
      || (List.exists (fun (Theorem th) ->
          try
            Logs.debug (fun m -> m " %a instance of %s (%a) ?" pp_formula f th.name pp_formula th.conclusion);
            ignore(instance f th.conclusion);
            Logs.debug (fun m ->  m "YES");
            true
          with
          | _ ->
            Logs.debug (fun m ->  m "NO");
            false)
          (List.filter (function Theorem th -> match th.kind with KAssumed | KAxiom | KTheorem -> true | KInvalid | KUnproved -> false) (Theorems.get_theorems())))
      || is_instance_axiom f
      (*cut*)
      || (cut f (List.flatten @@ fst @@ List.split proved))
      (*application of notations*)
      || List.exists (fun f' -> equiv_notation f f') (List.flatten @@ fst @@ List.split proved)
    in
      let subst = Substitution.simultaneous_substitution_formula_prop
      in
    match to_prove with
    | Demonstration [] ->
      let demonstration = Demonstration(List.rev proved)
      in
      printer_demonstration Format.std_formatter demonstration;
      Ok (Theorem { original_proof with demonstration = demonstration})
    | Demonstration (([f_i],(Single f as step))::p)  when f = f_i->
      if (verif_formula hypotheses proved f_i)
      then
        begin
          Logs.debug (fun m -> m "%a Proved" pp_formula f_i);
          verif_prop ~keep_calls ~name ~hypotheses ~proved:(([f_i],step) :: proved) ~to_prove:(Demonstration p) ~original_proof
        end
      else
        begin
          Logs.debug (fun m -> m "Not proved : %a" pp_formula f_i);
          Error ("Invalid demonstration", Invalid_demonstration {kind=KUnproved;name;params = []; premisses=hypotheses; conclusion=f_i; demonstration=List.rev (step::(snd @@ List.split proved))})
        end
    | Demonstration ((l,(Call({theorem = Theorem theorem; params}) as step))::p)
      when (subst  ~vars:theorem.params ~terms:params theorem.conclusion) = List.(hd (rev l)) ->
      begin
        match keep_calls with
        | Expand_Calls ->
          verif_prop ~keep_calls ~name ~hypotheses ~proved
            ~to_prove:(Demonstration ((List.map (function f -> ([f],Single f)) ((List.map (subst ~vars:theorem.params ~terms:params )theorem.premisses) @ l) @ p))) ~original_proof
        | Keep_Calls ->
         match   List.find_all (fun f -> not (verif_formula hypotheses proved (subst ~vars:theorem.params ~terms:params f))) theorem.premisses
         with
         | (_::_) as l-> Error ("Premisses of $" ^ theorem.name ^ "$ not verified", Premisses_not_verified (List.map (subst  ~vars:theorem.params ~terms:params) l))
         | [] -> verif_prop ~keep_calls ~name ~hypotheses ~proved:(([(subst ~vars:theorem.params ~terms:params theorem.conclusion)],step) :: proved) ~to_prove:(Demonstration p) ~original_proof
      end
    | d ->
      begin
        Format.fprintf Format.std_formatter "XYX Dem(%a)" printer_demonstration d;
        failwith "to implement (unknown shape of Demonstration)"
      end

  (* f is at the end of the proof *)
  let is_formula_at_end f t =
    let rev_t = List.rev t
    in
    try
      match List.hd rev_t
      with
      | Single g when g = f -> true
      | Single _ -> failwith "Formula not at the end, but didn't check the notation reductions in single step."
      | Call ({theorem = Theorem theorem; params}) when equiv_notation (Substitution.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params theorem.conclusion)  f -> true
      | Call ({theorem = Theorem theorem; params}) ->
        begin
          Logs.debug (fun m -> m "[is_formula_at_end]formula =%a,last_demo = %a "pp_formula f pp_formula (Substitution.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params theorem.conclusion));
          failwith "Formula not at the end, but didn't check the notation reductions in call."
        end
    with
    | Failure _ -> false

  let kernel_prop_interp_verif ~keep_calls theorem_unproved =
    let compiled_proof =
      compile ~keep_calls ~demonstration:theorem_unproved.demonstration ()
    in
    verif_prop ~keep_calls ~name:theorem_unproved.name ~hypotheses:theorem_unproved.premisses ~proved:[] ~to_prove:compiled_proof ~original_proof:theorem_unproved
  ;;

  (*displaced in theories/Bourbaki_Logic.prf
    (* |   F \\implies  F *)
    prop_proof_verif  ~hyp:[] (formula_from_string "X_1 \\implies X_1")
    ~proof:(List.map formula_from_string [
        "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies
      (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ]);;

    theorems_prop := {
    kind = KTheorem;
    name="[Bourbaki]C8";
    demonstration = Demonstration [];
    conclusion=formula_from_string "X_1 \\implies X_1";
    }::!theorems_prop;;
  *)

  (* Displaced in theories/Bourbaki_Logic.prf
     |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
     let demo_chaining =
     List.map (fun s -> (formula_from_string s)) [
      "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";
      "((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies  (X_1 \\implies (X_2 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      (*k*)
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)))";

      (*s*)
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))  \\implies
      (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
     ]
     ;;

     theorems_prop := {
     kind = KTheorem;
     name="chainage";
     demonstration=demo_chaining;
     conclusion=formula_from_string "(X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))";
     }::!theorems_prop;;
  *)
  (*non A  \\implies  non B |   B  \\implies  A*)
  (* TODO : delete once they are not needed anymore
     let h = ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))	
     and ((\\lnot (\\lnot X_1)) \\implies X_1) =((\\lnot (\\lnot X_1)) \\implies  X_1)
     and ((\\lnot (\\lnot X_2)) \\implies X_1) = ((\\lnot (\\lnot X_2)) \\implies  X_1)	
     and (X_2 \\implies \\lnot (\\lnot X_2))=	(X_2 \\implies \\lnot (\\lnot X_2))
     in
  *)
(*
 * proof_verification ~hyp:[] (formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))")
  ~proof:(List.map formula_from_string [

      "((\\lnot (\\lnot X_1)) \\implies X_1)";
      "((\\lnot (\\lnot X_1)) \\implies X_1) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1))";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))  \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))  \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
      "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)";
      "(X_2 \\implies \\lnot (\\lnot X_2))";
      "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2)))";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))";
      "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
      "((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies  (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))  \\implies  ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1)))";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)))";
      "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1))";
      "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)";
      "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))))";
      "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
      "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
      "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";
    ]);;
theorems_prop := {
  kind = KAssumed;
  name="contraposition";
  demonstration = Demonstration [];
  conclusion=formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
  ::!theorems_prop;;
*)
(*
(* |   F ou F  \\implies  F *)
prop_proof_verif ~hyp:[] (formula_from_string "(\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A}")
  ~proof:(List.map (fun s -> (formula_from_string s)) [
      "((\\mathbf{A} \\lor\\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A}))";
      "((\\lnot \\mathbf{A})  \\implies   ((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A}))";
      "((\\lnot \\mathbf{A})  \\implies   ((\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A}))  \\implies  ((((\\mathbf{A} \\lor\\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A})))  \\implies  ((\\lnot \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A}))))";
      "((((\\mathbf{A} \\lor\\mathbf{A})  \\implies  \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A})))  \\implies  ((\\lnot \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A}))))";
      "((\\lnot \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A})))";
      "((\\lnot \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  \\lnot (\\mathbf{A}\\lor\\mathbf{A})))  \\implies   (((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A}))  \\implies  ((\\lnot \\mathbf{A})  \\implies  (\\lnot (\\mathbf{A}\\lor\\mathbf{A}))))";
      "((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A}))";
      "(((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A}))  \\implies  ((\\lnot \\mathbf{A})  \\implies  (\\lnot (\\mathbf{A}\\lor\\mathbf{A}))))";
      "((\\lnot \\mathbf{A})  \\implies  (\\lnot (\\mathbf{A}\\lor\\mathbf{A})))";
      "((\\lnot \\mathbf{A})  \\implies  (\\lnot (\\mathbf{A}\\lor\\mathbf{A})))  \\implies   ((\\mathbf{A}\\lor\\mathbf{A})   \\implies  \\mathbf{A})";
      "(\\mathbf{A}\\lor \\mathbf{A})  \\implies  \\mathbf{A}";
    ]);;

theorems_prop := {
  kind = KAssumed;
  name="[Bourbaki]S1";
  demonstration = Demonstration [];
  conclusion=formula_from_string "(X_1 \\lor X_1) \\implies X_1";
}::!theorems_prop;;
*)

  (*|   A ou \\lnot A*)
  (* TODO delete when not need anymore
     let X_1 \\lor \\lnot X_1 = X_1 \\lor \\lnot X_1
     and \\lnot (X_1 \\implies X_1) = \\lnot (X_1 \\implies X_1)
     in
  *)
(*
proof_verification ~hyp:[] (formula_from_string "X_1 \\lor \\lnot X_1")
  ~proof:(List.map formula_from_string [
      "(X_1 \\implies X_1)";(**)
      "(X_1 \\implies X_1)  \\implies  (\\lnot (\\lnot (X_1 \\implies X_1)))"; (**)
      "\\lnot (\\lnot (X_1 \\implies X_1))";(*OK*)

      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)

      "X_1 \\implies (X_1 \\lor \\lnot X_1)";(**)
      "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  (X_1 \\implies (X_1 \\lor \\lnot X_1)))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\implies ((X_1 \\lor \\lnot X_1)))";(*OK*)

      "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; (**)
      "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))  \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))))"; (**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; (*OK*)

      "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  \\lnot X_1)";(**)
      "((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  \\lnot X_1)";(**)
      "((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  \\lnot X_1) \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  \\lnot X_1))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))";(*OK*)

      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))) \\implies (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))";(**)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)";(*OK*)

      "(\\lnot X_1) \\implies  (X_1 \\lor \\lnot X_1)";(**)
      "((\\lnot X_1) \\implies  (X_1 \\lor \\lnot X_1)) \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies  (X_1 \\lor \\lnot X_1)))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor \\lnot X_1)))";(*OK*)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor \\lnot X_1)))) \\implies (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (\\lnot X_1)) \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (X_1 \\lor \\lnot X_1)))";(**)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (\\lnot X_1)) \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (X_1 \\lor \\lnot X_1))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1))";(*OK*)

      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))";(*OK*)

      "((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))";(**)
      "(((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies   ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))))";(**)

      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))";(*OK*)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))) \\implies  (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";(**)
      "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))";(*OK*)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies  (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1))  \\implies  ((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  (\\lnot (X_1 \\implies X_1))))";(**)
      "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1))  \\implies  ((\\lnot (X_1 \\lor \\lnot X_1))  \\implies  (\\lnot (X_1 \\implies X_1))))";(**)
      "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))";(*OK*)
      "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1))))";(*OK*)
      "(\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1)))";(*OK*)
      "(\\lnot(\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((X_1 \\lor \\lnot X_1))";(*OK*)
      "\\lnot(\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)
      "(X_1 \\lor \\lnot X_1)"
    ]);;
  theorems_prop := (Theorem {
      kind = KAssumed;
      name="Excluded middle";
      params = [];
      premisses = [];
      demonstration = Demonstration [];
      conclusion=formula_from_string "(X_1 \\lor \\lnot X_1)";
    })::!theorems_prop;;
   *)

  let verif ~keep_calls theorem_unproved =
    if not (is_formula_at_end theorem_unproved.conclusion  theorem_unproved.demonstration)
    then
      begin
        Logs.debug (fun m -> m "Conclusion :\n%a" pp_formula theorem_unproved.conclusion);
        Error ("Formula is not at the end of the proof", Invalid_demonstration theorem_unproved)
      end
    else
      kernel_prop_interp_verif ~keep_calls theorem_unproved

end
