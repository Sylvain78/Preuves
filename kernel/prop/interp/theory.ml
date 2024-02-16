open Kernel.Logic
open Formula_prop
open Theorem_prop

module Prop:(LOGIC 
             with type formula = formula_prop 
              and type notation = notation_prop
              and type demonstration = demonstration_prop
            ) =
struct



  include Axioms_prop
  include Instance_notation_printers
  include Theorem_prop
  (*TODO open Substitution_prop*)
  include (Prop_parser : sig 
             val formula_from_string : string -> Formula_prop.formula_prop
             val notation_from_string : string -> Formula_prop.notation_prop
             (* TODO one day ... 
              * val save_parser : string -> unit
              * *)
           end)

(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
Prop_parser.formule lexbuf
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
    | PImpl(f1, f2) , PImpl(g1, g2) ->  (equiv_notation f2 g2) && (equiv_notation f1 g1)
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

  let theorems_prop = ref []

  type formula = formula_prop
  type notation = notation_prop
  type demonstration = demonstration_prop
  let axioms = axioms_prop
  let add_axiom ax = axioms := ax :: !axioms
  let theorems = theorems_prop
  type theorem = (formula, demonstration) Kernel.Logic.theorem_logic 
  type step =  
    | Single of formula 
    | Call of {theorem : theorem; params : formula list}
  type theorem_unproved = (formula, step list) Kernel.Logic.theorem_logic 
  let string_to_formula = formula_from_string
  let formula_to_string = to_string_formula_prop
  let printer_formula = printer_formula_prop
  let string_to_notation = notation_from_string
  let printer_demonstration ff d=
    (Format.pp_print_list ~pp_sep:Format.pp_print_newline printer_formula) ff d
  let printer_step ff = function
    | Single f -> Format.fprintf ff "Single(%a)" printer_formula f
    | Call{theorem; params} -> Format.fprintf ff "Call(%s,%a)" theorem.name 
                                 (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_char out  ',')
                                     printer_formula out l) params
  exception Invalid_demonstration of theorem_unproved

  let print_invalid_demonstration =  (function 
      | Invalid_demonstration {conclusion=f;premisses=hypotheses;demonstration=demo;_} -> 
        (*Printexc.print_backtrace stderr; flush stderr;*)
        Some (
          Format.fprintf Format.str_formatter "Invalid demonstration of %a\n\ntheorems:\n%a\n\nhypotheses:%a\n\ndemonstration:%a\n\n" printer_formula f
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_char out  ',') (fun out t -> Format.pp_print_string out t.name) out l) !theorems
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_char out  ',') printer_formula  out l) hypotheses
            (fun out l -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_char out  ',') printer_step  out l) demo ; 
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
    List.exists (function axiom -> try ignore (instance f axiom.conclusion);true  with Failed_Unification _ -> false) !axioms_prop

  let rec compile ~speed ?(hypotheses=[]) ~demonstration () = 
    match demonstration 
    with 
    | [] -> []
    | Single f as step:: l -> ([f],step) :: (compile ~speed ~hypotheses ~demonstration:l ())
    | Call {theorem ; params } as step :: l ->
      match speed with
      | Fast -> ([(Substitution_prop.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params theorem.conclusion)],step) :: (compile ~speed ~hypotheses ~demonstration:l ())
      | Paranoid -> ((List.map (function step -> (Substitution_prop.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params step)) theorem.demonstration),step) 
                    :: (compile ~speed ~hypotheses ~demonstration:l ())

  let rec verif_prop ~(hypotheses:formula list) ~(proved:(formula * step) list) ~(to_prove:(formula list * step) list) = 
    match to_prove with
    | [] -> Ok ()
    | ([f_i],(Single f as step))::p  when f = f_i->  
      if (
        (*Formula is an hypothesis*)
        List.mem f_i hypotheses 
        (*Formula already present *)
        || List.mem f_i (fst @@ List.split proved)
        (*Formula is an instance of a theorem or axiom *)
        || (List.exists (fun th -> 
            try
              Logs.debug (fun m -> m " %a instance of %s (%a) ?" pp_formula f_i th.name pp_formula th.conclusion);
              ignore(instance f_i th.conclusion);
              Logs.debug (fun m ->  m "YES");
              true
            with 
            | _ -> 
              Logs.debug (fun m ->  m "NO");
              false) 
            (!theorems))
        || is_instance_axiom f_i
        (*cut*)
        || (cut f_i (fst @@ List.split proved)) 
        (*application of notations*)
        || List.exists (fun f -> equiv_notation f_i f) (fst @@ List.split proved)
      )
      then 
        begin
          Logs.debug (fun m -> m "%a Proved" pp_formula f_i);
          verif_prop ~hypotheses ~proved:((f_i,step) :: proved) ~to_prove:p
        end
      else 
        begin
          Logs.debug (fun m -> m "Not proved : %a" pp_formula f_i);
          Error ("Invalid demonstration", (f_i, !theorems, hypotheses, List.rev (step::(snd @@ List.split proved))))
        end
    | _ -> failwith "to implement"

  let kernel_prop_interp_verif ~speed ~hypotheses ~formula:(f:formula) ~proof:(proof:step list)  =
    let compiled_proof = compile ~speed ~demonstration:proof ()
    in
    (* f is at the end of the proof *)
    let is_end_proof f t =
      let rev_t = List.rev t
      in
      try
        f = List.hd rev_t
      with
      | Failure _ -> false
    in
    if not (is_end_proof f (List.flatten @@ fst @@ List.split compiled_proof))
    then Error ("Formula is not at the end of the proof", (f, !theorems, hypotheses, snd @@ List.split compiled_proof))
    else
      verif_prop ~hypotheses ~proved:[] ~to_prove:compiled_proof
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
    kind = Theorem;
    name="[Bourbaki]C8";
    demonstration = [];
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
     kind = Theorem;
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
  kind = Assumed;
  name="contraposition";
  demonstration = [];
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
  kind = Assumed;
  name="[Bourbaki]S1";
  demonstration = [];
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
   *)
  theorems_prop := {
    kind = Assumed;
    name="Excluded middle";
    params = [];
    premisses = [];
    demonstration = [];
    conclusion=formula_from_string "(X_1 \\lor \\lnot X_1)";
  }::!theorems_prop;;


  let verif ~speed theorem_unproved = 
    let compiled_demonstration = compile ~speed ~hypotheses:theorem_unproved.premisses ~demonstration:theorem_unproved.demonstration ()
    in
    match kernel_prop_interp_verif ~speed ~hypotheses:theorem_unproved.premisses ~formula:theorem_unproved.conclusion ~proof:theorem_unproved.demonstration
    with
    | Ok () -> Ok {theorem_unproved with demonstration = compiled_demonstration} 
    | Error _ -> Error ("invalid",Invalid_demonstration theorem_unproved)

end