include Axioms_prop
open Formula_prop
include Formula_tooling
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

exception Invalid_demonstration of formula_prop * formula_prop list;;
Printexc.register_printer (function 
    | Invalid_demonstration(f,t) -> 
      Printexc.print_backtrace stdout; flush stdout;
      Some("Invalid demonstration: " ^ (to_string_formula_prop f) ^ "\n[[\n" ^
           (List.fold_left  (fun acc f1-> acc ^ (to_string_formula_prop f1) ^ "\n") ""  t) ^ "]]\n") 
    | _ -> None)
;;

let rec verif ?(axioms=[]) ?(theorems=[]) () ~hypotheses ~proved ~to_prove = 
  match to_prove with
  | [] -> true
  | f_i::p ->  
    if (
      (*Formula is an hypothesis*)
      List.mem f_i hypotheses 
      (*Formula already present *)
      || List.mem f_i proved
      (*Formula is an instance of a theorem or axiom *)
      || (List.exists (fun th -> 
          try
            Printf.printf " %s instance of %s (%s) ?\n" (to_string_formula_prop f_i ) th.name_theorem_prop (to_string_formula_prop th.conclusion_prop);
            Logs.debug (fun m -> m " %a instance of %s (%a) ?" pp_formula f_i th.name_theorem_prop pp_formula th.conclusion_prop);
            ignore(instance f_i th.conclusion_prop);
            print_endline "yes";
            Logs.debug (fun m ->  m "YES");
            true
          with 
          | _ -> 
            print_endline "no";
            Logs.debug (fun m ->  m "NO");
            false) 
          (theorems @ axioms)) 
      (*cut*)
      || (cut f_i proved) 
      (*application of notations*)
      || List.exists (fun f -> equiv_notation f_i f) proved
    )
    then 
      begin
        Logs.debug (fun m -> m "%a Proved" pp_formula f_i);
        verif ~axioms ~theorems () ~hypotheses ~proved:(f_i :: proved) ~to_prove:p
      end
    else 
      begin
        Logs.debug (fun m -> m "Not proved : %a" pp_formula f_i);
        raise (Invalid_demonstration (f_i,List.rev (f_i::proved)))
      end

let prop_proof_verif ?(axioms=[]) ?(theorems=[]) ?(hypotheses=[]) f ~proof:proof =
  (* f is at the end of the proof *)
  let is_end_proof f t =
    let rev_t = List.rev t
    in
    try
      f = List.hd rev_t
    with
    | Failure _ -> false
  in
  if not (is_end_proof f proof)
  then failwith "Formula is not at the end of the proof"
  else
    verif ~axioms ~theorems () ~hypotheses  ~proved:[] ~to_prove:proof
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
  kind_prop = Theorem;
  name_theorem_prop="[Bourbaki]C8";
  proof_prop = [];
  conclusion_prop=formula_from_string "X_1 \\implies X_1";
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
   kind_prop = Theorem;
   name_theorem_prop="chainage";
   proof_prop=demo_chaining;
   conclusion_prop=formula_from_string "(X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))";
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
  kind_prop = Assumed;
  name_theorem_prop="contraposition";
  proof_prop = [];
  conclusion_prop=formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
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
  kind_prop = Assumed;
  name_theorem_prop="[Bourbaki]S1";
  proof_prop = [];
  conclusion_prop=formula_from_string "(X_1 \\lor X_1) \\implies X_1";
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
  kind_prop = Assumed;
  name_theorem_prop="Excluded middle";
  proof_prop = [];
  conclusion_prop=formula_from_string "(X_1 \\lor \\lnot X_1)";
}::!theorems_prop;;
