open Axioms_prop
open Formula_prop
open Prop_parser 
(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
	Prop_parser.formule lexbuf
*)
exception Failed_Unification of formula_prop * formula_prop


(*SKE TODO : where to put this function ?*)
let rec apply_notations = function 
  | PVar v as t -> t
  | PNeg f -> PNeg (apply_notations f)
  | PAnd(f1,f2) -> PAnd(apply_notations f1, apply_notations f2) 
  | POr(f1,f2) -> POr(apply_notations f1, apply_notations f2) 
  | PImpl(f1,f2) -> PImpl(apply_notations f1, apply_notations f2) 
  | PApply_notation {apply_notation_prop = n ; apply_notation_prop_params = list_params } ->
    let  replace  m = function 
      | Param a  -> begin
          try  (to_string_formula_prop  (List.assoc (Param a) m))
          with Not_found -> failwith "apply_notations"
        end
      | String s  -> s 
    in
    let map_param_val = List.combine n.notation_prop_params list_params
    in 
    let notation_with_params_replaced = List.map (replace map_param_val ) n.notation_prop_semantique
    in
    formula_from_string (List.fold_left  (fun s t -> s ^ " " ^ t) "" notation_with_params_replaced)

let get_semantique ({apply_notation_prop; apply_notation_prop_params}:apply_notation_prop) =
  let map_params = List.combine apply_notation_prop.notation_prop_params apply_notation_prop_params
  in
  let replace = function 
    | String s -> " " ^ s ^ " "
    | Param _ as p -> "(" ^ (to_string_formula_prop (List.assoc p map_params)) ^ ")"
  in
  formula_from_string
    (        List.fold_left (fun s e -> s^(replace e)) "" apply_notation_prop.notation_prop_semantique)

let rec instance_aux l f g  = match f, g 
  with
  | _, (PVar i as g) -> begin
      try
        let (v, t) = List.find (fun (v1, t1) -> v1 = g) l
        in
        if (t = f) then l
        else raise (Failed_Unification(f, g))
      with Not_found -> (g, f)::l (*g=Xi bound to f*)
    end
  | PNeg f1 , PNeg g1 -> instance_aux l f1 g1
  | PAnd(f1, f2) , PAnd(g1, g2) 
  | POr(f1, f2) , POr(g1, g2) 
  | PImpl(f1, f2) , PImpl(g1, g2) -> instance_aux (instance_aux l f2 g2) f1 g1
  | PApply_notation {apply_notation_prop=apply_notation_prop_f; apply_notation_prop_params = apply_notation_prop_params_f}, 
    PApply_notation {apply_notation_prop=apply_notation_prop_g; apply_notation_prop_params=apply_notation_prop_params_g} -> 
    if  (apply_notation_prop_f.notation_prop_name = apply_notation_prop_g.notation_prop_name) 
    then
      (List.fold_left (fun list_instances (f,g) -> instance_aux list_instances f g) l  (List.combine apply_notation_prop_params_f apply_notation_prop_params_g) )
    else raise (Failed_Unification(f, g))
  | PApply_notation ({apply_notation_prop=apply_notation_prop_f; apply_notation_prop_params = apply_notation_prop_params_f} as f), g->
    let f' = get_semantique f  in
    instance_aux l f' g
  | f,  PApply_notation ({apply_notation_prop=apply_notation_prop_g; apply_notation_prop_params = apply_notation_prop_params_g} as g)->
    let g' = get_semantique g  in
    instance_aux l f g'
  | _ -> raise (Failed_Unification(f, g))
and instance f g = (*TODO reencapsularte instance_aux in instance *)
  (**	@param l list of PVariables of g already instanciated in f *)

  try  
    instance_aux [] f g <> []
  with _ -> false



let cut f p =
  List.exists (function | PImpl(g1, g2) -> g2 = f && List.mem g1 p | _ -> false) p

let theorems_prop = ref []

exception Invalid_demonstration of formula_prop * formula_prop list;;
Printexc.register_printer (function Invalid_demonstration(f,t) -> 
    Some("Invalid demonstration: " ^ (to_string_formula_prop f) ^ "\n[[\n" ^
         (List.fold_left  (fun acc f1-> acc ^ (to_string_formula_prop f1) ^ "\n") ""  t) ^ "]]\n") 
                                  | _ -> None)
;;

let rec verif t = function
  | [] -> true
  | f_i::p as demo -> 
    let f_i_normalized = apply_notations f_i
    in
    if 
      (List.mem f_i_normalized t (*Formula already present *)
       (*instance of an axiom or a theorem*)
       || (List.exists (fun a -> instance (apply_notations f_i_normalized) a.axiom_prop) 
             (axioms_prop @ !theorems_prop)) 
       || (cut f_i_normalized p)) (*cut*)
    then verif t p
    else raise (Invalid_demonstration (f_i_normalized,List.rev demo))

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
    verif hypotheses (List.rev (proof))
;;
(*SKE TODO To remove*)
theorems_prop := {name_axiom_prop="C8 Bourbaki"; axiom_prop=formula_from_string "(X_1 \\implies X_1)";}::!theorems_prop;;

(* |   F \\implies  *)
proof_verification ~hyp:[] (formula_from_string "X_1 \\implies X_1") 
  ~proof:(List.map formula_from_string [
      "(X_1  \\implies ((X_1  \\implies  X_1) \\implies X_1))  \\implies 
    (( X_1  \\implies  (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1))";
      "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
      "(X_1 \\implies (X_1  \\implies  X_1))  \\implies  (X_1  \\implies  X_1)";
      "X_1 \\implies (X_1 \\implies X_1)";
      "X_1 \\implies X_1"
    ]);;

(* |   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)*)
proof_verification ~hyp:[] (formula_from_string "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))")
  ~proof: (List.map formula_from_string [
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
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))  \\implies 
    (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
    ]);;
theorems_prop := {name_axiom_prop="???"; axiom_prop=(formula_from_string "(X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))");}::!theorems_prop;;

(*non A  \\implies  non B |   B  \\implies  A*)
(* TODO : delete once they are not needed anymore
   let h = ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))	
   and ((\\lnot (\\lnot X_1)) \\implies X_1) =((\\lnot (\\lnot X_1)) \\implies  X_1)
   and ((\\lnot (\\lnot X_2)) \\implies X_1) = ((\\lnot (\\lnot X_2)) \\implies  X_1)	
   and (X_2 \\implies \\lnot (\\lnot X_2))=	(X_2 \\implies \\lnot (\\lnot X_2))
   in
*)
proof_verification ~hyp:[] (formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))")
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
theorems_prop := {name_axiom_prop="contraposition"; axiom_prop=formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}::!theorems_prop;;

(* |   F ou F  \\implies  F *)
proof_verification ~hyp:[] (formula_from_string "(X_1 \\lor X_1) \\implies X_1")
  ~proof:(List.map formula_from_string [
      "((X_1 \\lor X_1)  \\implies  X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))";
      "((\\lnot X_1) \\implies  ((X_1 \\lor X_1)  \\implies  X_1))";
      "((\\lnot X_1) \\implies  ((X_1 \\lor X_1)  \\implies  X_1)) \\implies ((((X_1 \\lor X_1)  \\implies  X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))))";
      "((((X_1 \\lor X_1)  \\implies  X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))))";
      "((\\lnot X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1)))";
      "((\\lnot X_1) \\implies ((\\lnot X_1)  \\implies  \\lnot (X_1\\lor X_1))) \\implies  (((\\lnot X_1)  \\implies  (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lor X_1))))";
      "((\\lnot X_1)  \\implies  (\\lnot X_1))";
      "(((\\lnot X_1)  \\implies  (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lor X_1))))";
      "((\\lnot X_1) \\implies (\\lnot (X_1\\lor X_1)))";
      "((\\lnot X_1) \\implies (\\lnot (X_1\\lor X_1))) \\implies  ((X_1\\lor X_1)  \\implies X_1)";
      "(X_1\\lor X_1)  \\implies  X_1";
    ]);;
theorems_prop := {name_axiom_prop="[Bourbaki]S1"; axiom_prop=(formula_from_string "(X_1 \\lor X_1) \\implies X_1");}::!theorems_prop;;

(*|   A ou \\lnot A*)
(* TODO delete when not need anymore
   let X_1 \\lor \\lnot X_1 = X_1 \\lor \\lnot X_1
   and \\lnot (X_1 \\implies X_1) = \\lnot (X_1 \\implies X_1)
   in
*)
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
theorems_prop := {name_axiom_prop="Excluded middle"; axiom_prop=formula_from_string "(X_1 \\lor \\lnot X_1)";}::!theorems_prop;;
