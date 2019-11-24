include Axioms_prop
open Formula_prop
include (Prop_parser : sig 
           val formula_from_string : string -> Formula_prop.formula_prop
           val notation_from_string : string -> Formula_prop.notation_prop
         end)
(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
Prop_parser.formule lexbuf
*)
exception Failed_Unification of formula_prop * formula_prop


(*SKE TODO : where to put this function ?*)
let rec apply_notations = function 
  | PVar _ | PMetaVar _ as t -> t
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
    if  (apply_notation_prop_f.notation_prop_name = apply_notation_prop_g.notation_prop_name) 
    then
      List.for_all2 (fun f -> fun g -> equiv_notation f g) apply_notation_prop_params_f apply_notation_prop_params_g
    else 
      false
  | PApply_notation f, g ->
    let f' = get_semantique f  in
    equiv_notation f' g
  | f,  PApply_notation g ->
    let g' = get_semantique g  in
    equiv_notation f g'
  | _ -> false

(**	@param l list of PVariables of g already instanciated in f *)
let instance f g =
  let rec instance_aux l f g  = match f, g 
    with
    | _, (PVar _ as g) | _, (PMetaVar _ as g) -> begin
        try
          let (_, t) = List.find (fun (v1, _) -> v1 = g) l
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
    | PApply_notation f, g ->
      let f' = get_semantique f  in
      instance_aux l f' g
    | f,  PApply_notation g ->
      let g' = get_semantique g  in
      instance_aux l f g'

    | _ -> raise (Failed_Unification(f, g))
  in
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

let rec verif ~hypotheses ~proved ~to_prove = 
  match to_prove with
  | [] -> true
  | f_i::p ->  
    if 
      (   List.mem f_i hypotheses (*Formula is an hypothesis*)
          || List.mem f_i proved (*Formula already present *) 
          (*instance of a theorem or axiom *)
          || (List.exists (fun a -> instance f_i a.proposition_prop) 
                (!theorems_prop @ !axioms_prop)) 
          (*cut*)
          || (cut f_i proved) 
          || begin
            match proved with 
            | [] -> false 
            (*application of notations*)
            | f::_ -> equiv_notation f_i f 
          end
      )
    then 
      verif ~hypotheses ~proved:(f_i :: proved) ~to_prove:p
    else 
      raise (Invalid_demonstration (f_i,List.rev (f_i::proved)))

let proof_verification ~hyp:hypotheses f ~proof:proof =
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
    verif ~hypotheses  ~proved:[] ~to_prove:proof
;;
(*SKE TODO To remove*)
theorems_prop := {name_proposition_prop="C8 Bourbaki"; proposition_prop=formula_from_string "(X_1 \\implies X_1)";}::!theorems_prop;;
(*
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
*)
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
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))  \\implies 
    (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
    ]);;

theorems_prop := {name_proposition_prop="chainage"; proposition_prop=(formula_from_string "(X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))");}::!theorems_prop;;

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
*)
theorems_prop := {name_proposition_prop="contraposition"; proposition_prop=formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}::!theorems_prop;;

(* |   F ou F  \\implies  F *)
proof_verification ~hyp:[] (formula_from_string "(\\mathbb{A} \\lor \\mathbb{A})  \\implies  \\mathbb{A}")
    ~proof:(List.map formula_from_string [
        "((\\mathbb{A} \\lor\\mathbb{A})  \\implies  \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A}))";
        "((\\lnot \\mathbb{A})  \\implies   ((\\mathbb{A} \\lor \\mathbb{A})  \\implies  \\mathbb{A}))";
        "((\\lnot \\mathbb{A})  \\implies   ((\\mathbb{A} \\lor \\mathbb{A})  \\implies  \\mathbb{A}))  \\implies  ((((\\mathbb{A} \\lor\\mathbb{A})  \\implies  \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A})))  \\implies  ((\\lnot \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A}))))";
        "((((\\mathbb{A} \\lor\\mathbb{A})  \\implies  \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A})))  \\implies  ((\\lnot \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A}))))";
        "((\\lnot \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A})))";
        "((\\lnot \\mathbb{A})  \\implies  ((\\lnot \\mathbb{A})  \\implies  \\lnot (\\mathbb{A}\\lor\\mathbb{A})))  \\implies   (((\\lnot \\mathbb{A})  \\implies  (\\lnot \\mathbb{A}))  \\implies  ((\\lnot \\mathbb{A})  \\implies  (\\lnot (\\mathbb{A}\\lor\\mathbb{A}))))";
        "((\\lnot \\mathbb{A})  \\implies  (\\lnot \\mathbb{A}))";
        "(((\\lnot \\mathbb{A})  \\implies  (\\lnot \\mathbb{A}))  \\implies  ((\\lnot \\mathbb{A})  \\implies  (\\lnot (\\mathbb{A}\\lor\\mathbb{A}))))";
        "((\\lnot \\mathbb{A})  \\implies  (\\lnot (\\mathbb{A}\\lor\\mathbb{A})))";
        "((\\lnot \\mathbb{A})  \\implies  (\\lnot (\\mathbb{A}\\lor\\mathbb{A})))  \\implies   ((\\mathbb{A}\\lor\\mathbb{A})   \\implies  \\mathbb{A})";
        "(\\mathbb{A}\\lor \\mathbb{A})  \\implies  \\mathbb{A}";
      ]);;

theorems_prop := {name_proposition_prop="[Bourbaki]S1"; proposition_prop=(formula_from_string "(X_1 \\lor X_1) \\implies X_1");}::!theorems_prop;;

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
theorems_prop := {name_proposition_prop="Excluded middle"; proposition_prop=formula_from_string "(X_1 \\lor \\lnot X_1)";}::!theorems_prop;;
