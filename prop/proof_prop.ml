include Axioms_prop
open Formula_prop
(*TODO open Substitution_prop*)
include (Prop_parser : sig 
           val formula_from_string : string -> Formula_prop.formula_prop
         end)
(*
let (read_formule : string -> (formula_prop * string) list) = function s ->
        let lexbuf = Dyp.from_string (Prop_parser.pp ()) s
        in
Prop_parser.formule lexbuf
*)
exception Failed_Unification of formula_prop * formula_prop

type theorem_prop = 
  {
    name_theorem_prop : string;
    parameters_prop : var_prop list;
    premises_prop : formula_prop list;
    proof_prop : proof_prop;
    conclusion_prop: formula_prop;
  }

and term_proof_prop  = 
  (*TODO | TPPAxiom   of string * formula_prop *)
  | TPPFormula of formula_prop
(*TODO  | TPPTheorem of formula_prop * (theorem_prop * (formula_prop list)(*parametres*) * (formula_prop list)(* premisses*))*)

and proof_prop = term_proof_prop list 

(*TODO
let term_proof_to_formula_prop  = function
  | TPPFormula f -> f
  | TPPAxiom (_,f) -> f
  | TPPTheorem(f,_) -> f
*)

(*SKE TODO : where to put this function ?*)
(*let rec apply_notations = function 
  | PVar _ as t -> t
  | PNeg f -> PNeg (apply_notations f)
  | PAnd(f1,f2) -> PAnd(apply_notations f1, apply_notations f2) 
  | POr(f1,f2) -> POr(apply_notations f1, apply_notations f2) 
  | PImpl(f1,f2) -> PImpl(apply_notations f1, apply_notations f2) 
*)
(*TODO
(* Equivalence of formulas, modulo notations*)
let rec equiv_notation f g =
  match f, g 
  with
  | PVar v1, PVar v2 -> v1=v2
  | PNeg f1 , PNeg g1 -> equiv_notation f1 g1
  | PAnd(f1, f2) , PAnd(g1, g2) 
  | POr(f1, f2) , POr(g1, g2) 
  | PImpl(f1, f2) , PImpl(g1, g2) ->  (equiv_notation f2 g2) && (equiv_notation f1 g1)
  | _ (*TODO apply notations*)-> false
*)
(**	@param l list of PVariables of g already instanciated in f *)
let instance f g =
  let rec instance_aux l f g  = match f, g 
    with
    | _, (PVar _ as g) -> begin
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
  | (TPPFormula f_i)::p ->  
    if (
          (*Formula is an hypothesis*)
             List.mem f_i hypotheses 
          (*Formula already present *)
          || List.mem f_i proved 
          (*Formula is an instance of a theorem or axiom *)
          || (List.exists (fun a -> instance f_i a.proposition_prop) 
                          (!theorems_prop @ !axioms_prop)) 
          (*cut*)
          || (cut f_i proved) 
          (*TODO || begin
            match proved with 
            | [] -> false 
            (*application of notations*)
            | f::_ -> equiv_notation f_i f
          end
          *)
      )
    then 
      verif ~hypotheses ~proved:(f_i :: proved) ~to_prove:p
    else 
      raise (Invalid_demonstration (f_i,List.rev (f_i::proved)))
(*TODO | TPPAxiom (name_ax, formula_ax) :: p -> 
   if List.mem {name_proposition_prop=name_ax; proposition_prop=formula_ax} !axioms_prop then 
      verif ~hypotheses ~proved:(formula_ax :: proved) ~to_prove:p
   else 
      raise (Invalid_demonstration (formula_ax,List.rev (formula_ax::proved)))
 | TPPTheorem  (f , (theorem, parameters, premises)) :: proof -> (f = theorem.conclusion_prop) && 
                                                                           (verif ~hypotheses ~proved:(f::proved) ~to_prove:proof) && 
                                                                           (List.for_all (fun p -> let premise = simultaneous_substitution_formula_prop theorem.parameters_prop parameters p
                                                                                           in
                                                                                           List.mem premise (List.map term_proof_to_formula_prop proof)
                                                                                         ) 
                                                                              premises)
*)

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

  if not(is_end_proof (TPPFormula f) proof)
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
  ~proof: (List.map (fun s -> TPPFormula (formula_from_string s)) [
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
  ~proof:(List.map (fun s -> TPPFormula (formula_from_string s)) [
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
