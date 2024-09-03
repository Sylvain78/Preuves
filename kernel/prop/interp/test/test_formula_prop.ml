open OUnit2
open Kernel.Logic
open Kernel_prop_interp.Formula
open Kernel_prop_interp.Instance_notation_printers
open Kernel_prop_interp.Theory.Prop

let print_result = function
  | Ok _ -> "Ok"
  | Error (m,e) -> m ^ ( match print_invalid_demonstration e with None -> "" | Some s -> s)

let notation = string_to_notation "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;
let () = 
  ignore (string_to_formula "(X_1=>X_2)=>((X_2=>X_3)=>(X_1=>X_3))");
  ignore ( string_to_formula "((\\lnot \\mathbf{A})=>((\\mathbf{A} \\lor \\mathbf{A})=>\\mathbf{A}))=>((((\\mathbf{A} \\lor \\mathbf{A})=>\\mathbf{A})=>((\\lnot \\mathbf{A})=>(\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))=>((\\lnot \\mathbf{A})=>((\\lnot \\mathbf{A})=>(\\lnot (\\mathbf{A} \\lor \\mathbf{A})))))")
;;

(* |- F \\implies F *)
let verif_tauto = 
  let demo_tauto=
    (List.map (fun s -> Single (string_to_formula s)) [
        "(X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)) \\implies 
 (( X_1 \\implies (X_1 \\implies X_1)) \\implies (X_1 \\implies X_1))";
        "X_1 \\implies ((X_1 \\implies X_1) \\implies X_1)";
        "(X_1 \\implies (X_1 \\implies X_1)) \\implies (X_1 \\implies X_1)";
        "X_1 \\implies (X_1 \\implies X_1)";
        "X_1 \\implies X_1"
      ])
  in
  let theorem_unproved = {kind=Kernel.Logic.KTheorem; name="tautologie" ; params=[]; premisses=[]; conclusion=(string_to_formula "X_1 \\implies X_1"); demonstration=demo_tauto}
  in
  match (verif ~keep_calls:Expand_calls theorem_unproved )
  with
  | Ok (Theorem theorem)->
    begin
      Theorems.add_theorem (Theorem {theorem with kind = KTheorem});
      true
    end
  | Error _ -> false
;;

(* |- (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)*)
let modus_ponens_unproved = 
  let modus_ponens = string_to_formula"((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  and modus_ponens_demo = (List.map (fun s -> Single(string_to_formula s)) [
      "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";
      "((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))"; 
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";
      (*k*)
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)))";
      (*s*)
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))) \\implies 
 (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
    ]) 
  in
  {kind = KUnproved;name="modus ponens";params=[];premisses=[];conclusion=modus_ponens;demonstration=modus_ponens_demo}
let verif_cut = verif ~keep_calls:Expand_calls modus_ponens_unproved

let add_chaining =
  let chaining =
    string_to_formula "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  and demo_chaining = 
    List.map (fun s -> Single(string_to_formula s)) [
      "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";
      "((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
      "((X_2 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))";
      "((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "(((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      (*k*)
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)))";

      (*s*)
      "((X_1 \\implies X_2) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies X_2)) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))) \\implies 
 (((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))))";

      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_2))) \\implies ((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))";
      "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
    ] 
  in
  let chaining_unproved =
    {
      kind = Kernel.Logic.KUnproved;
      name = "C6";
      params = [];
      premisses = [];
      demonstration = demo_chaining;
      conclusion = chaining;
    }
  in
  match (verif ~keep_calls:Expand_calls chaining_unproved ) 
  with
  | Ok (Theorem theorem) ->
    print_endline "C6 verified";
    Theorems.add_theorem (Theorem {theorem with kind = KTheorem})
  | Error _ -> ();;

(*non A \\implies non B \\implies B \\implies A*)
let contraposition = string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))"
and contraposition_demo = (List.map (fun s -> Single(string_to_formula s)) [
    "((\\lnot (\\lnot X_1)) \\implies X_1)";
    "((\\lnot (\\lnot X_1)) \\implies X_1) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_1)) \\implies X_1) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
    "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)";
    "(X_2 \\implies \\lnot (\\lnot X_2))";
    "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))";
    "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
    "((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies X_1) \\implies (X_2 \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_2)) \\implies X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))))";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
    "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";
  ]) 
let contraposition_unproved = {
  kind = KAssumed;
  name ="contraposition";
  params = [];
  premisses = [];
  demonstration = contraposition_demo;
  conclusion =contraposition;}
let verif_contraposee = verif ~keep_calls:Expand_calls contraposition_unproved
;;
match verif_contraposee 
with 
| Ok (Theorem theorem) -> 
  Theorems.add_theorem (Theorem {theorem with kind = KTheorem})
| Error _ -> ()
;;

(*|- A ou \\lnot A*)
let tiers_exclus = (string_to_formula "X_1 \\lor \\lnot X_1")
let tiers_exclus_demo = (List.map (fun s -> Single(string_to_formula s)) [

    "(X_1 \\implies X_1)";
    "(X_1 \\implies X_1) \\implies (\\lnot (\\lnot (X_1 \\implies X_1)))"; 
    "\\lnot (\\lnot (X_1 \\implies X_1))";(*OK*)

    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)

    "X_1 \\implies (X_1 \\lor \\lnot X_1)";
    "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\implies (X_1 \\lor \\lnot X_1)))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\implies ((X_1 \\lor \\lnot X_1)))";(*OK*)

    "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; 
    "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))))"; 
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; (*OK*)

    "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1)";
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1)";
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))";(*OK*)

    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))) \\implies (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))";
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)";(*OK*)

    "(\\lnot X_1) \\implies (X_1 \\lor \\lnot X_1)";
    "((\\lnot X_1) \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies (X_1 \\lor \\lnot X_1)))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor \\lnot X_1)))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor \\lnot X_1)))) \\implies (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1)))";
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1))";(*OK*)

    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))";(*OK*)

    "((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))";
    "(((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies 
 ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))))";

    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))) \\implies 
 (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";
    "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies 
 (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\implies X_1))))";
    "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\implies X_1))))";
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1))))";(*OK*)
    "(\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1)))";(*OK*)
    "(\\lnot(\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((X_1 \\lor \\lnot X_1))";(*OK*)
    "\\lnot(\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)
    "(X_1 \\lor \\lnot X_1)"
  ])
let tiers_exclus_unproved={kind=KUnproved;name="tiers exclus"; params=[];premisses=[];conclusion=tiers_exclus;demonstration=tiers_exclus_demo}
let verif_tiers_exclus =
  (*let z = X_1 \\lor \\lnot X_1
    and tout = \\lnot (X_1 \\implies X_1)
    in
  *)
  verif ~keep_calls:Expand_calls tiers_exclus_unproved 

(* |- (A \\implies C) \\implies (A \\implies (B \\implies C))*)
let rajout = (string_to_formula "(X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))")
and rajout_demo = (List.map (fun s -> Single(string_to_formula s)) [
    (*((S (K (S (K K)))) I)*) 
    "(X_1 \\implies X_3) \\implies (X_1 \\implies X_3)";(*i*)
    "X_3 \\implies (X_2 \\implies X_3)"; (*k*)
    "(X_3 \\implies (X_2 \\implies X_3)) \\implies (X_1 \\implies (X_3 \\implies (X_2 \\implies X_3)))"; 
    "(X_1 \\implies (X_3 \\implies (X_2 \\implies X_3)))"; (*k k*)
    "(X_1 \\implies (X_3 \\implies (X_2 \\implies X_3))) \\implies 
 ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))"; 
    "((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))"; (*s (k k)*)
    "((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))))";
    "((X_1 \\implies X_3) \\implies ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))))"; (*k (s (k k))*)
    "((X_1 \\implies X_3) \\implies ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))) \\implies 
 (((X_1 \\implies X_3) \\implies (X_1 \\implies X_3)) \\implies ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))))";
    "(((X_1 \\implies X_3) \\implies (X_1 \\implies X_3)) \\implies ((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))))";(*s (k (s (k k)))*)
    "((X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3)))"; (*(s (k (s (k k)))) i*)
  ])
let rajout_demo_unproved={kind=KUnproved;name="rajout"; params=[];premisses=[]; conclusion=rajout;demonstration=rajout_demo}
let verif_rajout_hypothese =
  (*TODO to delete when not needed anymore
    let 
    X_1,b,X_3=X_1,X_2,X_3
    in
    let (X_1 \\implies X_3) = (X_1 \\implies X_3)
    and (X_2 \\implies X_3) = (b \\implies X_3)*)
  verif ~keep_calls:Expand_calls rajout_demo_unproved

(* |- F ou F \\implies F *)
let ou_idempotent = (string_to_formula "(X_1 \\lor X_1) \\implies X_1")
and ou_idempotent_demo = (List.map (fun s -> Single(string_to_formula s)) [
    "((X_1 \\lor X_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))";
    "((\\lnot X_1) \\implies ((X_1 \\lor X_1) \\implies X_1))";
    "((\\lnot X_1) \\implies ((X_1 \\lor X_1) \\implies X_1)) \\implies ((((X_1 \\lorX_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))))";
    "((((X_1 \\lorX_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1)))";
    "((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies (((\\lnot X_1) \\implies (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies (\\lnot X_1))";
    "(((\\lnot X_1) \\implies (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1)))";
    "((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))) \\implies ((X_1\\lorX_1) \\implies X_1)";
    "(X_1\\lor X_1) \\implies X_1";
  ])
let ou_idempotent_unproved = {kind=KUnproved;name="ou idempotent";params=[];premisses=[];conclusion=ou_idempotent;demonstration=ou_idempotent_demo}
let verif_ou_idempotent = verif ~keep_calls:Expand_calls ou_idempotent_unproved

(* |- (A ou B) \\implies (A \\implies C) \\implies (B \\implies C) \\implies C*)
let ou_diamant = (string_to_formula "(X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))")
and ou_diamant_demo = 
  let neg p = PNeg p
  and (=>.) a b = PImpl(a,b)
  and (||.) a b = POr(a,b)
  (*let notation = string_to_notation "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;*)
  and x1,x2,x3 = PVar 1, PVar 2, PVar 3
  in 
  let a,b,c=x1,x2,x3
  in 
  let tout = neg (a=>.a)
  and a_ou_b = (a||.b)
  and a_entraine_c = (a=>.c)
  and b_entraine_c = (b=>.c)
  in 
  let diamond = (a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c)))
  in 
  let taut x =
    [
      (x =>. ((x =>. x) =>. x)) =>. ((x =>. (x =>. x)) =>. (x =>. x));
      x =>. ((x =>. x) =>. x);
      (x =>. (x =>. x)) =>. (x =>. x);
      x =>. (x =>. x);
      x =>. x;
    ]
  and cut x1 x2 x3 =
    [
      (x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3));
      ((x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3))) =>. ((x2 =>. x3) =>. ((x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3))));
      ((x2 =>. x3) =>. ((x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3))));
      ((x2 =>. x3) =>. ((x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3)))) =>. (((x2 =>. x3) =>. (x1 =>. (x2 =>. x3))) =>. ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3))));
      (((x2 =>. x3) =>. (x1 =>. (x2 =>. x3))) =>. ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3))));
      ((x2 =>. x3) =>. (x1 =>. (x2 =>. x3)));
      ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3)));
      ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3))) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))) =>. ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)))); 
      ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2)));
      ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)))) =>. (((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2))) =>. ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3))));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2))) =>. ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
    ] 
  in
  let neg_contraposition x1 x2 =
    [
      (*138*) ((neg (neg x1)) =>.x1);
      ((neg (neg x1)) =>.x1) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x1)) =>.x1));
      ((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x1)) =>.x1);
      (*155*) ]@ (cut (neg (neg x2)) (neg (neg x1)) x1) @[
      ((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x1)) =>.x1) =>.((neg (neg x2)) =>.x1));
      (((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x1)) =>.x1) =>.((neg (neg x2)) =>.x1))) =>.((((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x1)) =>.x1)) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x2)) =>.x1)));
      ((((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x1)) =>.x1)) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x2)) =>.x1)));
      ((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x2)) =>.x1);
      (*160*) (x2 =>.neg (neg x2));
      (x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.neg (neg x2)));
      ((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.neg (neg x2));
      (*163*)]@cut x2 (neg (neg x2)) x1@[
      (x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1));
      (*165*) ((x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1))) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.((x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1))));
      (((neg (neg x2)) =>.(neg (neg x1))) =>.((x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1))));
      (((neg (neg x2)) =>.(neg (neg x1))) =>.((x2 =>.neg (neg x2)) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1)))) =>.((((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.neg (neg x2))) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1))));
      (((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.neg (neg x2))) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1)));
      ((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1));
      (*170*) (((neg (neg x2)) =>.(neg (neg x1))) =>.(((neg (neg x2)) =>.x1) =>.(x2 =>.x1))) =>.((((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x2)) =>.x1)) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.x1)));
      (((neg (neg x2)) =>.(neg (neg x1))) =>.((neg (neg x2)) =>.x1)) =>.(((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.x1));
      ((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.x1);
      (*187*) (((neg x1) =>.(neg x2)) =>.((neg (neg x2)) =>.(neg (neg x1))));
      (*188*)] @ 
    (cut ((neg x1) =>.(neg x2)) ((neg (neg x2)) =>.(neg (neg x1))) (x2=>.x1))
    @ [
      (((neg x1) =>.(neg x2)) =>.((neg (neg x2)) =>.(neg (neg x1)))) =>.((((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.x1)) =>.(((neg x1) =>.(neg x2)) =>.(x2 =>.x1)));
      ((((neg (neg x2)) =>.(neg (neg x1))) =>.(x2 =>.x1)) =>.(((neg x1) =>.(neg x2)) =>.(x2 =>.x1)));
      (((neg x1) =>.(neg x2)) =>.(x2 =>.x1));
    ]
  in 
  List.map (fun f -> Single f) (
    (*05*) 
    (taut a) @ [
      (a =>. a) =>. (neg tout);
      (*neg tout*)
      (neg tout);
      (neg tout)=>.(b_entraine_c=>. neg tout);
      (b_entraine_c=>. neg tout);
      (*10*) (b_entraine_c=>. neg tout)=>.(a_entraine_c=>.(b_entraine_c=>. neg tout));
      (a_entraine_c=>.(b_entraine_c=>. neg tout));
      (a_entraine_c=>.(b_entraine_c=>. neg tout))=>. (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));
      (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));

      (*a_ou_b;*)
      (*a_ou_b=>.((neg c)=>.a_ou_b);*)
      a_ou_b=>.((neg c)=>.a_ou_b);

      (*((neg c)=>.a_ou_b);*)
      (*15*) ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b));

      (((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))=>. 
      (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

      (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
      ((a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))))=>.
      ((a_ou_b =>. ((neg c) =>. a_ou_b))=>. (a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

      (a_ou_b=>.((neg c)=>.a_ou_b))=>. (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

      (*20*) (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

      ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
      ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))) =>. (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))))) =>. ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (*25*) ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));

      (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.a_ou_b))));

      (*a_entraine_c;*)
      (*27*) a_entraine_c=>.((neg c)=>.a_entraine_c);
      (*((neg c)=>.a_entraine_c);*)
      (*32*) ] @ (taut (neg c)) @ [
      ((neg c)=>.(neg c))=>.(a_entraine_c=>.((neg c)=>.(neg c)));
      (a_entraine_c=>.((neg c)=>.(neg c)));
      (*35*) ((a_entraine_c)=>.((neg c)=>.(neg a)));
      ((a_entraine_c)=>.((neg c)=>.(neg a)))=>.((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
      ((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
      ((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))))=>.
      (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
      (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
      (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))))=>.
      (*40*) (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
      (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
      (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))))=>.
      ((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
      ((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
      a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)));
      (*45*) ((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));

      (((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
      (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
      (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
      (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))))=>.
      ((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
      ((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
      (*50*) a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));
      (a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
      ((a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a))));
      (a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a)));
      (*((neg c)=>.(neg a));*)
      a_entraine_c=>.((neg c)=>.(neg a));
      ((neg a)=>.(a_ou_b=>.(b)));
      (*((neg a)=>.(a_ou_b=>.(b)))=>. ((neg c)=>. ((neg a)=>.(a_ou_b=>.(b))));*)
      (*55*) ((neg a)=>.(a_ou_b=>.(b)))=>. ((neg c)=>. ((neg a)=>.(a_ou_b=>.(b))));
      (*((neg c)=>.((neg a)=>.(a_ou_b=>.(b))));*)
      ((neg c)=>.((neg a)=>.(a_ou_b=>.(b))));
      (*((neg c)=>.((neg a)=>.(a_ou_b=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));*)
      ((neg c)=>.((neg a)=>.(a_ou_b=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));
      (*(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));*)
      ((((neg c)=>.(neg a))=>.((neg c)=>.((a_ou_b)=>.(b)))));
      ((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.
      (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))));
      (*60*) (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))));
      (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.
      ((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))));
      ((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))));
      (a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))));

      (((neg c)=>.(a_ou_b=>.b)))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))));
      ((((neg c)=>.(a_ou_b=>.b)))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.
      (*65*) (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));
      (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))); (*k k*)
      (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))=>.
      ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));

      ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))); (*s (k k)*)
      ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));
      (*70*) ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));(*k (s (k k))*)
      ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))))=>.
      (((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));
      (((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))); (*(s (k (s (k k))))*)
      (*77*) ] @ (taut ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))) (*i*)@ [

      ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));(*((s (k (s (k k)))) i)*)

      (*((neg c)=>.(a_ou_b=>.(b)));*)

      a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))));
      (*((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)
      (*80*) ((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));
      (((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))=>.
      (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
      (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
      (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
      ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
      ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
      ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
      (*85*) (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
      (*(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)

      a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))));
      (b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
      (*90*) ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))));


      ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
       ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))) =>. 
      (*91*)(a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

      (*92*) a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
      (a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>. ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))) =>. ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
      (*95*) (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))=>. ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))) ;
      ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
                                                                                       ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))) ;

      (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
        (*100*) ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));

      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (*105*) (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
      (*((neg c)=>.(b));*)
      (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))));
      (*((neg c)=>.(b))=>.(b_entraine_c=>.((neg c)=>.(b)));
        (b_entraine_c=>.((neg c)=>.(b)));
        (b_entraine_c=>.((neg c)=>.(b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))));

        a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)));*)
      (*b_entraine_c;*)
      b_entraine_c=>.((neg c)=>. b_entraine_c);
      (b_entraine_c=>.((neg c)=>. b_entraine_c))=>.
      (*110*) (a_entraine_c=>.(b_entraine_c=>.((neg c)=>. b_entraine_c)));
      (*((neg c)=>.(b_entraine_c));*)
      a_entraine_c=>.(b_entraine_c=>.((neg c)=>. b_entraine_c));

      (*((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c));*)
      (((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c)));
      (((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.(b_entraine_c=>.(((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c))));
      b_entraine_c=>. (((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c)));
      (b_entraine_c=>. (((neg c)=>.(b_entraine_c))=>.(((neg c)=>.b)=>.((neg c)=>.c))))=>.
      ((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))));
      ((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))));
      ((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))))=>.
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))));


      a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))));

      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(b_entraine_c)))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b_entraine_c))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))));
      (*120*) ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b_entraine_c))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))));
      (*(((neg c)=>.b)=>.((neg c)=>.c));*)
      (*(((neg c)=>.b)=>.((neg c)=>.c));
        (((neg c)=>.b)=>.((neg c)=>.c))=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)));*)
      a_entraine_c=>.((b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))));
      (b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.
      ((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)));

      ((b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.
       ((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c))))=>.
      (a_entraine_c=>.((b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.
                       ((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)))));

      (a_entraine_c=>.((b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.
                       ((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)))));

      (a_entraine_c=>.((b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))=>.((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)))));
      ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)))));


      a_entraine_c=>.((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c)));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.b))=>.(b_entraine_c=>.((neg c)=>.c))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c))));
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c))));

      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c))))=>.
      (*130*) (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));

      (*((neg c)=>.(c));*)
      (*((neg c)=>.(c));
        ((neg c)=>.(c))=>.(b_entraine_c=>.((neg c)=>.(c)));*)
      a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(c))));
      (*((neg c)=>.((neg tout)=>.(neg c)));*)
      (*135*) ((neg c)=>.((neg tout)=>.(neg c)));
      ((neg c)=>.((neg tout)=>.(neg c)))=>.(b_entraine_c=>.((neg c)=>.((neg tout)=>.(neg c))));
      (b_entraine_c=>.((neg c)=>.((neg tout)=>.(neg c))));
      (*(((neg tout)=>.(neg c))=>.((c)=>.(tout)));*)

    ]@ neg_contraposition (tout) (c) @ [
      (((neg tout)=>.(neg c))=>.((c)=>.(tout)));
      (((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>.(b_entraine_c=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))));
      (b_entraine_c=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))));
      (*(((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>. ((neg c) =>. (((neg tout)=>.(neg c))=>.((c)=>.(tout))));*)
      ((((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>. ((neg c) =>. (((neg tout)=>.(neg c))=>.((c)=>.(tout)))));
      ((((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>. ((neg c) =>. (((neg tout)=>.(neg c))=>.((c)=>.(tout)))))=>.(b_entraine_c=>.((((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>. ((neg c) =>. (((neg tout)=>.(neg c))=>.((c)=>.(tout))))));
      (b_entraine_c=>.((((neg tout)=>.(neg c))=>.((c)=>.(tout)))=>. ((neg c) =>. (((neg tout)=>.(neg c))=>.((c)=>.(tout))))));
      (*((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))));*)
      ((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))));
      ((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>.(b_entraine_c=>.((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout)))));
      (b_entraine_c=>.((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout)))));
      (*((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>. (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)));*)
      (((neg c)=>.(((neg tout)=>.(neg c)) =>. ((c)=>.(tout))))=>. 
       (((neg c)=>.((neg tout)=>.(neg c))) =>. ((neg c)=>.(c=>.tout))));

      (((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))
       =>. 
       (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)))
      )
      =>.
      (b_entraine_c=>.(((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))
                       =>. 
                       (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)))
                      )
      );
      (b_entraine_c=>.(((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>. (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)))));
      (*(((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)));*)
      (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)));
      (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)))=>.(b_entraine_c=>.(((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout))));
      (b_entraine_c=>.(((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout))));
      (*((neg c)=>.((c)=>.(tout)));*)
      ((neg c)=>.((c)=>.(tout)));
      ((neg c)=>.((c)=>.(tout)))=>.(b_entraine_c=>.((neg c)=>.((c)=>.(tout))));
      (b_entraine_c=>.((neg c)=>.((c)=>.(tout))));
      (*((neg c)=>.(c=>.tout))=>.(((neg c)=>.c)=>. ((neg c)=>.tout));*)
      ((neg c)=>.(c=>.tout))=>.(((neg c)=>.c)=>. ((neg c)=>.tout));
      (((neg c)=>.(c=>.tout))=>.(((neg c)=>.c)=>. ((neg c)=>.tout)))=>.(b_entraine_c=>.(((neg c)=>.(c=>.tout))=>.(((neg c)=>.c)=>. ((neg c)=>.tout))));
      b_entraine_c=>.(((neg c)=>.(c=>.tout))=>.(((neg c)=>.c)=>. ((neg c)=>.tout)));
      (*((neg c)=>.c)=>. ((neg c)=>.tout);*)
      (((neg c)=>.c)=>. ((neg c)=>.tout));
      (((neg c)=>.c)=>. ((neg c)=>.tout))=>.(b_entraine_c=>.(((neg c)=>.c)=>. ((neg c)=>.tout)));
      (b_entraine_c=>.(((neg c)=>.c)=>. ((neg c)=>.tout)));
      (b_entraine_c=>.(((neg c)=>.c)=>. ((neg c)=>.tout)))=>.
      ((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout)));
      ((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout)));
      ((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout)))=>.
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout))));
      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout))));

      (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.c))=>.(b_entraine_c=>.((neg c)=>.tout))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout))));
      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout))));

      ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout))))=>.
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout)))));


      a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout))));

      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout)))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout)))));
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.tout)))));
      (*((neg c)=>.(tout));*)
      (*((neg c)=>.(tout));
        ((neg c)=>.(tout))=>.(b_entraine_c=>.((neg (c))=>.(tout)));*)



      a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))));
      (*(((neg c)=>.(tout))=>.((neg tout)=>.(neg(neg c))));*)
      ((neg (c))=>.(tout))=>.((neg tout)=>.(neg(neg (c))));
      (((neg (c))=>.(tout))=>.((neg tout)=>.(neg(neg (c)))))=>.(b_entraine_c=>.(((neg (c))=>.(tout))=>.((neg tout)=>.(neg(neg (c))))));
      (b_entraine_c=>.(((neg (c))=>.(tout))=>.((neg tout)=>.(neg(neg (c))))));
      (b_entraine_c=>.(((neg (c))=>.(tout))=>.((neg tout)=>.(neg(neg (c))))))=>.
      ((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))));
      ((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))));
      ((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
      (a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))));

      (a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))));
      (a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.
      (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))));
      (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))));

      (a_entraine_c =>. ((b_entraine_c=>.((neg (c))=>.(tout))) =>. (b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.
      ((a_entraine_c =>. (b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))));
    ]@(cut 
         a_ou_b 
         (a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))
         ((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))
      )@[
      (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))
      =>.
      (((a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.
        ((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))
       =>.(a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))));

      (((a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))=>.(a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))));

      a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))));

      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))));
      (*((neg tout)=>.(neg(neg c)));*)
      (*((neg tout)=>.(neg(neg c)));
        ((neg tout)=>.(neg(neg c)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))));*)
      a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))));
      (b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))=>.
      ((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))));

      ((b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))=>.
       ((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))=>.
      (a_entraine_c=>.((b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))=>.
                       ((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))));
      (a_entraine_c=>.((b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))=>.
                       ((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))));

      (a_entraine_c=>.((b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.(a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))));

      ((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
       (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))));
      ((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
       (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))))=>.
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
                 (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))));

      a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
                (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))));

      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))=>.
                 (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.(a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))));

      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.
       (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))));

      a_ou_b=>.
      (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))));
      (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))=>.
      ((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))));
    ] @ (cut
           a_ou_b
           (a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))
           ((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))))
        ) 
    @ [

      (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))))
      =>.(((a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))=>.
           ((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))))
          =>.
          (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))))));	 
      (((a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))))=>.(a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))))));
      a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))));


      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg tout))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))));
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg tout))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))));
      (*(neg(neg c));*)
      (*(neg(neg c));
        (neg(neg c))=>.(b_entraine_c=>.(neg(neg (c))));*)
      a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))));
      (*((neg(neg c))=>.(c));*)
      ((neg(neg c))=>.(c));
      ((neg(neg c))=>.(c))=>.(b_entraine_c=>.((neg(neg c))=>.(c)));
      (b_entraine_c=>.((neg(neg c))=>.(c)));

      (b_entraine_c=>.((neg(neg c))=>.(c)))=>.
      ((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c));

      ((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c));

      ((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c))=>.
      (a_entraine_c=>.((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c)));

      (a_entraine_c=>.((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c)));
      (a_entraine_c=>.((b_entraine_c=>.(neg(neg c)))=>.(b_entraine_c=>.c)))=>.
      ((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c)));
      ((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c)));
      ((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c)))=>.
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c))));
      (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg(neg c))))=>.(a_entraine_c=>.(b_entraine_c=>.c))))=>.
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg c)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.c))));
      ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg c)))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.c))));
      (*(c)*)
      (*c;
        c=>.(b_entraine_c=>.c);*)
      (*a_entraine_c=>.(b_entraine_c=>.c);
        (a_entraine_c=>.(b_entraine_c=>.c))=>. (a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c)));*)

      diamond;
    ])
let ou_diamant_unproved = {kind=KUnproved;name="ou diamant";params=[];premisses=[];conclusion=ou_diamant;demonstration=ou_diamant_demo}
let verif_ou_diamant = verif ~keep_calls:Expand_calls ou_diamant_unproved

let test_tauto _ = assert_bool "tauto" (verif_tauto)
let test_cut _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal ~msg:"cut" ~printer:formula_to_string
    (string_to_formula "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))")
    (match verif_cut with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion
let test_contraposee _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal ~msg:"contraposee" ~printer:formula_to_string
    contraposition
    (match verif_contraposee with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion
let test_tiers_exclus _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal~msg:"tiers exclus" ~printer:formula_to_string
    tiers_exclus
    (match verif_tiers_exclus with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion
let test_rajout_hypothese _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal ~msg:"rajout hypothese" ~printer:formula_to_string
    rajout 
    (match verif_rajout_hypothese with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion
let test_ou_idempotent _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal ~msg:"ou idempotent" ~printer:formula_to_string
    ou_idempotent
    (match verif_ou_idempotent with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion
let test_ou_diamant _ = 
  print_string "number of theorems : ";print_int (Theorems.get_theorems() |> List.length);print_newline();
  assert_equal ~printer:formula_to_string ~msg:"ou diamant" 
    ou_diamant
    (match verif_ou_diamant with Ok (Theorem theorem) -> theorem | Error (_,e) -> raise e).conclusion

let test_instance_1 _ = 
  assert_equal [(PVar 1, PVar 1); (PVar 2, PVar 2)] (instance (string_to_formula "X_1 \\land X_2") (string_to_formula "X_1 \\land X_2"))
let test_instance_2 _ = 
  assert_equal [(PVar 3,
                                       PApply_notation
                                         {apply_notation_prop =
                                            {notation_prop_name = "imply";
                                             notation_prop_params = [Param "a"; Param "b"];
                                             notation_prop_notation = [Param "a"; String "=>"; Param "b"];
                                             notation_prop_semantique =
                                               [String "("; Param "a"; String ")"; String "\\implies"; String "(";
                                                Param "b"; String ")"]};
                                          apply_notation_prop_params =
                                            [PNeg (PMetaVar "A"); PNeg (POr (PMetaVar "A", PMetaVar "A"))]});
                                      (PVar 2,
                                       PApply_notation
                                         {apply_notation_prop =
                                            {notation_prop_name = "imply";
                                             notation_prop_params = [Param "a"; Param "b"];
                                             notation_prop_notation = [Param "a"; String "=>"; Param "b"];
                                             notation_prop_semantique =
                                               [String "("; Param "a"; String ")"; String "\\implies"; String "(";
                                                Param "b"; String ")"]};
                                          apply_notation_prop_params =
                                            [POr (PMetaVar "A", PMetaVar "A"); PMetaVar "A"]});
                                      (PVar 1, PNeg (PMetaVar "A"))] (
    instance 
      (string_to_formula "((\\lnot \\mathbf{A})=>((\\mathbf{A} \\lor \\mathbf{A})=>\\mathbf{A}))=>((((\\mathbf{A} \\lor \\mathbf{A})=>\\mathbf{A})=>((\\lnot \\mathbf{A})=>(\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))=>((\\lnot \\mathbf{A})=>((\\lnot \\mathbf{A})=>(\\lnot (\\mathbf{A} \\lor \\mathbf{A})))))")
      (string_to_formula "(X_1=>X_2)=>((X_2=>X_3)=>(X_1=>X_3))"))

(** Tests for to_string *)
let test_to_string_formula_pvar _ =
  let s = to_string_formula_prop (PVar 1)
  in assert_equal s "X_1"

let test_to_string_formula_pvar_11 _ =
  let s = to_string_formula_prop (PVar 11)
  in assert_equal s "X_{11}"

let test_to_string_formula_pvar_metavar _ =
  let s = to_string_formula_prop (PMetaVar "A")
  in assert_equal "\\mathbf{A}" s

let test_to_string_formula_pneg _ =
  let s = to_string_formula_prop (string_to_formula "\\lnot X_1")
  in assert_equal s "\\lnot X_1"

let test_to_string_formula_pneg_notation _ =
  let _ = string_to_notation "Notation\nimply\nParam\na b\nSyntax\na \" => \" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd"
  in 
  let s = to_string_formula_prop (string_to_formula "\\lnot \\lnot (\\mathbf{A} => \\mathbf{A})")
  in assert_equal ~printer:(fun s -> s) "\\lnot \\lnot (\\mathbf{A} => \\mathbf{A})" s

let test_to_string_formula_pand _ =
  let s = to_string_formula_prop (string_to_formula "X_1 \\land X_2")
  in assert_equal s "X_1 \\land X_2"

let test_to_string_formula_pand_par _ =
  let s = to_string_formula_prop (string_to_formula "X_1 \\land (X_2 \\land X_3)")
  in assert_equal s "X_1 \\land X_2 \\land X_3"

let test_to_string_formula_por _ = 
  let s = to_string_formula_prop (string_to_formula "X_1 \\lor X_2")
  in assert_equal s "X_1 \\lor X_2"

let test_to_string_formula_por_par _ = 
  let s = to_string_formula_prop (string_to_formula "X_1 \\lor (X_2 \\lor X_3)")
  in assert_equal s "X_1 \\lor X_2 \\lor X_3"

let test_to_string_formula_pand_por _ = 
  let s = to_string_formula_prop (string_to_formula "(X_1 \\land X_2) \\lor X_3")
  in assert_equal s "(X_1 \\land X_2) \\lor X_3"

let test_to_string_formula_por_pand _ = 
  let s = to_string_formula_prop (string_to_formula "(X_1 \\lor X_2) \\land X_3")
  in assert_equal s "(X_1 \\lor X_2) \\land X_3"

let test_to_string_formula_impl _ = 
  let s = to_string_formula_prop (string_to_formula "X_1 \\implies X_2")
  in assert_equal s "X_1 \\implies X_2"

let test_to_string_formula_not_impl _ = 
  let s = to_string_formula_prop (string_to_formula "(\\lnot X_1) \\implies (\\lnot X_2)")
  in 
  assert_equal ~printer:(fun s -> s) "(\\lnot X_1) \\implies \\lnot X_2" s

let test_to_string_formula_and_impl _ = 
  let s = to_string_formula_prop (string_to_formula "X_3 \\land (X_1 \\implies X_2)")
  in assert_equal s "X_3 \\land (X_1 \\implies X_2)"

let test_to_string_formula_notation _ =
  let s = to_string_formula_prop (string_to_formula "X_1 \\implies X_2")
  in assert_equal ~printer:(fun s -> s) "X_1 \\implies X_2" (*TODO \\implies --> =>*) s

(* Tests for printer_formula *)
let test_printer_formula_pvar _ = printer_formula_prop Format.str_formatter (PVar 1);
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1"

let test_printer_formula_pmetavar _ = printer_formula_prop Format.str_formatter (PMetaVar "A");
  let s = Format.flush_str_formatter()
  in assert_equal s "\\mathbf{A}"

let test_printer_formula_pvar_11 _ = printer_formula_prop Format.str_formatter (PVar 11);
  let s = Format.flush_str_formatter()
  in assert_equal s "X_{11}"

let test_printer_formula_pneg _ = printer_formula_prop Format.str_formatter (string_to_formula "\\lnot X_1");
  let s = Format.flush_str_formatter()
  in assert_equal ~printer:(fun s -> s) s "\\lnot X_1"

let test_printer_formula_pand _ = printer_formula_prop Format.str_formatter (string_to_formula "X_1 \\land X_2");
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1 \\land X_2"

let test_printer_formula_pand_par _ = printer_formula_prop Format.str_formatter (string_to_formula "X_1 \\land (X_2 \\land X_3)");
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1 \\land X_2 \\land X_3"

let test_printer_formula_por _ = printer_formula_prop Format.str_formatter (string_to_formula "X_1 \\lor X_2");
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1 \\lor X_2"

let test_printer_formula_por_par _ = printer_formula_prop Format.str_formatter (string_to_formula "X_1 \\lor (X_2 \\lor X_3)");
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1 \\lor X_2 \\lor X_3"

let test_printer_formula_pand_por _ = printer_formula_prop Format.str_formatter (string_to_formula "(X_1 \\land X_2) \\lor X_3");
  let s = Format.flush_str_formatter()
  in assert_equal s "(X_1 \\land X_2) \\lor X_3"

let test_printer_formula_por_pand _ = printer_formula_prop Format.str_formatter (string_to_formula "(X_1 \\lor X_2) \\land X_3");
  let s = Format.flush_str_formatter()
  in assert_equal s "(X_1 \\lor X_2) \\land X_3"

let test_printer_formula_impl _ = printer_formula_prop Format.str_formatter (string_to_formula "X_1 \\implies X_2");
  let s = Format.flush_str_formatter()
  in assert_equal s "X_1 \\implies X_2"

let test_printer_formula_impl_par _ = printer_formula_prop Format.str_formatter (string_to_formula "(X_1 \\implies X_2) \\implies X_3");
  let s = Format.flush_str_formatter()
  in assert_equal s "(X_1 \\implies X_2) \\implies X_3" ~printer:(fun s -> s)

let test_printer_formula_and_impl _ = printer_formula_prop Format.str_formatter (string_to_formula "X_3 \\land (X_1 \\implies X_2)");
  let s = Format.flush_str_formatter()
  in assert_equal "X_3 \\land (X_1 \\implies X_2)" s ~printer:(fun s -> s)

let test_printer_formula_pappl_fail _ = 
  let n = string_to_notation "Notation\ntest\nParam\n a\nSyntax\nc\nSemantics\n\"X_1\"\nEnd"
  in
  try
    printer_formula_prop Format.str_formatter 
      (PApply_notation {apply_notation_prop=n ; apply_notation_prop_params = [PVar 2]})
  with 
  | Failure _ -> assert_bool "" true;;

let test_notation _ =
  try
    let notation = string_to_notation "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd"
    in
    ignore notation
  with _ -> assert_failure "test_notation"

let instance_suite =
  "Instance">:::
  [ "test_instance_1">::test_instance_1; 
    "test_instance_2">::test_instance_2; ]


let printer_formula_suite =
  "printer_formula" >:::
  [ "test printer_formula PVar">:: test_printer_formula_pvar;
    "test printer_formula PMetaVar">:: test_printer_formula_pmetavar;
    "test printer_formula PVar X_{11}">:: test_printer_formula_pvar_11;
    "test printer_formula PNeg">:: test_printer_formula_pneg;
    "test printer_formula PAnd">:: test_printer_formula_pand;
    "test printer_formula PAnd par">:: test_printer_formula_pand_par;
    "test printer_formula POr">:: test_printer_formula_por;
    "test printer_formula POr par">:: test_printer_formula_por_par;
    "test_printer_formula_pand_por">:: test_printer_formula_pand_por;
    "test_printer_formula_por_pand">::test_printer_formula_por_pand;
    "test_printer_formula_impl">::test_printer_formula_impl;
    "test_printer_formula_impl_par">::test_printer_formula_impl_par;
    "test_printer_formula_and_impl">::test_printer_formula_and_impl;
    (*"test_printer_formula_PAppl_fail">::test_printer_formula_pappl_fail;*)
  ]

let to_string_formula_suite =
  "to_string_formula" >:::
  [ 
    "test_to_string_formula_not_impl">::test_to_string_formula_not_impl;
    "test to_string_formula PVar">:: test_to_string_formula_pvar;
    "test to_string_formula PVar X_{11}">:: test_to_string_formula_pvar_11;
    "test to_string_formula PMetaVar ">:: test_to_string_formula_pvar_metavar;
    "test to_string_formula PNeg">:: test_to_string_formula_pneg;
    "test to_string_formula PNeg Notation ">:: test_to_string_formula_pneg_notation;
    "test to_string_formula PAnd">:: test_to_string_formula_pand;
    "test to_string_formula PAnd par">:: test_to_string_formula_pand_par;
    "test to_string_formula POr">:: test_to_string_formula_por;
    "test to_string_formula POr par">:: test_to_string_formula_por_par;
    "test_to_string_formula_pand_por">:: test_to_string_formula_pand_por;
    "test_to_string_formula_por_pand">::test_to_string_formula_por_pand;
    "test_to_string_formula_impl">::test_to_string_formula_impl;
    "test_to_string_formula_and_impl">::test_to_string_formula_and_impl;
    "test_to_string_formula_notation">::test_to_string_formula_notation;
  ]


let prop_suite =
  "Prop">:::
  [ "test_tauto" >:: test_tauto ;
    "test_cut" >:: test_cut ; 
    "test_contraposee" >:: test_contraposee ; 
    "test_tiers_exclus" >:: test_tiers_exclus ; 
    "test_rajout_hypothese" >:: test_rajout_hypothese ; 
    "test_ou_idempotent" >:: test_ou_idempotent ; 
    "test_ou_diamant" >:: test_ou_diamant ;
  ] 
;;

let notation_suite =
  "Notation">:::
  [ "test_notation" >:: test_notation
  ]
;;

let () =
  run_test_tt_main instance_suite;
  run_test_tt_main printer_formula_suite;
  run_test_tt_main to_string_formula_suite;
  run_test_tt_main prop_suite;
  run_test_tt_main notation_suite;

