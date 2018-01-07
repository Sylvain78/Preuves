open OUnit2
open Formula_prop
open Axioms_prop
open Proof_prop
open Prop_parser

let () = print_string "before\n";;
let n1 = notation_from_string "Notation imply \n Param  a b\nSyntax a \"=>\" \nSemantics ";;
let n2 = notation_from_string "Notation imply \n Param  a b\nSyntax \"=>\" \nSemantics ";;
let n3 = notation_from_string "Notation imply \n Param  a b\nSyntax a  \nSemantics ";;
let () = print_string "after\n";;


(* |- F \\implies F *)
let verif_tauto = proof_verification ~hyp:[] ( print_string "verif_tauto\n";let f = formula_from_string "X_1 =>  X_1" in print_string "verif_tauto (after parse)"; f) 
~proof:(List.map formula_from_string [
    "(X_1 \\implies ((X_1 \\implies X_1) \\implies X_1))  \\implies 
    (( X_1 \\implies (X_1 \\implies X_1)) \\implies (X_1 \\implies X_1))";
    "X_1 \\implies((X_1 \\implies X_1) \\implies X_1)";
    "(X_1 \\implies (X_1 \\implies X_1)) \\implies (X_1 \\implies X_1)";
    "X_1 \\implies(X_1 \\implies X_1)";
    "X_1 \\implies X_1"
]);;

(* |- (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)*)
let verif_cut = proof_verification ~hyp:[] (formula_from_string "(X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3))")
~proof: (List.map formula_from_string [
    "(X_1 \\implies(X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";
    "((X_1 \\implies(X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies(X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
    "((X_2 \\implies X_3) \\implies ((X_1 \\implies(X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
    "((X_2 \\implies X_3) \\implies ((X_1 \\implies(X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3)))) \\implies (((X_2 \\implies X_3) \\implies (X_1 \\implies(X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
    "(((X_2 \\implies X_3) \\implies (X_1 \\implies(X_2 \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))))";
    "((X_2 \\implies X_3) \\implies  (X_1 \\implies(X_2 \\implies X_3)))";
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

(*non A \\implies non B |- B \\implies A*)
let verif_contraposee = 
        (*TODO delete when not needed anymore
        let h = ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))    
        and (X_1 \\lor X_2) =((\\lnot (\\lnot X_1)) \\implies  X_1)
        and i = ((\\lnot (\\lnot X_2)) \\implies  X_1)    
        and a2=    (X_2 \\implies \\lnot (\\lnot X_2))
        in
        *)
proof_verification ~hyp:[] (formula_from_string "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))")
~proof:(List.map formula_from_string [
    "((\\lnot (\\lnot X_1)) \\implies  X_1)";
    "((\\lnot (\\lnot X_1)) \\implies  X_1) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies  X_1))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies  X_1)";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_1)) \\implies  X_1) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_1)) \\implies  X_1) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies  X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1)))";
    "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((\\lnot (\\lnot X_1)) \\implies  X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1)";
    "(X_2 \\implies \\lnot (\\lnot X_2))";
    "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))";
    "(X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))";
    "((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))) \\implies  (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies ((X_2 \\implies \\lnot (\\lnot X_2)) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies \\lnot (\\lnot X_2))) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1)))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (((\\lnot (\\lnot X_2)) \\implies  X_1) \\implies (X_2 \\implies X_1))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)))";
    "(((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies((\\lnot (\\lnot X_2)) \\implies  X_1)) \\implies (((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1))";
    "((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))))";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies  ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))) \\implies ((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
    "((((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1))) \\implies (X_2 \\implies X_1)) \\implies (((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1)))";
    "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";
]);;

(*|- A ou \\lnot A*)
let verif_tiers_exclus =
(*let z = X_1 \\lor \\lnot X_1
and tout = \\lnot (X_1 \\implies X_1)
in
*)
proof_verification ~hyp:[] (formula_from_string "X_1 \\lor \\lnot X_1")
~proof:(List.map formula_from_string [
    
    "(X_1 \\implies X_1)";(**)
    "(X_1 \\implies X_1) \\implies (\\lnot (\\lnot (X_1 \\implies X_1)))"; (**)
    "\\lnot (\\lnot (X_1 \\implies X_1))";(*OK*)
     
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)
    
    "X_1 \\implies (X_1 \\lor \\lnot X_1)";(**)
    "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\implies (X_1 \\lor \\lnot X_1)))";(**)
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\implies((X_1 \\lor \\lnot X_1)))";(*OK*)
    
    "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; (**)
    "((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1))))"; (**)
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot X_1)))"; (*OK*)
    
    "(X_1 \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1)";(**)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1)";(**)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1) \\implies  ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies \\lnot X_1))";(**)
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
    "(((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies 
    ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies  (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))))";(**)
    
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1))) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))))) \\implies 
    (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";(**)
    "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot (X_1 \\lor \\lnot X_1)))) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((X_1 \\lor \\lnot X_1) \\implies (\\lnot (X_1 \\implies X_1)))))";(**)
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (((X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1))))) \\implies 
    (((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\implies X_1))))";(**)
    "(((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\lor \\lnot X_1)) \\implies (\\lnot (X_1 \\implies X_1))))";(**)
    "(\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))";(*OK*)
    "((\\lnot (X_1 \\lor \\lnot X_1)) \\implies ((\\lnot (X_1 \\implies X_1)))) \\implies ((\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1))))";(*OK*)
    "(\\lnot (\\lnot (X_1 \\implies X_1))) \\implies (\\lnot(\\lnot (X_1 \\lor \\lnot X_1)))";(*OK*)
    "(\\lnot(\\lnot (X_1 \\lor \\lnot X_1))) \\implies ((X_1 \\lor \\lnot X_1))";(*OK*)
    "\\lnot(\\lnot (X_1 \\lor \\lnot X_1))";(*OK*)
    "(X_1 \\lor \\lnot X_1)"
]);;

(* |- (A \\implies C) \\implies (A \\implies (B \\implies C))*)
let verif_rajout_hypothese =
        (*TODO to delete when not needed anymore
         let 
        X_1,b,X_3=X_1,X_2,X_3
        in
        let (X_1 \\implies X_3) = (X_1 \\implies X_3)
        and (X_2 \\implies X_3) = (b \\implies X_3)
        in*)
proof_verification ~hyp:[] (formula_from_string "(X_1 \\implies X_3) \\implies (X_1 \\implies (X_2 \\implies X_3))")
~proof:(List.map formula_from_string [
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
]);;

(* |- F ou F \\implies F *)
let verif_ou_idempotent =
proof_verification ~hyp:[] (formula_from_string "(X_1 \\lor X_1) \\implies X_1")
~proof:(List.map formula_from_string [
    "((X_1 \\lorX_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))";
    "((\\lnot X_1) \\implies  ((X_1 \\lor X_1) \\implies X_1))";
    "((\\lnot X_1) \\implies  ((X_1 \\lor X_1) \\implies X_1)) \\implies ((((X_1 \\lorX_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))))";
    "((((X_1 \\lorX_1) \\implies X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies ((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1)))";
    "((\\lnot X_1) \\implies ((\\lnot X_1) \\implies \\lnot (X_1\\lorX_1))) \\implies  (((\\lnot X_1) \\implies (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies (\\lnot X_1))";
    "(((\\lnot X_1) \\implies (\\lnot X_1)) \\implies ((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))))";
    "((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1)))";
    "((\\lnot X_1) \\implies (\\lnot (X_1\\lorX_1))) \\implies  ((X_1\\lorX_1)  \\implies X_1)";
    "(X_1\\lorX_1) \\implies X_1";
]);;
(*TODO 
(* |- (A ou B) \\implies (A \\implies C) \\implies (B \\implies C) \\implies C*)
let verif_ou_diamant =
let 
X_1,b,X_3=X_1,X_2,X_3
in
let tout = \\lnot (X_1 \\implies X_1)
and (X_1 \\lor X_2) = (X_1 \\lorb)
and (X_1 \\implies X_3) = (X_1 \\implies X_3)
and (X_2 \\implies X_3) = (b \\implies X_3)
in
(proof_verification ~hyp:[] ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)))
~proof:[
X_1 \\implies X_1;
(X_1 \\implies X_1) \\implies (\\lnot tout);
(*\\lnot tout*)
(\\lnot tout);
(\\lnot tout) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout);
((X_2 \\implies X_3) \\implies  \\lnot tout);
((X_2 \\implies X_3) \\implies  \\lnot tout) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout));
((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout));
((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout)) \\implies 
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout)));
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies  \\lnot tout)));

(*(X_1 \\lor X_2);*)
(*(X_1 \\lor X_2) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2));*)
(X_1 \\lor X_2) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2));

(*((\\lnot X_3) \\implies (X_1 \\lor X_2));*)
((X_1 \\lor X_2) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2))) \\implies  ((X_1 \\lor X_2) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2))));

((X_1 \\lor X_2) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2))));
((X_1 \\lor X_2) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2)))) \\implies 
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2)))));
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\lor X_2)))));
(*(X_1 \\implies X_3);*)
(X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\implies X_3));
(*((\\lnot X_3) \\implies (X_1 \\implies X_3));*)

((\\lnot X_3) \\implies (\\lnot X_3));
((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_3)));
((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_3)));
(((X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)));
(((X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies ((\\lnot X_3) \\implies (((X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))));
((\\lnot X_3) \\implies (((X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))));
((\\lnot X_3) \\implies (((X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies 
(((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))));
(((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))));
(((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies 
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (X_1 \\implies X_3)) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))))) \\implies 
(((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
(((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_1 \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
(X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)));
((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)));

(((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies 
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))))) \\implies 
(((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
(((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))));
(X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_3)) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies 
(((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_3))) \\implies ((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1))));
((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_3))) \\implies ((X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1)));
(*((\\lnot X_3) \\implies (\\lnot X_1));*)
(X_1 \\implies X_3) \\implies ((\\lnot X_3) \\implies (\\lnot X_1));
((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b)));
(*((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))) \\implies  ((\\lnot X_3) \\implies  ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))));*)
((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))) \\implies  ((\\lnot X_3) \\implies  ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))));
(*((\\lnot X_3) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))));*)
((\\lnot X_3) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b))));
(*((\\lnot X_3) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b)))) \\implies (((\\lnot X_3) \\implies (\\lnot X_1)) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))));*)
((\\lnot X_3) \\implies ((\\lnot X_1) \\implies ((X_1 \\lor b) \\implies (b)))) \\implies (((\\lnot X_3) \\implies (\\lnot X_1)) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))));
(*(((\\lnot X_3) \\implies (\\lnot X_1)) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))));*)
((((\\lnot X_3) \\implies (\\lnot X_1)) \\implies ((\\lnot X_3) \\implies (((X_1 \\lor X_2)) \\implies (b)))));
((((\\lnot X_3) \\implies (\\lnot X_1)) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies 
((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))));
((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))));
((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies 
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))));
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))));
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies (\\lnot X_1))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))) \\implies 
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))));
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies (\\lnot X_1)))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))));
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))));
(*
X_1 : (X_1 \\implies X_3)
b : (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))
X_3 : (X_2 \\implies X_3)
*)



(((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies b))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))));
((((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies b))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))) \\implies 
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))));
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))); (*k k*)
((X_1 \\implies X_3) \\implies ((((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))) \\implies 
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))));

(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))); (*s (k k)*)
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))));
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))));(*k (s (k k))*)
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))))) \\implies 
((((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))))));
((((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))) \\implies (((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))))); (*(s (k (s (k k))))*)
((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))));(*i*)
(((X_1 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor b) \\implies (b)))))));(*((s (k (s (k k)))) i)*)




(*((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)));*)

(X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))));
(*((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b));*)
((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b));
(((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))) \\implies 
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b)))));
(*(((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies b));*)

(X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies (b))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies (b)))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))));

((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies (b))))) \\implies ((((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies (b)))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));

((((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_1 \\lor X_2))) \\implies ((\\lnot X_3) \\implies (b)))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)))));

(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))) \\implies 
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_1 \\lor X_2)))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))))));
(*((\\lnot X_3) \\implies (b));*)
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))));
(*((\\lnot X_3) \\implies (b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b))));

(X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (b)));*)
(*(X_2 \\implies X_3);*)
(X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies  (X_2 \\implies X_3));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies  (X_2 \\implies X_3))) \\implies 
((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies  (X_2 \\implies X_3))));
(*((\\lnot X_3) \\implies ((X_2 \\implies X_3)));*)
(X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies  (X_2 \\implies X_3)));

(*((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3));*)
(((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)));
(((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))));
(X_2 \\implies X_3) \\implies  (((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)));
((X_2 \\implies X_3) \\implies  (((\\lnot X_3) \\implies ((X_2 \\implies X_3))) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))));


(X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_2 \\implies X_3))))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))));
(*(((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3));*)
(*(((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3));
(((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)));*)
(X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)));

(((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3))) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies b) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));


 (X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))));

(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies 
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies b)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))));

(*((\\lnot X_3) \\implies (X_3));*)
(*((\\lnot X_3) \\implies (X_3));
((\\lnot X_3) \\implies (X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_3)));*)
(X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (X_3))));
(*((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3)));*)
((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3)));
((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))));
(*(((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)));*)
(((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)));
(((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))));
((X_2 \\implies X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))));
(*(((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies  ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))));*)
((((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies  ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))));
((((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies  ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))))) \\implies ((X_2 \\implies X_3) \\implies ((((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies  ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))))));
((X_2 \\implies X_3) \\implies ((((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))) \\implies  ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))))));
(*((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))));*)
((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout))));
((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))));
(*((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies  (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)));*)
(((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies  (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout))));
(((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies  (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies  (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies (((\\lnot tout) \\implies (\\lnot X_3)) \\implies ((X_3) \\implies (tout)))) \\implies  (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)))));
(*(((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)));*)
(((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout)));
(((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout))));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies ((\\lnot tout) \\implies (\\lnot X_3))) \\implies ((\\lnot X_3) \\implies (X_3 \\implies tout))));
(*((\\lnot X_3) \\implies ((X_3) \\implies (tout)));*)
((\\lnot X_3) \\implies ((X_3) \\implies (tout)));
((\\lnot X_3) \\implies ((X_3) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_3) \\implies (tout))));
((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies ((X_3) \\implies (tout))));
(*((\\lnot X_3) \\implies (X_3 \\implies tout)) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout));*)
((\\lnot X_3) \\implies (X_3 \\implies tout)) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout));
(((\\lnot X_3) \\implies (X_3 \\implies tout)) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies (X_3 \\implies tout)) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout))));
(X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies (X_3 \\implies tout)) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout)));
(*((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout);*)
(((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout));
(((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout)) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout)));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout)));
((X_2 \\implies X_3) \\implies (((\\lnot X_3) \\implies X_3) \\implies  ((\\lnot X_3) \\implies tout))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)));
(((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))));

(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)))) \\implies 
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)))));


(X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))));

((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)))));
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies X_3)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot X_3) \\implies tout)))));
(*((\\lnot X_3) \\implies (tout));*)
(*((\\lnot X_3) \\implies (tout));
((\\lnot X_3) \\implies (tout)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)));*)



(X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))));
(*(((\\lnot X_3) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot X_3))));*)
((\\lnot (X_3)) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))));
(((\\lnot (X_3)) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies ((X_2 \\implies X_3) \\implies (((\\lnot (X_3)) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))));
((X_2 \\implies X_3) \\implies (((\\lnot (X_3)) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))));
((X_2 \\implies X_3) \\implies (((\\lnot (X_3)) \\implies (tout)) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
(((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))));
(((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))));
(((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))));
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))));


((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))));

((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))) \\implies ((((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))) \\implies ((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))));
((((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))) \\implies ((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))));

(X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))));

(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot (X_3)) \\implies (tout))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))));
(*((\\lnot tout) \\implies (\\lnot(\\lnot X_3)));*)
(*((\\lnot tout) \\implies (\\lnot(\\lnot X_3)));
((\\lnot tout) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))));*)
(X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))));
((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies 
(((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))));

(((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies 
(((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies 
(((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies 
(((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));

(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))));

(X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));

((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))));

(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot tout) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))));

(X_1 \\lor X_2) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))));

((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies ((((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies ((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))));             
((((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot tout)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies ((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))));
(X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))));


((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))))))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot tout)))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))))));
(*(\\lnot(\\lnot X_3));*)
(*(\\lnot(\\lnot X_3));
(\\lnot(\\lnot X_3)) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3))));*)
(X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot (X_3)))));
(*((\\lnot(\\lnot X_3)) \\implies (X_3));*)
((\\lnot(\\lnot X_3)) \\implies (X_3));
((\\lnot(\\lnot X_3)) \\implies (X_3)) \\implies ((X_2 \\implies X_3) \\implies ((\\lnot(\\lnot X_3)) \\implies (X_3)));
((X_2 \\implies X_3) \\implies ((\\lnot(\\lnot X_3)) \\implies (X_3)));

((X_2 \\implies X_3) \\implies ((\\lnot(\\lnot X_3)) \\implies (X_3))) \\implies 
(((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3));

(((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3));

(((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3)) \\implies 
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3)));

((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3)));
((X_1 \\implies X_3) \\implies (((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))) \\implies ((X_2 \\implies X_3) \\implies X_3))) \\implies 
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)));
(((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))) \\implies 
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))));
((X_1 \\lor X_2) \\implies (((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3)))) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)))) \\implies 
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))));
(((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies (\\lnot(\\lnot X_3))))) \\implies ((X_1 \\lor X_2) \\implies ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3))));
(*(X_3)*)
(*X_3;
X_3 \\implies ((X_2 \\implies X_3) \\implies X_3);*)
(*(X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3);
((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)) \\implies  ((X_1 \\lor X_2) \\implies  ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)));*)

((X_1 \\lor X_2) \\implies  ((X_1 \\implies X_3) \\implies ((X_2 \\implies X_3) \\implies X_3)));
]);;
*)

let test_tauto test_ctxt = assert_bool "tauto"  (verif_tauto)
let test_cut test_ctxt = assert_bool "cut"  (verif_cut)
let test_contraposee test_ctxt = assert_bool "contraposee"  (verif_contraposee)
let test_tiers_exclus test_ctxt = assert_bool "tiers exclus"  (verif_tiers_exclus)
let test_rajout_hypothese test_ctxt = assert_bool "rajout hypothese"  (verif_rajout_hypothese)
let test_ou_idempotent test_ctxt = assert_bool "ou idempotent" (verif_ou_idempotent)
(*let test_ou_diamant test_ctxt = assert_bool "ou diamant" (verif_ou_diamant)*)

let test_instance test_ctxt = assert_bool "instance" (instance (formula_from_string "X_1 \\land X_2") (formula_from_string "X_1 \\land X_2"))

(** Tests for to_string *)
let test_to_string_formula_pvar test_ctxt =
let s = to_string_formula_prop  (PVar 1)
in assert_equal s "P1"
                                                
let test_to_string_formula_pneg test_ctxt =
let s = to_string_formula_prop  (formula_from_string "\\lnot X_1")
in assert_equal s "!P1"

let test_to_string_formula_pand test_ctxt =
let s =  to_string_formula_prop  (formula_from_string "X_1 \\land X_2")
in assert_equal s "P1 /\\ P2"

let test_to_string_formula_por test_ctxt = 
let s = to_string_formula_prop  (formula_from_string "X_1 \\lor X_2")
in assert_equal s "P1 \\/ P2"

let test_to_string_formula_pand_por test_ctxt = 
let s = to_string_formula_prop  (formula_from_string "(X_1 \\land X_2) \\lor X_3")
in assert_equal s "(P1 /\\ P2) \\/ P3"

let test_to_string_formula_por_pand test_ctxt = 
let s = to_string_formula_prop  (formula_from_string "(X_1 \\lor X_2) \\land X_3")
in assert_equal s "(P1 \\/ P2) /\\ P3"

let test_to_string_formula_impl test_ctxt = 
let s = to_string_formula_prop  (formula_from_string "X_1 \\implies X_2")
in assert_equal s "P1 => P2"

let test_to_string_formula_and_impl test_ctxt = 
let s = to_string_formula_prop  (formula_from_string "X_3 \\land (X_1 \\implies X_2)")
in assert_equal s "P3 /\\ (P1 => P2)"

(* Tests for printer_formula *)
let test_printer_formula_pvar test_ctxt = printer_formula_prop Format.str_formatter (PVar 1);
let s = Format.flush_str_formatter()
in assert_equal s "P1"
                                                
let test_printer_formula_pneg test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "\\lnot X_1");
let s = Format.flush_str_formatter()
in assert_equal s "!P1"

let test_printer_formula_pand test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "X_1 \\land X_2");
let s = Format.flush_str_formatter()
in assert_equal s "P1 /\\ P2"

let test_printer_formula_por test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "X_1 \\lor X_2");
let s = Format.flush_str_formatter()
in assert_equal s "P1 \\/ P2"

let test_printer_formula_pand_por test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "(X_1 \\land X_2) \\lor X_3");
let s = Format.flush_str_formatter()
in assert_equal s "(P1 /\\ P2) \\/ P3"

let test_printer_formula_por_pand test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "(X_1 \\lor X_2) \\land X_3");
let s = Format.flush_str_formatter()
in assert_equal s "(P1 \\/ P2) /\\ P3"

let test_printer_formula_impl test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "X_1 \\implies X_2");
let s = Format.flush_str_formatter()
in assert_equal s "P1 => P2"

let test_printer_formula_and_impl test_ctxt = printer_formula_prop Format.str_formatter (formula_from_string "X_3 \\land (X_1 \\implies X_2)");
let s = Format.flush_str_formatter()
in assert_equal s "P3 /\\ (P1 => P2)"

let instance_suite =
        "Instance">:::
                [ "test_instance">::test_instance ;
                ]

let printer_formula_suite =
        "printer_formula" >:::
                [ "test printer_formula PVar">:: test_printer_formula_pvar;
                  "test printer_formula PNeg">:: test_printer_formula_pneg;
                  "test printer_formula PAnd">:: test_printer_formula_pand;
                  "test printer_formula POr">:: test_printer_formula_por;
                  "test_printer_formula_pand_por">:: test_printer_formula_pand_por;
                  "test_printer_formula_por_pand">::test_printer_formula_por_pand;
                  "test_printer_formula_impl">::test_printer_formula_impl;
                  "test_printer_formula_and_impl">::test_printer_formula_and_impl;
                ]

let to_string_formula_suite =
        "to_string_formula" >:::
                [ "test to_string_formula PVar">:: test_to_string_formula_pvar;
                  "test to_string_formula PNeg">:: test_to_string_formula_pneg;
                  "test to_string_formula PAnd">:: test_to_string_formula_pand;
                  "test to_string_formula POr">:: test_to_string_formula_por;
                  "test_to_string_formula_pand_por">:: test_to_string_formula_pand_por;
                  "test_to_string_formula_por_pand">::test_to_string_formula_por_pand;
                  "test_to_string_formula_impl">::test_to_string_formula_impl;
                  "test_to_string_formula_and_impl">::test_to_string_formula_and_impl;
                ]


let prop_suite =
        "Prop">:::
                [ "test_tauto" >:: test_tauto ;
                  "test_cut" >:: test_cut ; 
                  "test_contraposee" >:: test_contraposee ; 
                  "test_tiers_exclus" >:: test_tiers_exclus ; 
                  "test_rajout_hypothese" >:: test_rajout_hypothese ; 
                  "test_ou_idempotent" >:: test_ou_idempotent ; 
                  (*"test_ou_diamant" >:: test_ou_diamant ;*)
                ] 
;;

let () =
        run_test_tt_main instance_suite;
        run_test_tt_main printer_formula_suite;
        run_test_tt_main to_string_formula_suite;
        run_test_tt_main prop_suite;
;;

