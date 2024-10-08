open Kernel.Logic
open Kernel_prop_interp.Formula
open Kernel_prop_interp.Instance_notation_printers
open Kernel_prop_interp.Theory.Prop

open OUnit2

let neg p = PNeg p
and (=>.) a b = PImpl(a,b)
and (||.) a b = POr(a,b)
(*let notation = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;*)
let notation = Kernel_prop_interp.Parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;
(* 
   |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
*)
let add_chaining =
  let chaining =
    string_to_formula "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
  let demo_chaining = 
    List.map (fun s -> (Single(string_to_formula s))) [
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
  in
  let chaining_unproved = {
    kind = Kernel.Logic.KUnproved;
    name = "C6";
    params = [];
    premisses = [];
    demonstration = demo_chaining;
    conclusion = chaining;
  }
  in
  let verif = (verif ~keep_calls:Expand_Calls chaining_unproved )          
  in
  match verif with 
  | Ok (Theorem chaining_proved) ->
    Theorems.add_theorem (Theorem {chaining_proved with kind = Kernel.Logic.KTheorem})
  | Error _ -> ()
;;
let x1,x2,x3 = PVar 1, PVar 2, PVar 3
let a,b,c=x1,x2,x3
let tout = neg (a=>.a)
and a_ou_b = (a||.b)
and a_entraine_c = (a=>.c)
and b_entraine_c = (b=>.c)
let diamond =  (a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c)))
let demo = 
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
      ((x2 =>. x3) =>.  (x1 =>. (x2 =>. x3)));
      ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3)));
      ((x2 =>. x3) =>. ((x1 =>. x2) =>. (x1 =>. x3))) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))) =>. ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))));  
      ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2)));
      ((x1 =>. x2) =>. (((x2 =>. x3) =>. (x1 =>. x2)) =>. ((x2 =>. x3) =>. (x1 =>. x3))))  =>.  (((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2))) =>. ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3))));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x2))) =>. ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
      ((x1 =>. x2) =>. ((x2 =>. x3) =>. (x1 =>. x3)));
    ] 
  in
  let neg_contraposition x1 x2 =
    [
      (*138*)      ((neg  (neg  x1))  =>.x1);
      ((neg  (neg  x1))  =>.x1)  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x1))  =>.x1));
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x1))  =>.x1);
      (*155*)    ]@ (cut (neg (neg x2)) (neg (neg x1)) x1) @[
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x1))  =>.x1)  =>.((neg  (neg  x2))  =>.x1));
      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x1))  =>.x1)  =>.((neg  (neg  x2))  =>.x1)))  =>.((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x1))  =>.x1))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x2))  =>.x1)));
      ((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x1))  =>.x1))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x2))  =>.x1)));
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x2))  =>.x1);
      (*160*)      (x2  =>.neg  (neg  x2));
      (x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.neg  (neg  x2)));
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.neg  (neg  x2));
      (*163*)]@cut x2 (neg (neg x2)) x1@[
      (x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1));
      (*165*)      ((x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1)))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1))));
      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1))));
      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((x2  =>.neg  (neg  x2))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1))))  =>.((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.neg  (neg  x2)))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1))));
      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.neg  (neg  x2)))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1)));
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1));
      (*170*)      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(((neg  (neg  x2))  =>.x1)  =>.(x2  =>.x1)))  =>.((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x2))  =>.x1))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.x1)));
      (((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.((neg  (neg  x2))  =>.x1))  =>.(((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.x1));
      ((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.x1);
      (*187*) (((neg  x1)  =>.(neg  x2))  =>.((neg  (neg  x2))  =>.(neg  (neg  x1))));
      (*188*)] @ 
    (cut ((neg  x1)  =>.(neg  x2)) ((neg  (neg  x2))  =>.(neg  (neg  x1))) (x2=>.x1))
    @ [
      (((neg  x1)  =>.(neg  x2))  =>.((neg  (neg  x2))  =>.(neg  (neg  x1))))  =>.((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.x1))  =>.(((neg  x1)  =>.(neg  x2))  =>.(x2  =>.x1)));
      ((((neg  (neg  x2))  =>.(neg  (neg  x1)))  =>.(x2  =>.x1))  =>.(((neg  x1)  =>.(neg  x2))  =>.(x2  =>.x1)));
      (((neg  x1)  =>.(neg  x2))  =>.(x2  =>.x1));
    ]
  in 
  (*05*)  (taut a) @ [
      (a =>. a) =>. (neg tout);
      (*neg tout*)
      (neg tout);
      (neg tout)=>.(b_entraine_c=>. neg tout);
      (b_entraine_c=>. neg tout);
      (*10*)   (b_entraine_c=>. neg tout)=>.(a_entraine_c=>.(b_entraine_c=>. neg tout));
      (a_entraine_c=>.(b_entraine_c=>. neg tout));
      (a_entraine_c=>.(b_entraine_c=>. neg tout))=>.  (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));
      (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));

      (*a_ou_b;*)
      (*a_ou_b=>.((neg c)=>.a_ou_b);*)
      a_ou_b=>.((neg c)=>.a_ou_b);

      (*((neg c)=>.a_ou_b);*)
      (*15*)    ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b));

      (((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))=>. 
      (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

      (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
      ((a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))))=>.
      ((a_ou_b =>. ((neg c) =>. a_ou_b))=>. (a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

      (a_ou_b=>.((neg c)=>.a_ou_b))=>.  (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

      (*20*)  (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

      ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
      ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))) =>. (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))))) =>. ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
      (*25*)    ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));

      (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.a_ou_b))));

      (*a_entraine_c;*)
      (*27*)    a_entraine_c=>.((neg c)=>.a_entraine_c);
      (*((neg c)=>.a_entraine_c);*)
      (*32*)  ] @ (taut (neg c)) @ [
            ((neg c)=>.(neg c))=>.(a_entraine_c=>.((neg c)=>.(neg c)));
            (a_entraine_c=>.((neg c)=>.(neg c)));
            (*35*)    ((a_entraine_c)=>.((neg c)=>.(neg a)));
            ((a_entraine_c)=>.((neg c)=>.(neg a)))=>.((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
            ((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
            ((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))))=>.
            (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
            (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
            (((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))))=>.
            (*40*)    (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
            (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
            (a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))))=>.
            ((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
            ((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
            a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)));
            (*45*)    ((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));

            (((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
            (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
            (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
            (a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))))=>.
            ((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
            ((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
            (*50*)    a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));
            (a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
            ((a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a))));
            (a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a)));
            (*((neg c)=>.(neg a));*)
            a_entraine_c=>.((neg c)=>.(neg a));
            ((neg a)=>.(a_ou_b=>.(b)));
            (*((neg a)=>.(a_ou_b=>.(b)))=>. ((neg c)=>. ((neg a)=>.(a_ou_b=>.(b))));*)
            (*55*)    ((neg a)=>.(a_ou_b=>.(b)))=>. ((neg c)=>. ((neg a)=>.(a_ou_b=>.(b))));
            (*((neg c)=>.((neg a)=>.(a_ou_b=>.(b))));*)
            ((neg c)=>.((neg a)=>.(a_ou_b=>.(b))));
            (*((neg c)=>.((neg a)=>.(a_ou_b=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));*)
            ((neg c)=>.((neg a)=>.(a_ou_b=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));
            (*(((neg c)=>.(neg a))=>.((neg c)=>.(a_ou_b=>.(b))));*)
            ((((neg c)=>.(neg a))=>.((neg c)=>.((a_ou_b)=>.(b)))));
            ((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.
            (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))));
            (*60*)    (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))));
            (a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.
            ((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))));
            ((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))));
            (a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))));

            (((neg c)=>.(a_ou_b=>.b)))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))));
            ((((neg c)=>.(a_ou_b=>.b)))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.
            (*65*)    (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));
            (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))); (*k k*)
            (a_entraine_c=>.((((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))=>.
            ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));

            ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))); (*s (k k)*)
            ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));
            (*70*)    ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));(*k (s (k k))*)
            ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))))=>.
            (((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))));
            (((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))))); (*(s (k (s (k k))))*)
            (*77*)  ] @ (taut ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b))))))) (*i*)@ [

            ((a_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))))));(*((s (k (s (k k)))) i)*)

            (*((neg c)=>.(a_ou_b=>.(b)));*)

            a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))));
            (*((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)
            (*80*)    ((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));
            (((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))=>.
            (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
            (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
            (b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
            ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
            ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
            ((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
            (*85*)    (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
            (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
            (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))))=>.
            ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
            ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
            (*(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)

            a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))));
            (b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
            (*90*)   ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))));


            ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
             ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))) =>. 
            (*91*)(a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

            (*92*)    a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
            (a_entraine_c =>. ((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>. ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))) =>. ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
            (a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
            (*95*)    (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
            (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
            (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));
            (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))=>. ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))) ;
            ((a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>. (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
                                                                                             ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>. (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))))) ;

            (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
              (*100*)      ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

            (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
            (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
            ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));
            ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));

            ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
            (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
            (*105*)    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
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
            (*110*)    (a_entraine_c=>.(b_entraine_c=>.((neg c)=>. b_entraine_c)));
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
            (*120*)    ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b_entraine_c))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))));
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
            (*130*)    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
            (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
            (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))))=>.
            ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
            ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));

            (*((neg c)=>.(c));*)
            (*((neg c)=>.(c));
              ((neg c)=>.(c))=>.(b_entraine_c=>.((neg c)=>.(c)));*)
            a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(c))));
            (*((neg c)=>.((neg tout)=>.(neg c)));*)
            (*135*)     ((neg c)=>.((neg tout)=>.(neg c)));
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
          ];;
let demo_S1 = 
  try 
    Kernel_prop_compile.Theory.Prop.compile  ~demonstration:(List.map (fun f -> Kernel_prop_compile.Theory.Prop.Single f) demo)  ()
  with Invalid_demonstration(demo) -> failwith (Printf.eprintf"\n";Printf.eprintf "\n";to_string_formula_prop demo.conclusion ^ (string_of_int @@ List.length @@ demo.demonstration))

let test_verif _ =
  assert_bool "test_verif" 
    (match Kernel_prop_compile.Theory.Prop.verif ~keep_calls:Expand_Calls 
             {kind = KInvalid;name="diamond";params=[];premisses=[];conclusion=diamond;demonstration=(List.map (function f -> Kernel_prop_compile.Theory.Prop.Single f) demo)}
     with Ok _ -> true
        | _ -> false)
let verif_suite =
  "verif test" >:::
  [
    "test verif" >:: test_verif;
  ]

let () =
  run_test_tt_main verif_suite
