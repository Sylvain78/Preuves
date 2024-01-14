open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Verif
open Kernel_prop_compile.Compile
open Kernel_prop_compile.Verif
open Kernel_prop_compile.Step

open OUnit2

let neg p = PNeg p
and (=>.) a b = PImpl(a,b)
and (||.) a b = POr(a,b)
(*let notation = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;*)
let notation = Kernel_prop_interp.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;
(* 
   |-   (F \\implies G) \\implies (G \\implies H) \\implies (F \\implies H)
*)
let add_chaining =
  let chaining =
    formula_from_string "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
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
  in
  let verif = (kernel_prop_interp_verif ~axioms:!axioms_prop chaining ~proof:demo_chaining)          
  in
  if verif then
      theorems_prop :=
        {
          kind_prop = Kernel_prop_interp.Kind_prop.Theorem;
          name_theorem_prop = "C6";
          proof_prop = demo_chaining;
          conclusion_prop = chaining;
        }
        :: !theorems_prop
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
    compile_demonstration ~axioms:!axioms_prop ~theorems:!theorems_prop ~demo:(List.map (fun f -> Step f) demo)  ()
  with Invalid_demonstration(f,l) -> failwith (Printf.eprintf"\n";Printf.eprintf "\n";to_string_formula_prop f ^ (string_of_int @@ List.length @@ l) )

let test_verif _ =
  assert_equal 
    (Ok ()) 
    (kernel_prop_compile_verif ~axioms:!axioms_prop ~theorems:!theorems_prop ~formula:(a_ou_b =>. (a_entraine_c=>.(b_entraine_c =>. c))) 
       ~proof:(compile_demonstration ~axioms:!axioms_prop ~theorems:!theorems_prop ~demo:(List.map (fun f -> Step f) demo) ()).demonstration ())
let verif_suite =
  "verif test" >:::
  [
    "test verif" >:: test_verif;
  ]

let () =
  run_test_tt_main verif_suite
