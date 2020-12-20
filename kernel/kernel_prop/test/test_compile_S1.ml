open Prop__Proof_prop
open Kernel_prop.Compile
open Kernel_prop.Verif
open OUnit2

let neg p = PNeg p
and (=>.) a b = PImpl(a,b)
and (||.) a b = POr(a,b)
(*let notation = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd";;*)
let x1,x2,x3 = PVar 1, PVar 2, PVar 3
let a,b=x1,x2
let tout = neg (a=>.a)
and a_ou_b = (a||.b)
and b_ou_a = ( b||.a)
let c = b_ou_a
let a_entraine_c = (a=>.c)
and b_entraine_c = (b=>.c)
let demo = 
  let x1,x2 = PVar 1, PVar 2
  in
  let 
    a,b=x1,x2
  in
  let tout = neg (a=>.a)
  and a_ou_b = (a||.b)
  and a_entraine_c = (a=>.c)
  and b_entraine_c = (b=>.c)
  in
  let taut x =
    [
      (x =>. ((x =>. x) =>. x)) =>. ((x =>. (x =>. x)) =>. (x =>. x));
      x =>. ((x =>. x) =>. x);
      (x =>. (x =>. x)) =>. (x =>. x);
      x =>. (x =>. x);
      x =>. x;
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

    (a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.
    ((
      (b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))
      =>.  
      ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))
     )
     =>.
     (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))
    ); 
    (((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
      ((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

    (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))));
    (a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
    ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));
    ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))));

    ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.
    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b))))));
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
    (a_entraine_c=>.(b_entraine_c=>.((neg c)=>. b_entraine_c)));
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
    ((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(b_entraine_c))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.b)=>.((neg c)=>.c)))));
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
    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
    (a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b)))=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))))=>.
    ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));
    ((a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.b))))=>.(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.c)))));

    (*((neg c)=>.(c));*)
    (*((neg c)=>.(c));
      ((neg c)=>.(c))=>.(b_entraine_c=>.((neg c)=>.(c)));*)
    a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(c))));
    (*((neg c)=>.((neg tout)=>.(neg c)));*)
    ((neg c)=>.((neg tout)=>.(neg c)));
    ((neg c)=>.((neg tout)=>.(neg c)))=>.(b_entraine_c=>.((neg c)=>.((neg tout)=>.(neg c))));
    (b_entraine_c=>.((neg c)=>.((neg tout)=>.(neg c))));
    (*(((neg tout)=>.(neg c))=>.((c)=>.(tout)));*)
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
    (((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>. (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout))));
    (((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>. (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout))))=>.(b_entraine_c=>.(((neg c)=>.(((neg tout)=>.(neg c))=>.((c)=>.(tout))))=>. (((neg c)=>.((neg tout)=>.(neg c)))=>.((neg c)=>.(c=>.tout)))));
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


    (a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.
    ((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))));

    (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))=>.(((a_entraine_c=>.((b_entraine_c=>.((neg (c))=>.(tout)))=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c))))))))=>.(a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.((neg (c))=>.(tout))))=>.(a_entraine_c=>.(b_entraine_c=>.((neg tout)=>.(neg(neg (c)))))))));
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

    (a_ou_b=>.(a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c)))))))=>.(((a_entraine_c=>.((b_entraine_c=>.(neg tout))=>.(b_entraine_c=>.(neg(neg (c))))))=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c)))))))=>.(a_ou_b=>.((a_entraine_c=>.(b_entraine_c=>.(neg tout)))=>.(a_entraine_c=>.(b_entraine_c=>.(neg(neg (c))))))));	         
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

    (a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c)));
  ];;
let demo_S1 = 
  try 
    compile_demonstration ~demo:demo ~theory:[] ()
  with Invalid_demonstration(f,l) -> failwith (string_of_int @@ List.length @@ l)
let test_verif _ =
  assert_equal 
    { theorem = a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c));
      demonstration=[]
    }
    (compile_demonstration ~demo:demo ())
let verif_suite =
  "verif test" >:::
  [
    "test verif" >:: test_verif;
  ]

let () =
run_test_tt_main verif_suite
