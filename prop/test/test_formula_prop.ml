open OUnit2
open Formula_prop
open Axioms_prop
open Proof_prop

(* |- F=>.F *)
let verif_tauto = (proof_verification ~hyp:[] (x1=>.x1) 
~proof:[
	(x1 =>.((x1 =>. x1)=>.x1)) =>.
	(( x1 =>. (x1 =>. x1)) =>. (x1 =>. x1));
	x1=>.((x1=>.x1)=>.x1);
	(x1 =>. (x1 =>. x1)) =>. (x1 =>. x1);
	x1=>.(x1=>.x1);
	x1=>.x1
]);;

(* |- (F=>.G)=>.(G=>.H)=>.(F=>.H)*)
let verif_cut = (proof_verification ~hyp:[] ((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))
~proof:[
	(x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3));
	((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3)))=>.((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>.((x1=>.(x2=>.x3))=>.((x1=>.x2)=>.(x1=>.x3))))=>.(((x2=>.x3)=>.(x1=>.(x2=>.x3)))=>.((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3))));
	(((x2=>.x3)=>.(x1=>.(x2=>.x3)))=>.((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3))));
	((x2=>.x3)=>. (x1=>.(x2=>.x3)));
	((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3)));
	((x2=>.x3)=>.((x1=>.x2)=>.(x1=>.x3)))=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)));
	(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)));
	(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3)))=>.((x1=>.x2)=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3))));	
	((x1=>.x2)=>.(((x2=>.x3)=>.(x1=>.x2))=>.((x2=>.x3)=>.(x1=>.x3))));
                        
	(*k*)
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)));
	
	(*s*)
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))) =>.
	(((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)))=>.((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3))));
	
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x2)))=>.((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)));
	((x1=>.x2)=>.((x2=>.x3)=>.(x1=>.x3)))
]);;

(*non A =>. non B |- B =>. A*)
let verif_contraposee = 
        let h = ((neg (neg x2))=>.(neg (neg x1)))	
        and a_ou_b =((neg (neg x1))=>. x1)
        and i = ((neg (neg x2))=>. x1)	
        and a2=	(x2=>.neg (neg x2))
        in
(proof_verification ~hyp:[] (((neg x1)=>.(neg x2))=>.(x2=>.x1))
~proof:[

a_ou_b;
a_ou_b=>.(h=>.a_ou_b);
h=>.a_ou_b;
h =>.(a_ou_b=>.i);
(h =>.(a_ou_b=>.i))=>.((h=>.a_ou_b)=>.(h=>.i));
((h=>.a_ou_b)=>.(h=>.i));
h=>.i;
a2;
a2=>.(h=>.a2);
h=>.a2;
a2=>.(i=>.(x2=>.x1));
(a2=>.(i=>.(x2=>.x1)))=>. (h=>.(a2=>.(i=>.(x2=>.x1))));
(h=>.(a2=>.(i=>.(x2=>.x1))));
(h=>.(a2=>.(i=>.(x2=>.x1)))) =>. ((h=>.a2)=>.(h=>.(i=>.(x2=>.x1))));
(h=>.a2)=>.(h=>.(i=>.(x2=>.x1)));
h=>.(i=>.(x2=>.x1));
(h=>.(i=>.(x2=>.x1)))=>.((h=>.i)=>.(h=>.(x2=>.x1)));
(h=>.i)=>.(h=>.(x2=>.x1));
h=>.(x2=>.x1);
(((neg x1)=>.(neg x2))=>. h);
(((neg x1)=>.(neg x2))=>. h)=>.((h=>.(x2=>.x1))=>.(((neg x1)=>.(neg x2))=>.(x2=>.x1)));
((h=>.(x2=>.x1))=>.(((neg x1)=>.(neg x2))=>.(x2=>.x1)));
(((neg x1)=>.(neg x2))=>.(x2=>.x1));
]);;

(*|- A ou neg A*)
let verif_tiers_exclus =
let z = x1 ||. neg x1
and tout = neg (x1=>.x1)
in
(proof_verification ~hyp:[] (z)
~proof:[

(x1=>.x1);(**)
(x1=>.x1) =>. (neg tout); (**)
neg tout;(*OK*)
 
(neg z)=>.(neg z);(*OK*)

x1=>.z;(**)
(x1=>.z)=>.((neg z) =>. (x1=>.z));(**)
(neg z)=>.(x1=>.(z));(*OK*)

((x1=>.z)=>.((neg z)=>.(neg x1))); (**)
((x1=>.z)=>.((neg z)=>.(neg x1))) =>. ((neg z)=>. ((x1=>.z)=>.((neg z)=>.(neg x1)))); (**)
(neg z)=>.((x1=>.z)=>.((neg z)=>.(neg x1))); (*OK*)

(x1=>.z)=>.((neg z) =>. neg x1);(**)
((neg z) =>. neg x1);(**)
((neg z) =>. neg x1)=>. ((neg z)=>.((neg z) =>. neg x1));(**)
(neg z)=>.((neg z)=>.(neg x1));(*OK*)

((neg z)=>.((neg z)=>.(neg x1)))=>.(((neg z)=>.(neg z))=>.((neg z)=>.(neg x1)));(**)
((neg z)=>.(neg z))=>.((neg z)=>.(neg x1));(**)
(neg z)=>.(neg x1);(*OK*)

(neg x1)=>. z;(**)
((neg x1)=>. z)=>. ((neg z)=>.((neg x1)=>. z));(**)
(neg z)=>.((neg x1)=>.(z));(*OK*)
((neg z)=>.((neg x1)=>.(z)))=>.(((neg z)=>. (neg x1))=>. ((neg z)=>. z));(**)
((neg z)=>. (neg x1))=>. ((neg z)=>. z);(**)
(neg z)=>.(z);(*OK*)

(neg z)=>.((neg tout)=>.(neg z));(*OK*)

((neg tout)=>.(neg z))=>.((z)=>.(tout));(**)
(((neg tout)=>.(neg z))=>.((z)=>.(tout)))=>.
((neg z)=>. (((neg tout)=>.(neg z))=>.((z)=>.(tout))));(**)

(neg z)=>.(((neg tout)=>.(neg z))=>.((z)=>.(tout)));(*OK*)
((neg z)=>.(((neg tout)=>.(neg z))=>.((z)=>.(tout))))=>.
(((neg z)=>.((neg tout)=>.(neg z)))=>.((neg z)=>.(z=>.tout)));(**)
(((neg z)=>.((neg tout)=>.(neg z)))=>.((neg z)=>.(z=>.tout)));(**)
(neg z)=>.((z)=>.(tout));(*OK*)
((neg z)=>.((z)=>.(tout)))=>.
(((neg z)=>.z) =>. ((neg z) =>. tout));(**)
(((neg z)=>.z) =>. ((neg z) =>. tout));(**)
(neg z)=>.(tout);(*OK*)
((neg z)=>.(tout))=>.((neg tout)=>.(neg(neg z)));(*OK*)
(neg tout)=>.(neg(neg z));(*OK*)
(neg(neg z))=>.(z);(*OK*)
neg(neg z);(*OK*)
z
]);;

(* |- (A=>.C)=>.(A=>.(B=>.C))*)
let verif_rajout_hypothese =
        let 
        a,b,c=x1,x2,x3
        in
        let a_entraine_c = (a=>.c)
        and b_entraine_c = (b=>.c)
        in
(proof_verification ~hyp:[] (a_entraine_c=>.(a=>.b_entraine_c))
~proof:[
 (*((S (K (S (K K)))) I)*)	
a_entraine_c=>.a_entraine_c;(*i*)
c=>.b_entraine_c; (*k*)
(c=>.b_entraine_c)=>.(a=>.(c=>.b_entraine_c)); 
(a=>.(c=>.b_entraine_c)); (*k k*)
(a=>.(c=>.b_entraine_c))=>.
(a_entraine_c=>.(a=>.b_entraine_c)); 
(a_entraine_c=>.(a=>.b_entraine_c)); (*s (k k)*)
(a_entraine_c=>.(a=>.b_entraine_c))=>.(a_entraine_c=>.(a_entraine_c=>.(a=>.b_entraine_c)));
(a_entraine_c=>.(a_entraine_c=>.(a=>.b_entraine_c))); (*k (s (k k))*)
(a_entraine_c=>.(a_entraine_c=>.(a=>.b_entraine_c)))=>.
((a_entraine_c=>.a_entraine_c)=>.(a_entraine_c=>.(a=>.b_entraine_c)));
((a_entraine_c=>.a_entraine_c)=>.(a_entraine_c=>.(a=>.b_entraine_c)));(*s (k (s (k k)))*)
(a_entraine_c=>.(a=>.b_entraine_c)); (*(s (k (s (k k)))) i*)
]);;

(* |- F ou F =>. F *)
let verif_ou_idempotent =
(proof_verification ~hyp:[] ((x1 ||. x1)=>.x1)
~proof:[
((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1));
((neg x1)=>. ((x1 ||. x1) =>. x1));
((neg x1)=>. ((x1 ||. x1) =>. x1))=>.((((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1)))=>.((neg x1)=>.((neg x1) =>. neg (x1||.x1))));
((((x1 ||.x1) =>. x1)=>.((neg x1) =>. neg (x1||.x1)))=>.((neg x1)=>.((neg x1) =>. neg (x1||.x1))));
((neg x1)=>.((neg x1) =>. neg (x1||.x1)));
((neg x1)=>.((neg x1) =>. neg (x1||.x1)))=>. (((neg x1) =>. (neg x1))=>.((neg x1)=>.(neg (x1||.x1))));
((neg x1) =>. (neg x1));
(((neg x1) =>. (neg x1))=>.((neg x1)=>.(neg (x1||.x1))));
((neg x1)=>.(neg (x1||.x1)));
((neg x1)=>.(neg (x1||.x1)))=>. ((x1||.x1) =>.x1);
(x1||.x1) =>. x1;
]);;
(*TODO 
(* |- (A ou B)=>.(A=>.C)=>.(B=>.C)=>.C*)
let verif_ou_diamant =
let 
a,b,c=x1,x2,x3
in
let tout = neg (a=>.a)
and a_ou_b = (a ||.b)
and a_entraine_c = (a=>.c)
and b_entraine_c = (b=>.c)
in
(proof_verification ~hyp:[] (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.c)))
~proof:[
a=>.a;
(a=>.a) =>. (neg tout);
(*neg tout*)
(neg tout);
(neg tout)=>.(b_entraine_c=>. neg tout);
(b_entraine_c=>. neg tout);
(b_entraine_c=>. neg tout)=>.(a_entraine_c=>.(b_entraine_c=>. neg tout));
(a_entraine_c=>.(b_entraine_c=>. neg tout));
(a_entraine_c=>.(b_entraine_c=>. neg tout))=>.
(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));
(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));

(*a_ou_b;*)
(*a_ou_b=>.((neg c)=>.a_ou_b);*)
a_ou_b=>.((neg c)=>.a_ou_b);

(*((neg c)=>.a_ou_b);*)
(a_ou_b=>.((neg c)=>.a_ou_b)) =>.  (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

(a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));
(a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)))=>.
(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.a_ou_b))));
(a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.((neg c)=>.a_ou_b))));
(*a_entraine_c;*)
a_entraine_c=>.((neg c)=>.a_entraine_c);
(*((neg c)=>.a_entraine_c);*)

((neg c)=>.(neg c));
((neg c)=>.(neg c))=>.(a_entraine_c=>.((neg c)=>.(neg c)));
(a_entraine_c=>.((neg c)=>.(neg c)));
((a_entraine_c)=>.((neg c)=>.(neg a)));
((a_entraine_c)=>.((neg c)=>.(neg a)))=>.((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))));
((neg c)=>.((a_entraine_c)=>.((neg c)=>.(neg a))))=>.
(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))));
(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a))))=>.
(a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
(a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))));
(a_entraine_c=>.(((neg c)=>.a_entraine_c)=>.((neg c)=>.((neg c)=>.(neg a)))))=>.
((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
((a_entraine_c=>.((neg c)=>.a_entraine_c))=>.(a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)))));
a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a)));
((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));

(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
(a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
(a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
(a_entraine_c=>.(((neg c)=>.((neg c)=>.(neg a)))=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))))=>.
((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
((a_entraine_c=>.((neg c)=>.((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)))));
a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a)));
(a_entraine_c=>.(((neg c)=>.(neg c))=>.((neg c)=>.(neg a))))=>.
((a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a))));
(a_entraine_c=>.((neg c)=>.(neg c)))=>.(a_entraine_c=>.((neg c)=>.(neg a)));
(*((neg c)=>.(neg a));*)
a_entraine_c=>.((neg c)=>.(neg a));
((neg a)=>.((a ||. b)=>.(b)));
(*((neg a)=>.((a ||. b)=>.(b)))=>. ((neg c)=>. ((neg a)=>.((a ||. b)=>.(b))));*)
((neg a)=>.((a ||. b)=>.(b)))=>. ((neg c)=>. ((neg a)=>.((a ||. b)=>.(b))));
(*((neg c)=>.((neg a)=>.((a ||. b)=>.(b))));*)
((neg c)=>.((neg a)=>.((a ||. b)=>.(b))));
(*((neg c)=>.((neg a)=>.((a ||. b)=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.((a ||. b)=>.(b))));*)
((neg c)=>.((neg a)=>.((a ||. b)=>.(b))))=>.(((neg c)=>.(neg a))=>.((neg c)=>.((a ||. b)=>.(b))));
(*(((neg c)=>.(neg a))=>.((neg c)=>.((a ||. b)=>.(b))));*)
((((neg c)=>.(neg a))=>.((neg c)=>.((a_ou_b)=>.(b)))));
((((neg c)=>.(neg a))=>.((neg c)=>.((a ||. b)=>.(b)))))=>.
((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b)))));
((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b)))));
((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.
(a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b))))));
(a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b))))));
(a_entraine_c=>.((((neg c)=>.(neg a)))=>.(((neg c)=>.((a ||. b)=>.(b))))))=>.
((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))));
((a_entraine_c=>.(((neg c)=>.(neg a))))=>.(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))));
(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))));
(*
a : a_entraine_c
b : (((neg c)=>.((a ||. b)=>.(b))))
c : b_entraine_c
*)



(((neg c)=>.((a ||. b)=>.b)))=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))));
((((neg c)=>.((a ||. b)=>.b)))=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))=>.
(a_entraine_c=>.((((neg c)=>.((a ||. b)=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))));
(a_entraine_c=>.((((neg c)=>.((a ||. b)=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))); (*k k*)
(a_entraine_c=>.((((neg c)=>.((a ||. b)=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))))=>.
((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))));

((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))); (*s (k k)*)
((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))));
((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))));(*k (s (k k))*)
((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))))=>.
(((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))));
(((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b))))))=>.((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))))); (*(s (k (s (k k))))*)
(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))));(*i*)
((a_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.((a ||. b)=>.(b)))))));(*((s (k (s (k k)))) i)*)




(*((neg c)=>.(a_ou_b=>.(b)));*)

a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))));
(*((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)
((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));
(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))=>.
(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
(b_entraine_c=>.(((neg c)=>.(a_ou_b=>.(b)))=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))));
((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b))))=>.
(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b))))=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))))=>.
((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
((a_entraine_c=>.(b_entraine_c=>.((neg c)=>.(a_ou_b=>.(b)))))=>.(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.b)))));
(*(((neg c)=>.(a_ou_b))=>.((neg c)=>.b));*)

a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))));
(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))));

(a_entraine_c=>.(b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b)))))=>.(((b_entraine_c=>.(((neg c)=>.(a_ou_b))=>.((neg c)=>.(b))))=>.
((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b)))))=>.(a_entraine_c=>.((b_entraine_c=>.((neg c)=>.(a_ou_b)))=>.(b_entraine_c=>.((neg c)=>.(b))))));

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
]);;
*)

let test_tauto test_ctxt = assert_bool "tauto"  (verif_tauto)
let test_cut test_ctxt = assert_bool "cut"  (verif_cut)
let test_contraposee test_ctxt = assert_bool "contraposee"  (verif_contraposee)
let test_tiers_exclus test_ctxt = assert_bool "tiers exclus"  (verif_tiers_exclus)
let test_rajout_hypothese test_ctxt = assert_bool "rajout hypothese"  (verif_rajout_hypothese)
let test_ou_idempotent test_ctxt = assert_bool "ou idempotent" (verif_ou_idempotent)
(*let test_ou_diamant test_ctxt = assert_bool "ou diamant" (verif_ou_diamant)*)

let x1,x2,x3 = PVar 1, PVar 2, PVar 3

let test_instance test_ctxt = assert_bool "instance" (instance (x1 &&. x2) (x1 &&. x2))

(** Tests for to_string *)
let test_to_string_formula_pvar test_ctxt =
let s = to_string_formula_prop  (x1)
in assert_equal s "P1"
                                                
let test_to_string_formula_pneg test_ctxt =
let s = to_string_formula_prop  (neg x1)
in assert_equal s "!P1"

let test_to_string_formula_pand test_ctxt =
let s =  to_string_formula_prop  (x1 &&. x2)
in assert_equal s "P1 /\\ P2"

let test_to_string_formula_por test_ctxt = 
let s = to_string_formula_prop  (x1 ||. x2)
in assert_equal s "P1 \\/ P2"

let test_to_string_formula_pand_por test_ctxt = 
let s = to_string_formula_prop  ((x1 &&. x2) ||. x3)
in assert_equal s "(P1 /\\ P2) \\/ P3"

let test_to_string_formula_por_pand test_ctxt = 
let s = to_string_formula_prop  ((x1 ||. x2) &&. x3)
in assert_equal s "(P1 \\/ P2) /\\ P3"

let test_to_string_formula_impl test_ctxt = 
let s = to_string_formula_prop  (x1 =>. x2)
in assert_equal s "P1 => P2"

let test_to_string_formula_and_impl test_ctxt = 
let s = to_string_formula_prop  (x3 &&. (x1 =>. x2))
in assert_equal s "P3 /\\ (P1 => P2)"

(* Tests for printer_formula *)
let test_printer_formula_pvar test_ctxt = printer_formula_prop Format.str_formatter (x1);
let s = Format.flush_str_formatter()
in assert_equal s "P1"
                                                
let test_printer_formula_pneg test_ctxt = printer_formula_prop Format.str_formatter (neg x1);
let s = Format.flush_str_formatter()
in assert_equal s "!P1"

let test_printer_formula_pand test_ctxt = printer_formula_prop Format.str_formatter (x1 &&. x2);
let s = Format.flush_str_formatter()
in assert_equal s "P1 /\\ P2"

let test_printer_formula_por test_ctxt = printer_formula_prop Format.str_formatter (x1 ||. x2);
let s = Format.flush_str_formatter()
in assert_equal s "P1 \\/ P2"

let test_printer_formula_pand_por test_ctxt = printer_formula_prop Format.str_formatter ((x1 &&. x2) ||. x3);
let s = Format.flush_str_formatter()
in assert_equal s "(P1 /\\ P2) \\/ P3"

let test_printer_formula_por_pand test_ctxt = printer_formula_prop Format.str_formatter ((x1 ||. x2) &&. x3);
let s = Format.flush_str_formatter()
in assert_equal s "(P1 \\/ P2) /\\ P3"

let test_printer_formula_impl test_ctxt = printer_formula_prop Format.str_formatter (x1 =>. x2);
let s = Format.flush_str_formatter()
in assert_equal s "P1 => P2"

let test_printer_formula_and_impl test_ctxt = printer_formula_prop Format.str_formatter (x3 &&. (x1 =>. x2));
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
        run_test_tt_main prop_suite
;;

