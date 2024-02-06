 module P = Kernel_prop_interp.Theory.Prop
open Kernel_prop_interp.Formula_prop

let neg p = PNeg p
and (=>.) a b = PImpl(a,b)
and (||.) a b = POr(a,b)
(*let notation = notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\implies\" \"(\"b\")\"\nEnd";;*)
let x1,x2,x3 = PVar 1, PVar 2, PVar 3
let a,b=x1,x2
let tout = neg (a=>.a)
and a_ou_b = (a||.b)
and b_ou_a = ( b||.a)
let c = b_ou_a
let a_entraine_c = (a=>.c)
and b_entraine_c = (b=>.c)


(* |   F \\implies  F *)
let verif_C8 =
  let demo = [
    (a =>. ((a =>. a) =>. a)) =>. (( a =>. (a =>. a)) =>. (a =>. a));
    a =>. ((a =>. a) =>. a);
    (a =>. (a =>. a)) =>. (a =>. a);
    a =>. (a =>. a);
    a =>. a;
  ]
  in
  match (P.verif  ~formula:(a=>. a) ~proof:(demo: P.demonstration) ())
  with 
  |Ok() ->  
    P.theorems := {
      kind = Theorem;
      name="[Bourbaki]C8";
      params = [];
      premisses = [];
      demonstration = demo;
      conclusion = P.string_to_formula  "X_1 \\implies X_1";
    }::!P.theorems 
 | Error _ -> ()

let add_chaining =
  let chaining =
    P.string_to_formula "((X_1 \\implies X_2) \\implies ((X_2 \\implies X_3) \\implies (X_1 \\implies X_3)))"
  in
  let demo_chaining = 
    List.map (fun s -> P.string_to_formula s) [
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
  match (P.verif  ~formula:chaining ~proof:demo_chaining ())          
  with
  | Ok () -> 
    P.theorems :=
      {
        kind = Kernel_prop_interp.Theory.Prop.Theorem;
        name = "C6";
        params = [];
        premisses = [];
        demonstration = demo_chaining;
        conclusion = chaining;
      }
      :: !P.theorems
  | Error _ -> ()
;;
(*non A  \\implies  non B |   B  \\implies  A*)
(* TODO : delete once they are not needed anymore
   let h = ((\\lnot (\\lnot X_2)) \\implies (\\lnot (\\lnot X_1)))	
   and ((\\lnot (\\lnot X_1)) \\implies X_1) =((\\lnot (\\lnot X_1)) \\implies  X_1)
   and ((\\lnot (\\lnot X_2)) \\implies X_1) = ((\\lnot (\\lnot X_2)) \\implies  X_1)	
   and (X_2 \\implies \\lnot (\\lnot X_2))=	(X_2 \\implies \\lnot (\\lnot X_2))
   in
*)
match
  P.verif  ~theorems:!P.theorems ~formula:(P.string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))") ()
    ~proof:(List.map (fun s -> P.string_to_formula s) [

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
      ])
with 
| Ok() ->  
  P.theorems := {
    kind = Kernel_prop_interp.Kind_prop.Assumed;
    name ="contraposition";
    params = [];
    premisses = [];
    demonstration = [];
    conclusion = P.string_to_formula "(((\\lnot X_1) \\implies (\\lnot X_2)) \\implies (X_2 \\implies X_1))";}
    ::!P.theorems
| Error _ -> ()
;;



(* |   F ou F  \\implies  F *)
let demo = (List.map (fun s -> P.string_to_formula s) [
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
  ])
in
match P.verif  ~theorems:!P.theorems ~formula:(P.string_to_formula "(\\mathbf{A} \\lor \\mathbf{A})  \\implies  \\mathbf{A}")
    ~proof:demo ()
with 
| Ok() ->
  P.theorems := {
    kind = Assumed;
    name="[Bourbaki]S1";
    params = [];
    premisses = [];
    demonstration = demo;
    conclusion=P.string_to_formula "(X_1 \\lor X_1) \\implies X_1";
  }::!P.theorems 
| Error _ -> ()

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
  [
    a=>.a;
    (a=>.a) =>. (neg tout);
    (*neg tout*)
    (neg tout);
    (neg tout)=>.(b_entraine_c=>. neg tout);
    (b_entraine_c=>. neg tout);
    (b_entraine_c=>. neg tout)=>.(a_entraine_c=>.(b_entraine_c=>. neg tout));
    (a_entraine_c=>.(b_entraine_c=>. neg tout));
    (a_entraine_c=>.(b_entraine_c=>. neg tout))=>.  (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));
    (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>. neg tout)));

    (*a_ou_b;*)
    (*a_ou_b=>.((neg c)=>.a_ou_b);*)
    a_ou_b=>.((neg c)=>.a_ou_b);

    (*((neg c)=>.a_ou_b);*)
    ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b));

    (((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))=>. 
    (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

    (a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
    ((a_ou_b =>.( ((neg c) =>. a_ou_b) =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))))=>.
    ((a_ou_b =>. ((neg c) =>. a_ou_b))=>. (a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));

    (a_ou_b=>.((neg c)=>.a_ou_b))=>.  (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

    (a_ou_b=>.(b_entraine_c=>.((neg c)=>.a_ou_b)));

    ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))));
    ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))) =>. (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
    (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
    (a_ou_b =>. ((b_entraine_c =>. ((neg c) =>. a_ou_b)) =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))))) =>. ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));
    ((a_ou_b =>. (b_entraine_c =>. ((neg c) =>. a_ou_b))) =>. (a_ou_b =>. (a_entraine_c =>. (b_entraine_c =>. ((neg c) =>. a_ou_b)))));

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
  ];;

(*let verif_ou_diamant =
  (prop_proof_kernel_verif ~hyp:[] (a_ou_b=>.(a_entraine_c=>.(b_entraine_c=>.c)))
     ~proof:demo);;
*)
let demo1 = demo @ [
    (a_ou_b=>. (a_entraine_c=>.(b_entraine_c=>.c))) =>.
    ((a_ou_b =>. a_entraine_c) =>. (a_ou_b =>.(b_entraine_c=>.c)));
    ((a_ou_b =>. a_entraine_c) =>. (a_ou_b =>.(b_entraine_c=>.c)));

    a_entraine_c;
    a_entraine_c =>. ( a_ou_b =>. a_entraine_c);
    ( a_ou_b =>. a_entraine_c);
    (a_ou_b =>.(b_entraine_c=>.c));
    (a_ou_b =>.(b_entraine_c=>.c)) =>. ((a_ou_b =>. b_entraine_c) =>. (a_ou_b =>. c));

    ((a_ou_b =>. b_entraine_c) =>. (a_ou_b =>. c));

    b_entraine_c;
    b_entraine_c =>.((a_ou_b =>. b_entraine_c));
    ((a_ou_b =>. b_entraine_c));

    a_ou_b =>. c;];;

let verif_S3 = 
  (P.verif  ~theorems:!P.theorems ~formula:(a_ou_b=>. c) ~proof:demo1 ())
;;
