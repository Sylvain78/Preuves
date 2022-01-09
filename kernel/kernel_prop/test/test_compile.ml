open Prop.Formula_prop
open Prop.Verif
open OUnit2

open Kernel_prop.Compile
open Kernel_prop.Verif

let x1,x2,x3 = PVar 1,PVar 2, PVar 3
let (=>) a b = PImpl(a,b)
let formula = x1=>x1


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
  let verif = (prop_proof_verif ~hyp:(List.map Prop.Verif.formula_from_string [])
                 chaining
                 ~proof:demo_chaining)          
  in
  if verif then
      theorems_prop :=
        {
          kind_prop = Prop.Kind_prop.Theorem;
          name_theorem_prop = "C6";
          proof_prop = demo_chaining;
          conclusion_prop = chaining;
        }
        :: !theorems_prop
;;


let demo =
  [ 
    (x1 =>((x1 => x1) => x1)) =>((x1 =>(x1 => x1)) =>(x1 => x1));
    x1 =>((x1 => x1) => x1);
    (x1 =>(x1 => x1)) =>(x1 => x1);
    x1 =>(x1 => x1);
    x1 => x1
  ]

let test = compile_demonstration ~theory:[] ~demo ();;

let test_cut _ =
  assert_equal {theorem=x2 ; demonstration=[Known 1 ; Known 2 ; Cut(1,2)]}
    (compile_demonstration ~demo:[x1; x1=>x2 ; x2] ~theory:[x1;x1=>x2] ())

let test_compile _ =
  assert_equal { theorem=formula ; demonstration=[ Known 1 ] }
    (compile_demonstration ~demo:[formula] ~theory:[formula] ())

let test_compile_a_implies_a _ =
  assert_equal 
    { theorem = formula ; 
      demonstration = [Ax (2, [(3, x1); (1, x1); (2, x1 => x1)]);
                       Ax (1, [(1, x1); (2, x1 => x1)]);
                       Cut (2, 1);
                       Ax (1, [(1, x1); (2, x1)]);
                       Cut (4, 3)
                      ]
    }

    (compile_demonstration ~demo:demo ())

let test_compile_s1 _ =
  let demo_chaining x1 x2 x3 = 
    [
      (x1 => (x2 => x3)) => ((x1 => x2) => (x1 => x3));
      ((x1 => (x2 => x3)) => ((x1 => x2) => (x1 => x3))) => ((x2 => x3) => ((x1 => (x2 => x3)) => ((x1 => x2) => (x1 => x3))));
      ((x2 => x3) => ((x1 => (x2 => x3)) => ((x1 => x2) => (x1 => x3))));
      ((x2 => x3) => ((x1 => (x2 => x3)) => ((x1 => x2) => (x1 => x3)))) => (((x2 => x3) => (x1 => (x2 => x3))) => ((x2 => x3) => ((x1 => x2) => (x1 => x3))));
      (((x2 => x3) => (x1 => (x2 => x3))) => ((x2 => x3) => ((x1 => x2) => (x1 => x3))));
      ((x2 => x3) =>  (x1 => (x2 => x3)));
      ((x2 => x3) => ((x1 => x2) => (x1 => x3)));
      ((x2 => x3) => ((x1 => x2) => (x1 => x3))) => (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3)));
      (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3)));
      (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3))) => ((x1 => x2) => (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3))));
      ((x1 => x2) => (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3))));

      (*k*)
      ((x1 => x2) => ((x2 => x3) => (x1 => x2)));

      (*s*)
      ((x1 => x2) => (((x2 => x3) => (x1 => x2)) => ((x2 => x3) => (x1 => x3))))  => 
      (((x1 => x2) => ((x2 => x3) => (x1 => x2))) => ((x1 => x2) => ((x2 => x3) => (x1 => x3))));

      ((x1 => x2) => ((x2 => x3) => (x1 => x2))) => ((x1 => x2) => ((x2 => x3) => (x1 => x3)));
      ((x1 => x2) => ((x2 => x3) => (x1 => x3)))
    ] 
  in
  let _ = Prop.Prop_parser.notation_from_string "Notation\nimply\nParam\na b\nSyntax\na \"=>\" b\nSemantics\n\"(\"a\")\" \"\\implies\" \"(\"b\")\"\nEnd"
  and demo = compile_demonstration ~demo:((List.map Prop.Prop_parser.formula_from_string [
      "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))";
      "((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
      "((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "(((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))) \\implies (((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";
      "(((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies  ((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))) \\implies (((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";
      "(((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";
      "(((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";
      "(((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";

      (*k*)
      "(((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))))";

      (*s*)
      "(((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))  \\implies ((((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))))";

      "(((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";
      "(((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))))";

      "((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
      "((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "((\\lnot \\mathbf{A})  \\implies (((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A})) \\implies (\\lnot \\mathbf{A})))  \\implies (( (\\lnot \\mathbf{A})  \\implies  ((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A})))  \\implies  ((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A})))";
      "(\\lnot \\mathbf{A}) \\implies (((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})) \\implies (\\lnot \\mathbf{A}))";
      "((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A})  \\implies  (\\lnot \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A}))";
      "(\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A}))";
      "(\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})";
      "(((\\lnot \\mathbf{A}) \\implies (\\lnot \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))";

      (* nA -> nB ---> A->B *)
      "((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})";
      "((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}))";
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})";

      (*chaining*)    
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))) \\implies ((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";
      "((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies  ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})))";
      "(((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "(((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))) \\implies ((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";

      (*k*)
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))))";

      (*s*)
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))  \\implies 
    ((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))))";

      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      (*end chaining*)    

      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))  \\implies (((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}))) \\implies ((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})))";
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})";
      "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))";
      "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))))";
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))"; ]) @ (demo_chaining (POr(PMetaVar "A", PMetaVar "A")) (PNeg(PNeg(POr(PMetaVar "A", PMetaVar "A")))) (PMetaVar "A")) @ (List.map formula_from_string [

      (* Demonstrated by chaining :
       * "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
      *)
      "(((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies  (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))))  \\implies  ((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))";
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))";
      "(((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies \\mathbf{A})) \\implies (((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
      "((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})";
      "(((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies  ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))))";
    ]) 
                                          @ (demo_chaining (formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))") (formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})") (formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")) 
                                          @ (demo_chaining (formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))") (formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})") (formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")) 
                                          @ 
                                          (List.map formula_from_string [
                                              "(((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies  ((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A})))) \\implies ((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))";

                                              "((((\\lnot (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (\\lnot (\\lnot \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))";
                                              "(((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))";
                                              (* nA -> nB ---> A->B *)

                                              "((\\lnot \\mathbf{A}) \\implies (\\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})";
                                              "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}"
                                            ])) ()
  in
  assert_equal ~printer:(fun s -> Format.pp_print_list (printer_kernel_proof_term) Format.str_formatter s.demonstration; Format.flush_str_formatter ())
    {theorem =
       PImpl
         (POr (PMetaVar "A",
               PMetaVar "A"),
          PMetaVar "A");
     demonstration = 
       [
         Ax(5,[(1,formula_from_string "\\mathbf{A} \\lor \\mathbf{A}");(2,formula_from_string "\\mathbf{A}")]);
         Ax(11,[(2,formula_from_string "\\mathbf{A}");(1,formula_from_string "\\mathbf{A}")]);
         Ax(2,[(3,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "((\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))) \\implies (((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))");(2,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))")]);
         Cut(3,4);
         Ax(2,[(3,formula_from_string "((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))");(1,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))")]);
         Cut(5,6);
         Ax(1,[(1,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))");(2,formula_from_string "\\lnot \\mathbf{A}")]);
         Cut(8,7);
         Ax(2,[(3,formula_from_string "(\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))");(1,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Cut(9,10);
         Ax(1,[(1,formula_from_string "((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))))");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Cut(11,12);
         Ax(1,[(1,formula_from_string "(\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))")]);
         Ax(2,[(3,formula_from_string "(((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})))");(1,formula_from_string "(\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "(((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies ((\\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))")]);
         Cut(13,15);
         Cut(14,16);
         Cut(14,16);
         Cut(2,17);
         Cut(1,19);
         Ax(2,[(3,formula_from_string "\\lnot (\\mathbf{A} \\lor \\mathbf{A})");(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "\\lnot \\mathbf{A}")]);
         Ax(2,[(3,formula_from_string "\\lnot \\mathbf{A}");(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot \\mathbf{A}")]);
         Cut(23,22);
         Ax(1,[(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "\\lnot \\mathbf{A}")]);
         Cut(25,24);
         Cut(20,21);
         Cut(26,27);
         Ax(4,[(1,formula_from_string "\\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Cut(29,30);
         Ax(2,[(3,formula_from_string "\\mathbf{A}");(1,formula_from_string "\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "\\lnot \\lnot \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}))");(2,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}")]);
         Cut(32,33);
         Ax(2,[(3,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A})");(1,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A})")]);
         Cut(34,35);
         Ax(1,[(1,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}");(2,formula_from_string "\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(37,36);
         Ax(2,[(3,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Cut(38,39);
         Ax(1,[(1,formula_from_string "(((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})) \\implies (((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}))");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Cut(40,41);
         Ax(1,[(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}")]);
         Ax(2,[(3,formula_from_string "((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A})");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}");(2,formula_from_string "((\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})")]);
         Cut(42,44);
         Cut(43,45);
         Ax(2,[(3,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot \\mathbf{A}) \\implies \\mathbf{A}")]);
         Cut(46,47);
         Cut(29,38);
         Ax(3,[(1,formula_from_string "\\mathbf{A} \\lor \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Cut(50,51);
         Ax(2,[(3,formula_from_string "\\mathbf{A}");(1,formula_from_string "\\mathbf{A} \\lor \\mathbf{A}");(2,formula_from_string "\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Ax(1,[(1,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A})) \\implies (((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}")]);
         Cut(53,54);
         Ax(2,[(3,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}");(2,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A})")]);
         Cut(55,56);
         Ax(1,[(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}");(2,formula_from_string "\\mathbf{A} \\lor \\mathbf{A}")]);
         Cut(58,57);
         Ax(2,[(3,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}");(2,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(59,60);
         Ax(1,[(1,formula_from_string "(((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A}))) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(2,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(61,62);
         Ax(1,[(1,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}")]);
         Ax(2,[(3,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(1,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A}))")]);
         Cut(63,65);
         Cut(64,66);
         Ax(1,[(1,formula_from_string "((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Cut(67,68);
         Ax(2,[(3,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}");(2,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(69,70);
         Cut(52,71);
         Ax(2,[(3,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\mathbf{A}")]);
         Cut(72,73);
         Cut(49,74);
         Ax(5,[(1,formula_from_string "\\lnot \\mathbf{A}");(2,formula_from_string "\\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Ax(2,[(3,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "(((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))");(2,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Cut(77,78);
         Ax(2,[(3,formula_from_string "(((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))")]);
         Cut(79,80);
         Ax(1,[(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(82,81);
         Ax(2,[(3,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})")]);
         Cut(83,84);
         Ax(1,[(1,formula_from_string "((((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}))) \\implies ((((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})")]);
         Cut(85,86);
         Ax(1,[(1,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})");(2,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Ax(2,[(3,formula_from_string "(((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(1,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})");(2,formula_from_string "(((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}))")]);
         Cut(87,89);
         Cut(88,90);
         Ax(2,[(3,formula_from_string "(\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}");(1,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})");(2,formula_from_string "(\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}")]);
         Ax(1,[(1,formula_from_string "(((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))) \\implies ((((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))");(2,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Cut(77,78);
         Ax(2,[(3,formula_from_string "(((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies (((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))")]);
         Cut(79,80);
         Ax(1,[(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "(\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})")]);
         Cut(82,81);
         Ax(2,[(3,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(1,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})")]);
         Cut(83,84);
         Ax(1,[(1,formula_from_string "((((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}))) \\implies ((((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})))");(2,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})")]);
         Cut(85,86);
         Ax(1,[(1,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})");(2,formula_from_string "((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})")]);
         Ax(2,[(3,formula_from_string "(((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A}))");(1,formula_from_string "((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A})");(2,formula_from_string "(((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}) \\implies ((\\mathbf{A} \\lor \\mathbf{A}) \\implies \\mathbf{A})) \\implies (((\\lnot \\mathbf{A}) \\implies \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies ((\\lnot \\lnot (\\mathbf{A} \\lor \\mathbf{A})) \\implies \\lnot \\lnot \\mathbf{A}))")]);
         Cut(87,89);
         Cut(88,90);
         Cut(88,90);
         Cut(76,91);
         Cut(75,108);
         Cut(75,108);
         Cut(28,109);
       ]
    }
    demo

let compile_suite =
  "compile test" >:::
  [ 
    "test cut" >:: test_cut;
    "test compile" >:: test_compile;
    "test_compile_a_implies_a" >:: test_compile_a_implies_a;
    "test_compile_s1" >:: test_compile_s1;
  ]

let () = 
  run_test_tt_main compile_suite
