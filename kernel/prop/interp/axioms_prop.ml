open Theorem_prop

let a1 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies X_1)";;
let a2 = Prop_parser.formula_from_string "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";;

let a3 = Prop_parser.formula_from_string "X_1 \\implies \\lnot \\lnot X_1";;
let a4 = Prop_parser.formula_from_string "(\\lnot \\lnot X_1) \\implies X_1";;
let a5 = Prop_parser.formula_from_string "(X_1 \\implies X_2) \\implies ((\\lnot X_2) \\implies \\lnot X_1)";;

let a6 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies (X_1 \\land X_2))";;
let a7 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_1";;
let a8 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_2";;

let a9  = Prop_parser.formula_from_string "X_1 \\implies (X_1 \\lor X_2)";;
let a10 = Prop_parser.formula_from_string "X_2 \\implies (X_1 \\lor X_2)";;
let a11 = Prop_parser.formula_from_string "(\\lnot X_1) \\implies ((X_1 \\lor X_2) \\implies X_2)";;

let axioms_prop = ref [
    {
      kind_prop=Axiom;
      name_theorem_prop="A1";
      proof_prop=[];
      conclusion_prop=a1;
    };
    {
      kind_prop=Axiom;
      name_theorem_prop="A2";
      proof_prop=[];
      conclusion_prop=a2;
    };
    {
      kind_prop=Axiom;
      name_theorem_prop="A3";
      proof_prop=[];
      conclusion_prop=a3;
    };
    {
      kind_prop=Axiom;
    name_theorem_prop="A4";
    proof_prop=[];
    conclusion_prop=a4;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A5";
    proof_prop=[];
    conclusion_prop=a5;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A6";
    proof_prop=[];
    conclusion_prop=a6;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A7";
    proof_prop=[];
    conclusion_prop=a7;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A8";
    proof_prop=[];
    conclusion_prop=a8;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A9";
    proof_prop=[];
    conclusion_prop=a9;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A10";
    proof_prop=[];
    conclusion_prop=a10;
  };
  {
    kind_prop=Axiom;
    name_theorem_prop="A11";
    proof_prop=[];
    conclusion_prop=a11;
  };
];;
