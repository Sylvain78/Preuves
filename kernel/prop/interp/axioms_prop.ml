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
      kind=Axiom;
      name="A1";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a1;
    };
    {
      kind=Axiom;
      name="A2";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a2;
    };
    {
      kind=Axiom;
      name="A3";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a3;
    };
    {
      kind=Axiom;
      name="A4";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a4;
    };
    {
      kind=Axiom;
      name="A5";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a5;
    };
    {
      kind=Axiom;
      name="A6";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a6;
    };
    {
      kind=Axiom;
      name="A7";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a7;
    };
    {
      kind=Axiom;
      name="A8";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a8;
    };
    {
      kind=Axiom;
      name="A9";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a9;
    };
    {
      kind=Axiom;
      name="A10";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a10;
    };
    {
      kind=Axiom;
      name="A11";
      params= [];
      premisses=[];
      demonstration=[];
      conclusion=a11;
    };
  ];;
