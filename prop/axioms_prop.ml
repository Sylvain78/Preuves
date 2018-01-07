open Util
open Formula_prop

type axiom_prop =
  {
    name_axiom_prop : string;
    axiom_prop : formula_prop;
  }

let a1 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies X_1)";;
let a2 = Prop_parser.formula_from_string "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";;

let a3 = Prop_parser.formula_from_string "X_1 \\implies \\lnot (\\lnot X_1)";;
let a4 = Prop_parser.formula_from_string "\\lnot (\\lnot X_1) \\implies X_1";;
let a5 = Prop_parser.formula_from_string "(X_1 \\implies X_2) \\implies (\\lnot X_2 \\implies \\lnot X_1)";;

let a6 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies (X_1 \\land X_2))";;
let a7 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_1";;
let a8 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_2";;

let a9 = Prop_parser.formula_from_string "X_1 \\implies (X_1 \\lor X_2)";;
let a10 = Prop_parser.formula_from_string "X_2 \\implies (X_1 \\lor X_2)";;
let a11 = Prop_parser.formula_from_string "(\\lnot X_1) \\implies ((X_1 \\lor X_2) \\implies X_2)";;

let axioms_prop = [
  {
    name_axiom_prop="A1";
    axiom_prop=a1;
  };
  {
    name_axiom_prop="A2";
    axiom_prop=a2;
  };
  {
    name_axiom_prop="A3";
    axiom_prop=a3;
  };
  {
    name_axiom_prop="A4";
    axiom_prop=a4;
  };
  {
    name_axiom_prop="A5";
    axiom_prop=a5;
  };
  {
    name_axiom_prop="A6";
    axiom_prop=a6;
  };
  {
    name_axiom_prop="A7";
    axiom_prop=a7;
  };
  {
    name_axiom_prop="A8";
    axiom_prop=a8;
  };
  {
    name_axiom_prop="A9";
    axiom_prop=a9;
  };
  {
    name_axiom_prop="A10";
    axiom_prop=a10;
  };
  {
    name_axiom_prop="A11";
    axiom_prop=a11;
  };
];;
