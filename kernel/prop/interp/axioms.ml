open Theorem_prop
open Kernel.Logic

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

let (axioms_prop: theorem_prop list ref) = ref [
    Theorem {
      kind=KAxiom;
      name="A1";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a1;
    };
    Theorem {
      kind=KAxiom;
      name="A2";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a2;
    };
    Theorem {
      kind=KAxiom;
      name="A3";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a3;
    };
    Theorem {
      kind=KAxiom;
      name="A4";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a4;
    };
    Theorem {
      kind=KAxiom;
      name="A5";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a5;
    };
    Theorem {
      kind=KAxiom;
      name="A6";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a6;
    };
    Theorem {
      kind=KAxiom;
      name="A7";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a7;
    };
    Theorem {
      kind=KAxiom;
      name="A8";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a8;
    };
    Theorem {
      kind=KAxiom;
      name="A9";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a9;
    };
    Theorem {
      kind=KAxiom;
      name="A10";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a10;
    };
    Theorem {
      kind=KAxiom;
      name="A11";
      params= [];
      premisses=[];
      demonstration= Demonstration [];
      conclusion=a11;
    };
  ];;
