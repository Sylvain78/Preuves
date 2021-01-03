open Kernel_theorem_prop

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
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A1";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a1;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A2";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a2;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A3";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a3;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A4";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a4;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A5";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a5;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A6";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a6;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A7";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a7;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A8";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a8;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A9";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a9;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A10";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a10;
  };
  {
    kernel_kind_prop=Axiom;
    kernel_name_theorem_prop="A11";
    kernel_proof_prop=[];
    kernel_conclusion_prop=a11;
  };
];;
