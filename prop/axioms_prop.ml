open Formula_prop

type proposition_prop =
  {
    name_proposition_prop : string;
    proposition_prop : formula_prop;
  }

let a1 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies X_1)";;
let a2 = Prop_parser.formula_from_string "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))";;

let a3 = Prop_parser.formula_from_string "X_1 \\implies \\lnot \\lnot X_1";;
let a4 = Prop_parser.formula_from_string "(\\lnot \\lnot X_1) \\implies X_1";;
let a5 = Prop_parser.formula_from_string "(X_1 \\implies X_2) \\implies ((\\lnot X_2) \\implies \\lnot X_1)";;

let a6 = Prop_parser.formula_from_string "X_1 \\implies (X_2 \\implies (X_1 \\land X_2))";;
let a7 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_1";;
let a8 = Prop_parser.formula_from_string "(X_1 \\land X_2) \\implies X_2";;

let a9 = Prop_parser.formula_from_string "X_1 \\implies (X_1 \\lor X_2)";;
let a10 = Prop_parser.formula_from_string "X_2 \\implies (X_1 \\lor X_2)";;
let a11 = Prop_parser.formula_from_string "(\\lnot X_1) \\implies ((X_1 \\lor X_2) \\implies X_2)";;

let axioms_prop = ref [
  {
    name_proposition_prop="A1";
    proposition_prop=a1;
  };
  {
    name_proposition_prop="A2";
    proposition_prop=a2;
  };
  {
    name_proposition_prop="A3";
    proposition_prop=a3;
  };
  {
    name_proposition_prop="A4";
    proposition_prop=a4;
  };
  {
    name_proposition_prop="A5";
    proposition_prop=a5;
  };
  {
    name_proposition_prop="A6";
    proposition_prop=a6;
  };
  {
    name_proposition_prop="A7";
    proposition_prop=a7;
  };
  {
    name_proposition_prop="A8";
    proposition_prop=a8;
  };
  {
    name_proposition_prop="A9";
    proposition_prop=a9;
  };
  {
    name_proposition_prop="A10";
    proposition_prop=a10;
  };
  {
    name_proposition_prop="A11";
    proposition_prop=a11;
  };
];;
