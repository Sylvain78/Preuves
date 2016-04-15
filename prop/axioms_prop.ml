open Util
open Formula_prop

type axiom_prop =
  {
    name_axiom_prop : string;
    axiom_prop : formula_prop;
  }

let x1 = PVar (new_var())
and x2 = PVar (new_var())
and x3 = PVar (new_var());;

let a1 = x1 =>. (x2 =>. x1);;
let a2 = (x1 =>. (x2 =>. x3)) =>. ((x1 =>. x2) =>. (x1 =>. x3));;

let a3 = x1 =>. neg (neg x1);;
let a4 = neg (neg x1) =>. x1;;
let a5 = (x1 =>. x2) =>. (neg x2 =>. neg x1);;

let a6 = x1 =>. (x2 =>. (x1 &&. x2));;
let a7 = (x1 &&. x2) =>. x1;;
let a8 = (x1 &&. x2) =>. x2;;

let a9 = x1 =>. (x1 ||. x2);;
let a10 = x2 =>. (x1 ||. x2);;
let a11 = (neg x1) =>. ((x1 ||. x2) =>. x2);;

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
