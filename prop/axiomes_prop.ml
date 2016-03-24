open Util
open Formule_prop

type axiome_prop =
	{
	 nom_axiome_prop : string;
	 axiome_prop : pformule;
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

let axiomes_prop = [
	{
	 nom_axiome_prop="A1";
	 axiome_prop=a1;
	};
	{
	 nom_axiome_prop="A2";
	 axiome_prop=a2;
	};
	{
	 nom_axiome_prop="A3";
	 axiome_prop=a3;
	};
	{
	 nom_axiome_prop="A4";
	 axiome_prop=a4;
	};
	{
	 nom_axiome_prop="A5";
	 axiome_prop=a5;
	};
	{
	 nom_axiome_prop="A6";
	 axiome_prop=a6;
	};
	{
	 nom_axiome_prop="A7";
	 axiome_prop=a7;
	};
	{
	 nom_axiome_prop="A8";
	 axiome_prop=a8;
	};
	{
	 nom_axiome_prop="A9";
	 axiome_prop=a9;
	};
	{
	 nom_axiome_prop="A10";
	 axiome_prop=a10;
	};
	{
	 nom_axiome_prop="A11";
	 axiome_prop=a11;
	};
	];;
