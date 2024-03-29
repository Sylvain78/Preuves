type notation_prop_element = Param of string | String of string

type formula_prop =
  | PVar of int
  | PMetaVar of string
  | PNeg of formula_prop
  | PAnd of formula_prop * formula_prop
  | POr of formula_prop * formula_prop
  | PImpl of formula_prop * formula_prop
  | PApply_notation of apply_notation_prop
and apply_notation_prop =
  {
    apply_notation_prop : notation_prop;
    apply_notation_prop_params : formula_prop list; (*SKE TODO create database of notations*)
  }
and notation_prop =
  {
    notation_prop_name : string;
    notation_prop_params : notation_prop_element list;
    notation_prop_notation : notation_prop_element list;
    notation_prop_semantique : notation_prop_element list;
  }  

type phrase = 
  | F of formula_prop
  | N of notation_prop

(*SKE Example of notation
  "
  Notation equiv
  Params a b
  a \equiv b 
  (a \imply b)\\land(b \imply a)
  End
  "
*)

