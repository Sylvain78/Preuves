module Formula_Prop :
  sig
    val name : string
    type formula =
        PVar of int
      | PNeg of formula
      | PAnd of formula * formula
      | POr of formula * formula
      | PImpl of formula * formula
    val parser : (string -> formula) option ref
    val of_string : (string -> formula)
    val to_string : (formula -> string)
    val c1 : formula -> int
    val a : formula
    val b : formula
    val c : formula
    val d : formula
  end
module Prop :
  sig
    val name : string
    type formula = Formula_Prop.formula
    type demonstration
    type rule
    val rules : rule list
    val axiom : string -> formula Logic2.family
    val heuristic_proof :
      ?premisses:formula Logic2.family -> formula -> demonstration option
    val verification : demonstration -> bool
  end