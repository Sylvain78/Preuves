module type LOGIC = sig
  type kind = 
    | Axiom
    | Theorem
    | Assumed
  type formula
  type notation
  type demonstration
  type theorem = {
    kind : kind; 
    name : string; 
    params : formula list;
    premisses : formula list;
    demonstration : demonstration;
    conclusion : formula; 
  }

  val axioms : theorem list
  val theorems : theorem list ref

  type step =  
    | Single of formula 
    | Call of {
        theorem : theorem;
        params :  formula list
      }
  val trans : step list -> demonstration
  val string_to_formula : string -> formula
  val formula_to_string : formula -> string
  val string_to_notation : string -> notation
  val is_instance_axiom : formula -> bool
  val verif :
    ?theorems:theorem list -> 
    ?hypotheses:formula list -> unit ->
    formula:formula ->
    proof:demonstration ->
    (unit, string) result
  exception Invalid_demonstration of formula * theorem list * formula list * demonstration
    end
