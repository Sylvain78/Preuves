module type LOGIC = sig
  type kind = 
    | Axiom
    | Theorem
    | Assumed
  type formula
  type demonstration
  type theorem = {
    kind : kind; 
    name : string; 
    params : formula list;
    premisses : formula list;
    demonstration : demonstration;
    conclusion : formula; 
  }
  type step =  
    | Single of formula 
    | Call of {
        theorem : theorem;
        params :  formula list
      }
  val trans :step list -> demonstration
  val string_to_formula : string -> formula
  val formula_to_string : formula -> string
  val is_instance_axiom : formula -> bool
  val verif :
    ?is_axiom:(formula -> bool) ->
    ?theorems:theorem list ->
    ?hypotheses:formula list ->
    formula:formula ->
    proof:demonstration ->
    unit -> (unit, string) result
end
