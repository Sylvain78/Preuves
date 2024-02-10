type speed =
  | Fast
  | Paranoid

type kind = 
  | Axiom
  | Theorem
  | Assumed
let kind_to_string = function
  | Axiom -> "Axiom"
  | Theorem -> "Theorem"
  | Assumed -> "Assumed"

type ('formula, 'demonstration) theorem_logic = {
  kind : kind; 
  name : string; 
  params : 'formula list;
  premisses : 'formula list;
  demonstration : 'demonstration;
  conclusion : 'formula; 
}

module type LOGIC = sig
  type formula
  type notation
  type demonstration
  type theorem = (formula, demonstration) theorem_logic
  val axioms : theorem list ref
  val add_axiom : theorem -> unit
  val theorems : theorem list ref

  type step =  
    | Single of formula 
    | Call of 
        {
          theorem : theorem;
          params :  formula list
        }

  (*val trans : step list -> demonstration*)
  val is_instance_axiom : formula -> bool
  val compile :
    speed:speed -> step list -> demonstration 
  val verif :
    ?theorems:theorem list -> 
    ?hypotheses:formula list -> unit ->
    formula:formula ->
    proof:demonstration ->
    (unit, string * exn) result
  exception Invalid_demonstration of formula * theorem list * formula list * demonstration
  val print_invalid_demonstration : exn -> string option
  val string_to_formula : string -> formula
  val formula_to_string : formula -> string
  val printer_formula : Format.formatter -> formula -> unit
  val string_to_notation : string -> notation
  val printer_demonstration : Format.formatter -> demonstration -> unit
end
