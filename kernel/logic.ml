type speed =
  | Fast
  | Paranoid

type kind = 
  | Unproved
  | Invalid
  | Axiom
  | Theorem
  | Assumed

let kind_to_string = function
  | Unproved -> "Unproved"
  | Invalid -> "Invalid"
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
  type theorem_unproved = (formula, step list) theorem_logic
  val is_instance_axiom : formula -> bool
  val compile :
    speed:speed -> ?hypotheses:formula list -> demonstration:step list -> unit-> demonstration 
  val verif : speed:speed -> theorem_unproved -> 
    (theorem, string * exn) result
  exception Invalid_demonstration of theorem_unproved
  val print_invalid_demonstration : exn -> string option
  val string_to_formula : string -> formula
  val formula_to_string : formula -> string
  val printer_formula : Format.formatter -> formula -> unit
  val string_to_notation : string -> notation
  val printer_demonstration : Format.formatter -> demonstration -> unit
  val printer_step : Format.formatter -> step -> unit
end
