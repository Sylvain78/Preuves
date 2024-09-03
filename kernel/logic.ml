type keep_calls =
  | Keep_calls
  | Expand_calls

type kind =
  | KUnproved
  | KInvalid
  | KAxiom
  | KTheorem
  | KAssumed

let kind_to_string = function
  | KUnproved -> "Unproved"
  | KInvalid -> "Invalid"
  | KAxiom -> "Axiom"
  | KTheorem -> "Theorem"
  | KAssumed -> "Assumed"

type ('formula, 'demonstration) theorem_logic = {
  kind : kind;
  name : string;
  params : 'formula list;
  premisses : 'formula list;
  demonstration : 'demonstration;
  conclusion : 'formula;
}

module type THEOREMS = sig
  type t
  val theorems : t Dynarray.t
  val get_theorems : unit -> t list
  val add_theorem : t -> unit
  val find_by_name : name:string -> (t * int)
end

module type LOGIC = sig
  type formula
  type notation
  type demonstration
  and  theorem = Theorem of (formula, demonstration) theorem_logic [@@unboxed]
  and  step =
    | Single of formula
    | Call of
        {
          theorem : theorem;
          params :  formula list
        }
  module Theorems : (THEOREMS with type t = theorem)
  (*
  =
  struct
    type theorem
    let (theorems : theorem Dynarray.t) = Dynarray.create()
    let get_theorems () = Dynarray.to_list theorems
    let add_theorem th = Dynarray.add_last theorems th
    let find_by_name ~name =
      let limit = Dynarray.length theorems - 1
      in
      let rec find_aux index  =
        if (index > limit)
        then
          None
        else
          let theorem = Dynarray.get theorems index
          in
          if theorem.name = name
          then
            Some (theorem,index)
          else
            find_aux (index+1)
      in
      find_aux name 0 length
  end
  *)

  val empty_demonstration : demonstration
  val is_formula_at_end : formula -> step list -> bool
  val axioms : theorem list ref
  val add_axiom : theorem -> unit
  type theorem_unproved = (formula, step list) theorem_logic
  val is_instance_axiom : formula -> bool
  val compile :
    keep_calls:keep_calls -> ?hypotheses:formula list -> demonstration:step list -> unit-> demonstration
  val verif : keep_calls:keep_calls -> theorem_unproved ->
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
