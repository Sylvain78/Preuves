(** 1   General definitions of logic. *)

type 'a family = 'a -> bool

let empty_family = function _ -> false

(** module types **)
module type SIGNATURE = sig
  val name : string

  type symbol
  val of_string : string -> symbol
  val to_string: symbol -> string

  val constants : symbol family
  val relations : (symbol * int) family
  val operations : (symbol * int) family
  val binder : symbol family
  val new_symbol : unit -> symbol
end

module type LANGUAGE = sig
  val name : string

  type formula

  val of_string : string -> formula
  val to_string : formula -> string
end

module type LOGIC = sig
  val name : string

  type formula
  type demonstration
  type rule 
  val rules : rule list
  (* axiom can be explicit or implicit*)
  val axiom : string -> (formula family)

  val heuristic_proof :
    ?premisses:formula family -> formula -> demonstration option

  val verification : demonstration -> bool
end

