open Base_term

module Formula :
  functor (Sig : Signature.SIGNATURE) ->
    sig
      type var = Term(Sig).var =
        | Var of int
        | Metavar of string
      type term = Term(Sig).term =
        | V of var
        | Constant of Sig.symbol
        | Operation of Sig.symbol * term list
      val printers_constants :
        (Sig.symbol, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
      val compare_var : var -> var -> int
      module SetVar :
        sig
          type elt = var
          type t = Term(Sig).SetVar.t
          val empty : t
          val is_empty : t -> bool
          val mem : elt -> t -> bool
          val add : elt -> t -> t
          val singleton : elt -> t
          val remove : elt -> t -> t
          val union : t -> t -> t
          val inter : t -> t -> t
          val diff : t -> t -> t
          val compare : t -> t -> int
          val equal : t -> t -> bool
          val subset : t -> t -> bool
          val iter : (elt -> unit) -> t -> unit
          val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
          val for_all : (elt -> bool) -> t -> bool
          val exists : (elt -> bool) -> t -> bool
          val filter : (elt -> bool) -> t -> t
          val partition : (elt -> bool) -> t -> t * t
          val cardinal : t -> int
          val elements : t -> elt list
          val min_elt : t -> elt
          val max_elt : t -> elt
          val choose : t -> elt
          val split : elt -> t -> t * bool * t
          val find : elt -> t -> elt
          val of_list : elt list -> t
        end
      val variables_term : term -> SetVar.t
      val simultaneous_substitution_term : var list -> term list -> term -> term
      type substitution = term -> term
      val print_term : Format.formatter -> term -> unit
      type atomic_formula =
          Eq of term * term
        | Relation of Sig.symbol * term list
      val printers_relations :
        (Sig.symbol, Format.formatter -> atomic_formula -> unit) Hashtbl.t
      type formula =
          Atomic_formula of atomic_formula
        | Neg of formula
        | And of formula * formula
        | Or of formula * formula
        | Imply of formula * formula
        | Exists of var * formula
        | Forall of var * formula
      val equiv : formula -> formula -> formula
      exception Failed_unification_atomic_formula of atomic_formula *
                  atomic_formula
      val simultaneous_substitution_atomic_formula :
        var list -> term list -> atomic_formula -> atomic_formula
      val simultaneous_substitution_formula : var list -> term list -> formula -> formula
      val free_variables_of_atomic_formula : atomic_formula -> SetVar.t
      val free_variables_of_formula : formula -> SetVar.t
      val term_free_for_var : term -> 'a -> formula -> bool
      val printer_first_order_atomic_formula :
        Format.formatter -> atomic_formula -> unit
      val printer_first_order_formula : Format.formatter -> formula -> unit
    end
