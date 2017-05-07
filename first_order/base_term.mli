module type TERM =
  functor (Sig : Signature.SIGNATURE) ->
    sig
      type var = Var of int | Metavar of string
      module SetVar :
        sig
          type elt = var
          type t
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
          val map : (elt -> elt) -> t -> t
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
      type term
      val printers_constants :
        (Sig.symbol, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
      val printers_relations :
        (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
      val variables_term : term -> SetVar.t
      val simultaneous_substitution_term : var list -> term list -> term -> term
      val print_term : Format.formatter -> term -> unit
    end
module Term :
  functor (Sig : Signature.SIGNATURE) ->
    sig
      type var = Var of int | Metavar of string
      type term =
          V of var
        | Constant of Sig.symbol
        | Operation of Sig.symbol * term list
      val printers_constants :
        (Sig.symbol, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
      val printers_relations :
        (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
      val compare_var : var -> var -> int
      module SetVar :
        sig
          type elt = var
          type t
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
      val unifier_term : term -> term -> substitution
      val unifier_liste_term : (term * term) list -> substitution
      val print_term : Format.formatter -> term -> unit
    end
