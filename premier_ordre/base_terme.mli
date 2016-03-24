module type TERME =
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
      type terme
      val printers_constantes :
        (Sig.symbole, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
      val printers_relations :
        (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
      val variables_terme : terme -> SetVar.t
      val substitution_simultanee_terme : var list -> terme list -> terme -> terme
      val print_terme : Format.formatter -> terme -> unit
    end
module Terme :
  functor (Sig : Signature.SIGNATURE) ->
    sig
      type var = Var of int | Metavar of string
      type terme =
          V of var
        | Constante of Sig.symbole
        | Operation of Sig.symbole * terme list
      val printers_constantes :
        (Sig.symbole, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
      val printers_relations :
        (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
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
      val variables_terme : terme -> SetVar.t
      val substitution_simultanee_terme : var list -> terme list -> terme -> terme
      type substitution = terme -> terme
      val unifier_terme : terme -> terme -> substitution
      val unifier_liste_terme : (terme * terme) list -> substitution
      val print_terme : Format.formatter -> terme -> unit
    end
