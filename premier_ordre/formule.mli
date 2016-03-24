open Base_terme

module Formule :
  functor (Sig : Signature.SIGNATURE) ->
    sig
      type var = Terme(Sig).var =
        | Var of int
        | Metavar of string
      type terme = Terme(Sig).terme =
        | V of var
        | Constante of Sig.symbole
        | Operation of Sig.symbole * terme list
      val printers_constantes :
        (Sig.symbole, Format.formatter -> unit) Hashtbl.t
      val printers_operations :
        (Sig.symbole, Format.formatter -> terme -> unit) Hashtbl.t
      val compare_var : var -> var -> int
      module SetVar :
        sig
          type elt = var
          type t = Terme(Sig).SetVar.t
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
      val substitution_simultanee : var list -> terme list -> terme -> terme
      type substitution = terme -> terme
      val print_terme : Format.formatter -> terme -> unit
      type formule_atomique =
          Eq of terme * terme
        | Relation of Sig.symbole * terme list
      val printers_relations :
        (Sig.symbole, Format.formatter -> formule_atomique -> unit) Hashtbl.t
      type formule =
          Formule_atomique of formule_atomique
        | Neg of formule
        | And of formule * formule
        | Or of formule * formule
        | Imply of formule * formule
        | Exists of var * formule
        | Forall of var * formule
      exception Echec_unification_formule_atomique of formule_atomique *
                  formule_atomique
      val portee_atomique : formule_atomique -> SetVar.t * 'a list
      val substitution_simultanee_formule_atomique :
        var list -> terme list -> formule_atomique -> formule_atomique
      val substitution_simultanee : var list -> terme list -> formule -> formule
      val variables_libres_formule_atomique : formule_atomique -> SetVar.t
      val variables_libres_formule : formule -> SetVar.t
      val variables_liees_formule : formule -> SetVar.t
      val terme_libre_pour_var : terme -> 'a -> formule -> bool
      val ( => ) : formule -> formule -> formule
      val ( <= ) : formule -> formule -> formule
      val ( && ) : formule -> formule -> formule
      val ( || ) : formule -> formule -> formule
      val neg : formule -> formule
      val ( <=> ) : formule -> formule -> formule
      val ( ?& ) : var * formule -> formule
      val ( ?@ ) : var * formule -> formule
      val ( ^= ) : terme -> terme -> formule
      val ( ^!= ) : terme -> terme -> formule
      val printer_formule_atomique_premier_ordre :
        Format.formatter -> formule_atomique -> unit
      val printer_formule_premier_ordre : Format.formatter -> formule -> unit
    end
