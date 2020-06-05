module type SESSION =
  sig
    type save = Session.save = Text | Binary
    type mode = Session.mode = Prop | First_order
    type speed = Session.speed = Fast | Paranoid
    type status = Session.status = Unverified | Verified | False
    module type P =
      sig
        val a1 : Prop.Formula_prop.formula_prop
        val a2 : Prop.Formula_prop.formula_prop
        val a3 : Prop.Formula_prop.formula_prop
        val a4 : Prop.Formula_prop.formula_prop
        val a5 : Prop.Formula_prop.formula_prop
        val a6 : Prop.Formula_prop.formula_prop
        val a7 : Prop.Formula_prop.formula_prop
        val a8 : Prop.Formula_prop.formula_prop
        val a9 : Prop.Formula_prop.formula_prop
        val a10 : Prop.Formula_prop.formula_prop
        val a11 : Prop.Formula_prop.formula_prop
        val axioms_prop :
          Prop.Kernel_theorem_prop.kernel_theorem_prop list ref
        type notation_prop_element =
          Prop.Formula_prop.notation_prop_element =
            Param of string
          | String of string
        type formula_prop =
          Prop.Formula_prop.formula_prop =
            PVar of int
          | PMetaVar of string
          | PNeg of formula_prop
          | PAnd of formula_prop * formula_prop
          | POr of formula_prop * formula_prop
          | PImpl of formula_prop * formula_prop
          | PApply_notation of apply_notation_prop
        and apply_notation_prop =
          Prop.Formula_prop.apply_notation_prop = {
          apply_notation_prop : notation_prop;
          apply_notation_prop_params : formula_prop list;
        }
        and notation_prop =
          Prop.Formula_prop.notation_prop = {
          notation_prop_name : string;
          notation_prop_params : notation_prop_element list;
          notation_prop_notation : notation_prop_element list;
          notation_prop_semantique : notation_prop_element list;
        }
        val printer_formula_prop : Format.formatter -> formula_prop -> unit
        val to_string_formula_prop : formula_prop -> string
        type kernel_theorem_prop =
          Prop.Kernel_theorem_prop.kernel_theorem_prop = {
          kernel_kind_prop : Prop.Kind_prop.kind;
          kernel_name_theorem_prop : string;
          kernel_proof_prop : Prop.Formula_prop.formula_prop list;
          kernel_conclusion_prop : Prop.Formula_prop.formula_prop;
        }
        val formula_from_string : string -> Prop.Formula_prop.formula_prop
        val notation_from_string : string -> Prop.Formula_prop.notation_prop
        (* TODO one day...
         * val save_parser : string -> unit
         *)
        exception Failed_Unification of formula_prop * formula_prop
        val get_semantique : apply_notation_prop -> formula_prop
        val equiv_notation : formula_prop -> formula_prop -> bool
        val instance : formula_prop -> formula_prop -> bool
        val cut : formula_prop -> formula_prop list -> bool
        val theorems_prop :
          Prop.Kernel_theorem_prop.kernel_theorem_prop list ref
        exception Invalid_demonstration of formula_prop * formula_prop list
        val kernel_verif :
          hypotheses:formula_prop list ->
          proved:formula_prop list -> to_prove:formula_prop list -> bool
        val verif :
          hypotheses:formula_prop list ->
          proved:formula_prop list -> to_prove:formula_prop list -> bool
        val prop_proof_verif :
          hyp:formula_prop list ->
          formula_prop -> proof:formula_prop list -> bool
        val prop_proof_kernel_verif :
          hyp:formula_prop list ->
          formula_prop -> proof:formula_prop list -> bool
        val demo_chaining : Prop.Formula_prop.formula_prop list
      end
    module type F =
      sig
        module Formula :
          functor (Sig : First_order.Signature.SIGNATURE) ->
            sig
              module Bt :
                sig
                  type var =
                    First_order.Base_term.Term(Sig).var =
                      Var of int
                    | Metavar of string
                  val compare_var : var -> var -> int
                  module SetVar :
                    sig
                      type elt = var
                      type t = First_order.Base_term.Term(Sig).SetVar.t
                      val empty : t
                      val is_empty : t -> bool
                      val mem : elt -> t -> bool
                      val add : elt -> t -> t
                      val singleton : elt -> t
                      val remove : elt -> t -> t
                      val union : t -> t -> t
                      val inter : t -> t -> t
                      val disjoint : t -> t -> bool
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
                      val filter_map : (elt -> elt option) -> t -> t
                      val partition : (elt -> bool) -> t -> t * t
                      val cardinal : t -> int
                      val elements : t -> elt list
                      val min_elt : t -> elt
                      val min_elt_opt : t -> elt option
                      val max_elt : t -> elt
                      val max_elt_opt : t -> elt option
                      val choose : t -> elt
                      val choose_opt : t -> elt option
                      val split : elt -> t -> t * bool * t
                      val find : elt -> t -> elt
                      val find_opt : elt -> t -> elt option
                      val find_first : (elt -> bool) -> t -> elt
                      val find_first_opt : (elt -> bool) -> t -> elt option
                      val find_last : (elt -> bool) -> t -> elt
                      val find_last_opt : (elt -> bool) -> t -> elt option
                      val of_list : elt list -> t
                      val to_seq_from : elt -> t -> elt Seq.t
                      val to_seq : t -> elt Seq.t
                      val add_seq : elt Seq.t -> t -> t
                      val of_seq : elt Seq.t -> t
                    end
                  type term =
                    First_order.Base_term.Term(Sig).term =
                      TV of var
                    | TConstant of Sig.symbol
                    | TOperation of Sig.symbol * term list
                  val printers_constants :
                    (Sig.symbol, Format.formatter -> unit) Hashtbl.t
                  val printers_operations :
                    (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
                  val printers_relations :
                    (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
                  val variables_term : term -> SetVar.t
                  type substitution = term -> term
                  val simultaneous_substitution_term :
                    var list -> term list -> term -> term
                  val print_term : Format.formatter -> term -> unit
                end
              type var =
                First_order.Base_term.Term(Sig).var =
                  Var of int
                | Metavar of string
              type term =
                First_order.Base_term.Term(Sig).term =
                  TV of var
                | TConstant of Sig.symbol
                | TOperation of Sig.symbol * term list
              val printers_constants :
                (Sig.symbol, Format.formatter -> unit) Hashtbl.t
              val printers_operations :
                (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
              val compare_var : var -> var -> int
              module SetVar :
                sig
                  type elt = var
                  type t = First_order.Base_term.Term(Sig).SetVar.t
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
              val simultaneous_substitution_term :
                var list -> term list -> term -> term
              type substitution = term -> term
              val print_term : Format.formatter -> term -> unit
              type atomic_formula =
                First_order.Formula.Formula(Sig).atomic_formula =
                  Eq of term * term
                | Relation of Sig.symbol * term list
              val printers_relations :
                (Sig.symbol, Format.formatter -> atomic_formula -> unit)
                Hashtbl.t
              type formula =
                First_order.Formula.Formula(Sig).formula =
                  FAtomic_formula of atomic_formula
                | FNeg of formula
                | FAnd of formula * formula
                | FOr of formula * formula
                | FImply of formula * formula
                | FExists of var * formula
                | FForall of var * formula
              val equiv : formula -> formula -> formula
              exception Failed_unification_atomic_formula of atomic_formula *
                          atomic_formula
              val simultaneous_substitution_atomic_formula :
                var list -> term list -> atomic_formula -> atomic_formula
              val simultaneous_substitution_formula :
                var list -> term list -> formula -> formula
              val free_variables_of_atomic_formula :
                atomic_formula -> SetVar.t
              val free_variables_of_formula : formula -> SetVar.t
              val term_free_for_var : term -> 'a -> formula -> bool
              val printer_first_order_atomic_formula :
                Format.formatter -> atomic_formula -> unit
              val printer_first_order_formula :
                Format.formatter -> formula -> unit
            end
      end
    type 'formula session = 'formula Session.session =  {
      mutable mode : mode;
      mutable speed : speed;
      name : string;
      mutable history : string list;
      mutable axioms : 'formula list;
      mutable theorems : 'formula list;
    }
  end
val socket_name : string option ref
val file_name : string option ref
val usage : string
val version : string
val print_version_num : unit -> 'a
val print_version_string : unit -> 'a
val specs : (string * Arg.spec * string) list
val session : Prop.Kernel_theorem_prop.kernel_theorem_prop Session.session
val save_session : Session.save -> string -> unit
val load_session :
  Session.save -> string -> Util__Unix_tools.io_channel -> unit
val eval : string -> Util__Unix_tools.io_channel -> Protocol.answer
val repl : Util__Unix_tools.io_channel -> unit
val main : unit -> unit
