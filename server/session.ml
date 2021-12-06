type save = Text | Binary
type order = Prop | First_order
type speed = Keep_notations | Expand_notations (* expansion of notation *)
type evaluation = Compiled | Interpreted (* Compilation of demonstration, or verification line by line*)

(*
 * Verbose level :
 * 0
 * 1 verif
 * 2
 * 3
 * 4
 * 5
 * *)
type mode = { mutable verbose_level : int; mutable order : order; mutable speed : speed; mutable evaluation : evaluation }
type status = Unverified | Verified | False
module type P = module type of Prop.Verif
module type F = module type of First_order.Formula

type 'formula session =
  {
    mutable mode : mode ;
    mutable speed : speed ;
    name : string;
    mutable history : string list;
    (*mutable parser : (unit,
                      (string * string * string * string * string * string *
                       Prop.Formula_prop.notation_prop_element list * string * string *
                       string * Prop.Formula_prop.notation_prop_element list * string *
                       string * string * Prop.Formula_prop.notation_prop_element list *
                       string * string, Prop.Formula_prop.notation_prop, unit, unit,
                       unit, Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.formula_prop, Prop.Formula_prop.formula_prop,
                       Prop.Formula_prop.notation_prop, Prop.Formula_prop.notation_prop,
                       Prop.Formula_prop.notation_prop_element,
                       Prop.Formula_prop.notation_prop_element list, unit,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element)
                        Prop.Prop_parser.obj, unit, unit,
                      (string * string * string * string * string * string *
                       Prop.Formula_prop.notation_prop_element list * string * string *
                       string * Prop.Formula_prop.notation_prop_element list * string *
                       string * string * Prop.Formula_prop.notation_prop_element list *
                       string * string, Prop.Formula_prop.notation_prop, unit, unit,
                       unit, Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.formula_prop, Prop.Formula_prop.formula_prop,
                       Prop.Formula_prop.notation_prop, Prop.Formula_prop.notation_prop,
                       Prop.Formula_prop.notation_prop_element,
                       Prop.Formula_prop.notation_prop_element list, unit,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element list,
                       Prop.Formula_prop.notation_prop_element)
                        Prop.Prop_parser.obj Dyp.dyplexbuf)
        Dyp.parser_pilot;*)
    mutable axioms : 'formula list;
    mutable theorems : 'formula list;
  }
