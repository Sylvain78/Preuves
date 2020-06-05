type save = Text | Binary
type mode = Prop | First_order
type status = Unverified | Verified | False
type speed = Fast | Paranoid
module type P = module type of Prop.Proof_prop
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
