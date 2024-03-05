type order = Prop | First_order
type expand_notations = Keep_notations | Expand_notations (* expansion of notation *)
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
type mode = 
  { 
    mutable verbose_level : int; 
    mutable order : order; 
    mutable expand_notations : expand_notations; 
    mutable expand_calls : Kernel.Logic.speed;
    mutable evaluation : evaluation 
  }
type status = 
  | Unverified 
  | Verified 
  | False

type session =
  {
    mutable mode : mode ;
    name : string;
    mutable history : string list;
    (*mutable parser : (unit,
                      (string * string * string * string * string * string *
                       Kernel_prop_interp.Formula_prop.notation_prop_element list * string * string *
                       string * Kernel_prop_interp.Formula_prop.notation_prop_element list * string *
                       string * string * Kernel_prop_interp.Formula_prop.notation_prop_element list *
                       string * string, Kernel_prop_interp.Formula_prop.notation_prop, unit, unit,
                       unit, Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.formula_prop, Kernel_prop_interp.Formula_prop.formula_prop,
                       Kernel_prop_interp.Formula_prop.notation_prop, Kernel_prop_interp.Formula_prop.notation_prop,
                       Kernel_prop_interp.Formula_prop.notation_prop_element,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list, unit,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element)
                        Kernel_prop_interp.Parser.obj, unit, unit,
                      (string * string * string * string * string * string *
                       Kernel_prop_interp.Formula_prop.notation_prop_element list * string * string *
                       string * Kernel_prop_interp.Formula_prop.notation_prop_element list * string *
                       string * string * Kernel_prop_interp.Formula_prop.notation_prop_element list *
                       string * string, Kernel_prop_interp.Formula_prop.notation_prop, unit, unit,
                       unit, Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.formula_prop, Kernel_prop_interp.Formula_prop.formula_prop,
                       Kernel_prop_interp.Formula_prop.notation_prop, Kernel_prop_interp.Formula_prop.notation_prop,
                       Kernel_prop_interp.Formula_prop.notation_prop_element,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list, unit,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element list,
                       Kernel_prop_interp.Formula_prop.notation_prop_element)
                        Kernel_prop_interp.Parser.obj Dyp.dyplexbuf)
        Dyp.parser_pilot;*)
    mutable theory : (module Kernel.Logic.LOGIC);
    mutable user : string;
  }
