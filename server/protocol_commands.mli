type notation_element = Param of string | String of string

type demonstration_step =
  | Step of string
  | Call of string * (string list)

type command =
  | Verbose of int
  | Prop
  | First_order
  | Keep_notations
  | Expand_notations
  | Compiled
  | Interpreted
  | Save of Modes.ascii_mode * string
  | Load of Modes.ascii_mode * string
  | Notation of { name:string ; params: string list ; syntax : notation_element list ; semantics : notation_element list }
  | Theorem of {name:string ; params: string list; premisses: string list; conclusion : string ; demonstration : demonstration_step list; status : Session.status}
  | Axiom of {name:string; formula:string} 
  | History
  | Show of string
  | List of [`Axioms | `Theorems | `Files]
  | User of string
  | Quit

val encode_string : string -> bytes
val encode_command : command -> bytes

