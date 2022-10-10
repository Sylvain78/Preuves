type notation_element = Param of string | String of string
type command =
  | Verbose of int
  | Prop
  | Keep_notations
  | Expand_notations
  | Compiled
  | Interpreted
  | Save of Session.save * string
  | Load of Session.save * string
  | First_order
  | Notation of { name:string ; params: string list ; syntax : notation_element list ; semantics : notation_element list }
  | Theorem of {name:string ; params: string list; premisses: string list; conclusion : string ; demonstration : string list ; status : Session.status}
  | Axiom of {name:string; formula:string} 
  | History
  | Show of string
  | List of [`Axioms | `Theorems | `Files]
  | Quit
