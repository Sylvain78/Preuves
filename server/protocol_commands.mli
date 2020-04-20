type notation_element = Param of string | String of string
type command =
  | Save of Session.save * string
  | Load of Session.save * string
  | Prop
  | First_order
  | Notation of { name:string ; params: string list ; syntax : notation_element list ; semantics : notation_element list }
  | Theorem of {name:string ; params: string list; premisses: string list; conclusion : string ; demonstration : string list}
  | Axiom of {name:string; formula:string} 
