{
	open Parser
	open Util
	(*
	module MetaVars=Map.Make (
	struct
		type t= string
		let compare = String.compare
	end)  
	
	let metavars = ref (MetaVars.empty)
	*)
	let liste_constantes = ref []
	let liste_op  = ref ([] : (string * int) list)
	let liste_opbin = ref []
	let liste_rel = ref ([] : (string * int) list)
	let liste_relbin = ref []
}
rule token = parse
	[' ' '\t']     { token lexbuf }
| '(' | "\\left("   { LPAR }
| ')' | "\\right("  { RPAR }
| '{'               { DEBUT_GROUPE }
| '}'               { FIN_GROUPE }
| ','               { VIRG }
| '!'               { EXCLAM }
| '='               { EQ }
| "\\lneq"          { NEQ }
| "\\lnot"          { NEG }
| "\\land"          { AND }
| "\\lor"           { OR }
| "\\Rightarrow"    { IMPLY }
| "\\Leftrightarrow" { EQUIV }
| "\\exists"        { EXISTS }
| "\\forall"        { FORALL }
| '\\'(['a'-'z']+) as s {  match (List.mem s !liste_constantes),
														 		 (List.mem_assoc s !liste_rel),
																 (List.mem s !liste_relbin),
																 (List.mem_assoc s !liste_op),
																 (List.mem s !liste_opbin)
													  with 
														| true,_,_,_,_ -> CONSTANTE(s)
														| _,true,_,_,_ -> REL(List.find (fun (op, arite) -> op = s) !liste_rel )
														| _,_,true,_,_ -> RELBIN(s)
														| _,_,_,true,_ -> OP(List.find (fun (op, arite) -> op = s) !liste_op )
														| _,_,_,_,true -> OPBIN(s)
														| _ -> raise Not_found
													}
| "\\mathbf{X}_{" (['1'-'9']['0'-'9']* as i)"}" { VAR (int_of_string i)}
| "\\mathbf{"(['a'-'z''A'-'Z']+ as v) "}" { METAVAR(v) }
| eof { EOF }
