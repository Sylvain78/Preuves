(* open Protocol_commands*)

let decode s =
  try Protocol_parser.phrase Protocol_lexer.token (Lexing.from_string s)
  with 
  | Failure s' -> failwith ("Protocol decode failure (" ^ s' ^ ") : " ^ s)
  | Stdlib.Parsing.Parse_error -> failwith ("Protocol decode parse_error : " ^ s ^"XXX")
