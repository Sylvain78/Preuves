
type answer =
  | Ok
  | Answer of string

let decode s =
  try Protocol_parser.phrase Protocol_lexer.token (Lexing.from_string s)
  with 
  | Failure s' -> failwith ("Protocol decode error (" ^ s' ^ ") : " ^ s)
  | Stdlib.Parsing.Parse_error -> failwith ("Protocol decode error : " ^ s)
