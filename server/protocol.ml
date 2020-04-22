
type answer =
  | Ok
  | Answer of string

let decode s =
  print_string ("decode : "^s^ "\n");Stdlib.flush Stdlib.stdout;
  let _ =  print_string "decode: token ...\n"; ignore ( Protocol_lexer.token (Lexing.from_string s));print_string "decode : end token\n"
  in
  try Protocol_parser.phrase Protocol_lexer.token (Lexing.from_string s)
  with 
  | Stdlib.Parsing.Parse_error  -> failwith ("Protocol decode error : " ^ s)
