(* open Protocol_commands*)

let decode s =
  try Protocol_parser.phrase Protocol_lexer.token (Lexing.from_string s)
  with 
  | Failure s' -> failwith ("Protocol decode failure (" ^ s' ^ ") : " ^ s)
  | Stdlib.Parsing.Parse_error -> failwith ("Protocol decode parse_error : " ^ s ^"XXX")

type output = Latex | Text
type latex_output = LMath | LText

type answer = 
  | Ok of Protocol_commands.command
  | Answer of output * (latex_output option) * string
  | Error of string

let encode_answer = function
  | Ok c -> Bytes.(cat (of_string "Ok") (Protocol_commands.encode_command c))
(*  | Answer (Latex, Some LMath, s) -> "" ^ s
  | Answer (Latex, Some LText, s) -> "12" ^ s
  | Answer (Latex, None, s) -> "13" ^ s
  | Answer (Text, Some LMath, s) -> "14" ^ s
  | Answer (Text, Some LText, s) -> "15" ^ s
  | Answer (Text, None, s) -> "16" ^ s
*)
  | Answer (Latex, Some LText, s) -> Bytes.(concat empty ( [of_string"Answer"; of_string"latex";Protocol_commands.encode_string s]))
  | Error s -> Bytes.(cat (of_string ("Error")) (Protocol_commands.encode_string s))
  | _ -> failwith "unimplemented2"
