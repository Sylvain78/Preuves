{
open Protocol_parser
let keywords = Hashtbl.create 17
let _ = List.iter (fun (k,v) -> Hashtbl.add keywords k v) 
    [ 
      ("Prop",PROP) ;
      ("Notation",NOTATION) ; 
      ("Param",PARAM) ;
      ("Syntax",SYNTAX) ;
      ("Semantics",SEMANTICS) ;
      ("End",END) ;
      ("Theorem",THEOREM) ;
      ("Premisses", PREMISSES) ;
      ("Conclusion", CONCLUSION) ;
      ("Demonstration", DEMONSTRATION) ;
      ("Save", SAVE) ;
      ("Load", LOAD) ;
      ("binary", BINARY);
      ("text", TEXT) ;
    ]
let buffer = Buffer.create 256
let store_string_char c = Buffer.add_char buffer c
let get_stored_string () = Buffer.contents buffer
}
let newline = ('\013'* '\010')
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let digit = ['0'-'9']
let ident = (lowercase|uppercase)(lowercase|uppercase|digit)*

rule token = parse 
  | [' ' '\t']     { print_string "<space>";flush stdout;token lexbuf } 
  | newline { NEWLINE }
  | ident as id 
    { 
      try print_string ("keyword "^id ^ "\n");flush stdout;Hashtbl.find keywords id
      with 
      | Not_found -> print_string (" ident "^id^ "\n"); flush stdout;IDENT(Lexing.lexeme lexbuf)
    }
  | "\"" { quoted_string lexbuf;
           QUOTED_STRING (get_stored_string())
         } 
  | "$" { latex (Buffer.create 17) lexbuf; }
and latex buf = parse
 | '$' { FORMULA (Buffer.contents buf)}
 | "\\$" { Buffer.add_char buf '$' ; latex buf lexbuf }
 | _ as c { Buffer.add_char buf c ; latex buf lexbuf }
and quoted_string = parse
  | '\"'
     { () }
  | (_ as c)
    { store_string_char c;
      quoted_string lexbuf }
 and string = parse 
| [^'\n']* as s { STRING s }
