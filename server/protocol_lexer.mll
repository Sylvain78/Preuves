{
open Protocol_parser
let keywords = Hashtbl.create 17
let _ = List.iter (fun (k,v) -> Hashtbl.add keywords k v) 
[ 
      ("Prop",PROP) ;
      ("First_order", FIRST_ORDER) ;
      ("Keep_Notations",KEEP_NOTATIONS);
      ("Expand_Notations",EXPAND_NOTATIONS);
      ("Compiled", COMPILED);
      ("Interpreted", INTERPRETED);
      ("Notation",NOTATION) ; 
      ("History",HISTORY) ; 
      ("List",LIST) ; 
      ("Axioms",AXIOMS) ; 
      ("Theorems",THEOREMS) ; 
      ("Files",FILES) ; 
      ("Show",SHOW) ; 
      ("Param",PARAM) ;
      ("Syntax",SYNTAX) ;
      ("Semantics",SEMANTICS) ;
      ("End",END) ;
      ("Axiom",AXIOM);
      ("Theorem",THEOREM) ;
      ("Premisses", PREMISSES) ;
      ("Conclusion", CONCLUSION) ;
      ("Demonstration", DEMONSTRATION) ;
      ("Save", SAVE) ;
      ("Load", LOAD) ;
      ("binary", Binary);
      ("text", Text) ;
      ("User", USER) ;
      ("Quit", QUIT) ;
]
let buffer = Buffer.create 256
let store_string_char c = Buffer.add_char buffer c
let get_stored_string () =
        let s =Buffer.contents buffer 
        in 
        Buffer.clear buffer;
        s
let comments : string list ref = ref []
let add_comment s = 
  comments := s:: !comments
}
let newline = ('\013'* '\010')
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let digit = ['0'-'9']
let ident = (lowercase|uppercase)(lowercase|uppercase|digit|'_')*

rule token = parse 
  | newline | [' ' '\t']     { token lexbuf } 
  | '(' { LPAREN }
  | ')' { RPAREN }
  | ident as id 
    {
      try 
        Hashtbl.find keywords id
      with 
      | Not_found -> IDENT(Lexing.lexeme lexbuf)
    }
  | "\"" 
    { 
      quoted_string lexbuf;
      QUOTED_STRING ( "\"" ^ (get_stored_string()) ^ "\"")
    } 
  | "$" { latex (Buffer.create 17) lexbuf; }
  | "#"[^'\n']* { add_comment (Lexing.lexeme lexbuf); token lexbuf }
  | digit+ { NUMBER(int_of_string (Lexing.lexeme lexbuf)) }
  | _ as c { failwith (Printf.sprintf "unexpected character: %C" c) }
and latex buf = parse
      | '$' { FORMULA (Buffer.contents buf)}
      | "\\$" { Buffer.add_char buf '$' ; latex buf lexbuf }
      | _ as c { Buffer.add_char buf c ; latex buf lexbuf }
and quoted_string = parse
      | "\"" { () }
      | (_ as c)
        { 
          store_string_char c;
          quoted_string lexbuf 
        }
        
