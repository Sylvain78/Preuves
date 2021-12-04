%{
%}

%token NEWLINE
%token PROP
%token FIRST_ORDER
%token KEEP_NOTATIONS
%token EXPAND_NOTATIONS
%token INTERPRETED
%token COMPILED
%token NOTATION
%token PARAM
%token SYNTAX
%token SEMANTICS
%token DEMONSTRATION
%token END
%token AXIOM
%token THEOREM
%token PREMISSES
%token CONCLUSION
%token SAVE
%token LOAD
%token BINARY
%token TEXT
%token HISTORY
%token SHOW
%token VERBOSE
%token QUIT

%token<int> NUMBER
%token<string> IDENT
%token<string> QUOTED_STRING
%token<string> STRING
%token<string> FORMULA
%start phrase
%type<Protocol_commands.command> phrase

%%

phrase:
| mode { $1 }
| notation { $1 }
| axiom { $1 }
| theorem { $1 }
| file_command { $1 }
| info { $1} ;

notation:
 NOTATION NEWLINE 
 IDENT NEWLINE 
 PARAM NEWLINE ident_list NEWLINE 
 SYNTAX NEWLINE syntax_elt_list NEWLINE
 SEMANTICS NEWLINE syntax_elt_list NEWLINE
 END { Notation{name=$3 ; params=$7 ; syntax = $11 ; semantics=$15} }
;

axiom:
  AXIOM NEWLINE
  IDENT NEWLINE
  FORMULA { Axiom{name=$3 ; formula=$5} }
;

theorem:
 THEOREM NEWLINE
 IDENT NEWLINE
 PARAM NEWLINE
 formula_list 
 PREMISSES NEWLINE
 formula_list
 CONCLUSION NEWLINE
 FORMULA NEWLINE
 DEMONSTRATION NEWLINE
 term_proof_list 
 END { Theorem{name=$3;params=$7;premisses=$10;conclusion=$13;demonstration=$17;status=Unverified} } 
;

mode:
| VERBOSE NUMBER { Verbose $2 }
| PROP { Prop }
| FIRST_ORDER { First_order }
| KEEP_NOTATIONS { Keep_notations}
| EXPAND_NOTATIONS { Expand_notations }
| COMPILED { Compiled }
| INTERPRETED  { Interpreted  }
;

ident_list:
|  {[]}
| IDENT ident_list { $1 :: $2 }
;

syntax_elt_list:
| syntax_elt {[$1]}
| syntax_elt syntax_elt_list{ $1 :: $2 }
;

syntax_elt:
| IDENT { Param $1 }
| QUOTED_STRING {String $1 }
;

formula_list :
| { [] }
| FORMULA NEWLINE formula_list { $1::$3 }
;

term_proof_list:
| { [] }
| FORMULA NEWLINE term_proof_list { $1::$3 }
;

file_command :
| SAVE NEWLINE BINARY NEWLINE QUOTED_STRING{ Save(Binary, String.sub $5 1 ((String.length $5) - 2)) }
| SAVE NEWLINE TEXT NEWLINE QUOTED_STRING { Save(Text, String.sub $5 1 ((String.length $5) - 2)) }
| LOAD NEWLINE BINARY NEWLINE QUOTED_STRING { Load(Binary, String.sub $5 1 ((String.length $5) - 2)) }
| LOAD NEWLINE TEXT NEWLINE QUOTED_STRING { Load(Text, String.sub $5 1 ((String.length $5) - 2)) } 
;

info :
| QUIT {Quit}
| HISTORY { History }
| SHOW NEWLINE
  IDENT { Show $3 }
