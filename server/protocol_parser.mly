%{
open Protocol_commands
%}

%token PROP
%token FIRST_ORDER
%token KEEP_NOTATIONS // keep notations in condensed form at most possible
%token EXPAND_NOTATIONS //expand notations if needed
%token KEEP_CALLS // keep calls
%token EXPAND_CALLS //expand calls with corresponding theorem's demonstration (substituted with calling params)
%token INTERPRETED //Interpret line by line as string
%token COMPILED //Compile demo to AST + list of strings
%token FAST // accept instance of theorems
%token PARANOID // substitute theorems proofs with local hypothesis, and insert result in gloabl demo
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
%token Binary
%token Text
%token HISTORY
%token LIST
%token AXIOMS
%token THEOREMS
%token INVALIDATE
%token FILES
%token USER
%token SHOW
%token VERBOSE
%token QUIT
%token LPAREN RPAREN

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
| info { $1}
;

notation:
 NOTATION 
 IDENT 
 PARAM ident_list 
 SYNTAX syntax_elt_list 
 SEMANTICS syntax_elt_list
 END { Notation{name=$2 ; params=$4 ; syntax = $6 ; semantics=$8} }
;

axiom:
 AXIOM 
 IDENT 
 FORMULA { Axiom{name=$2 ; formula=$3} }
;

theorem:
 THEOREM 
 IDENT 
 PARAM 
 formula_list 
 PREMISSES 
 formula_list
 CONCLUSION 
 FORMULA 
 DEMONSTRATION 
 term_proof_list 
 END { Theorem{name=$2;params=$4;premisses=$6;conclusion=$8;demonstration=$10;kind=KUnproved} } 
;

mode:
| VERBOSE NUMBER { Verbose $2 }
| PROP { Prop }
| FIRST_ORDER { First_Order }
| KEEP_NOTATIONS { Keep_Notations}
| EXPAND_NOTATIONS { Expand_Notations }
| KEEP_CALLS { Keep_Calls }
| EXPAND_CALLS { Expand_Calls }
| COMPILED { Compiled }
| INTERPRETED { Interpreted }
;

ident_list:
| {[]}
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
|  FORMULA formula_list { $1::$2 }
| { [] }
;

term_proof_list:
| FORMULA term_proof_list { Step $1::$2 }
| IDENT LPAREN formula_list RPAREN  term_proof_list { Call ($1,$3)::$5 }
| { [] }
;

file_command :
| SAVE Binary QUOTED_STRING { Save(Binary, String.sub $3 1 ((String.length $3) - 2)) }
| SAVE Text QUOTED_STRING { Save(Text, String.sub $3 1 ((String.length $3) - 2)) }
| LOAD Binary QUOTED_STRING { Load(Binary, String.sub $3 1 ((String.length $3) - 2)) }
| LOAD Text QUOTED_STRING { Load(Text, String.sub $3 1 ((String.length $3) - 2)) }
;

info :
| QUIT {Quit}
| HISTORY { History }
| LIST AXIOMS { List `Axioms }
| LIST THEOREMS { List `Theorems }
| LIST FILES { List `Files }
| SHOW IDENT { Show $2 }
| USER IDENT { User $2 }
| INVALIDATE IDENT { Invalidate $2 }
;
