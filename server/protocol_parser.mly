%{
%}

%token NEWLINE
%token PROP
%token FIRST_ORDER
%token NOTATION
%token PARAM
%token SYNTAX
%token SEMANTICS
%token DEMONSTRATION
%token END
%token THEOREM

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
| theorem { $1 }
| test { Prop }
;

test:
  NOTATION IDENT {print_string "test ok\n";flush stdout;}
;
notation:
 NOTATION NEWLINE 
 IDENT NEWLINE 
 PARAM NEWLINE ident_list NEWLINE 
 SYNTAX NEWLINE syntax_elt_list NEWLINE
 SEMANTICS NEWLINE syntax_elt_list NEWLINE
 END { Notation{name=$3 ; params=$7 ; syntax = $11 ; semantics=$15} }
;

theorem:
 THEOREM NEWLINE
 IDENT NEWLINE
 PARAM NEWLINE
 string_list NEWLINE
 premisses NEWLINE
 FORMULA NEWLINE
 DEMONSTRATION NEWLINE
 term_proof_list 
 END { Theorem{name=$3;params=$7;premisses=$9;conclusion=$11;demonstration=$15} } 
;


mode:
| PROP { Prop }
| FIRST_ORDER { First_order }
;
ident_list:
|  {[]}
| IDENT {[$1]}
| IDENT ident_list { $1 :: $2 }
;

syntax_elt_list:
 syntax_elt {[$1]}
| syntax_elt syntax_elt_list{ $1 :: $2 }
;

syntax_elt:
| IDENT { print_string ("param " ^$1);Param $1 }
| QUOTED_STRING {print_string ("qs " ^$1);String $1 }
;

string_list:
| STRING { [$1] }
| STRING NEWLINE 
 string_list { $1::$3 }
;

premisses:
| FORMULA { [$1] }
| FORMULA NEWLINE premisses { $1::$3 }
;

term_proof_list:
| FORMULA { [$1] }
| FORMULA NEWLINE term_proof_list { $1::$3 }
;


