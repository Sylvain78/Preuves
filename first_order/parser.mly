%{
	
	open Base_terme
	open Util
	module Sig = Signature.SignatureMinimale
	
%}

%token DEBUT_GROUPE FIN_GROUPE EOF
%token LPAR RPAR VIRG EXCLAM
%token <string> CONSTANTE

%token EQ NEQ NEG AND OR IMPLY EXISTS FORALL
%token EQUIV
%token <string * int> OP
%token <string> OPBIN
%token <string * int> REL
%token <string> RELBIN
%token <int> VAR
%token <string> METAVAR

%right AND OR
%start var
%type <Base_terme.Term(Sig).var> start
%type <Base_terme.Term(Sig).var> var


%%

start :
| formule EOF { $1 }

var :
| VAR { Var $1 }
| METAVAR { Metavar $1 }

terme :
| CONSTANTE { Constante $1 }
| var { V($1) }
| OP LPAR liste_terme RPAR { Operation (fst $1,snd $1, $3) }
| terme OPBIN terme { Operation ($2, 2, [$1;$3]) }


liste_terme :
| terme {[$1]}
| terme VIRG liste_terme { $1::$3 }
 
formule_atomique :
| terme EQ terme { Eq($1,$3) }
| REL LPAR liste_terme RPAR { Relation (fst $1, snd $1, $3) }
| terme RELBIN terme { Relation($2, 2, [$1;$3]) }

formule :
| formule_atomique { Formule_atomique $1 }
| LPAR formule RPAR { $2 }
| NEG LPAR formule RPAR { Neg $3 }
| formule AND formule { And($1,$3) }
| formule OR  formule { Or ($1,$3) }
| LPAR formule RPAR IMPLY LPAR formule RPAR { Imply ($2,$6) }
| EXISTS var LPAR formule RPAR { Exists ($2,$4)}
| FORALL var LPAR formule RPAR { Forall ($2,$4)}
/* Conventions*/
| formule EQUIV formule { And (Imply($1,$3), Imply($3,$1)) } 
| EXISTS var OPBIN var LPAR formule RPAR { Exists($2, And(Formule_atomique(Relation($3, 2, [V($2);V($4)])), $6))}
| FORALL var OPBIN var LPAR formule RPAR { Forall($2, Imply(Formule_atomique(Relation($3, 2, [V($2);V($4)])), $6))}
| terme NEQ terme { Neg (Formule_atomique(Eq($1,$3))) }
| terme RELBIN terme RELBIN terme { And(Formule_atomique (Relation($2, 2, [$1;$3])),
																				Formule_atomique (Relation($4, 2, [$3;$5]))) }
| terme EQ terme RELBIN terme { And(Formule_atomique (Eq($1,$3)),
																				Formule_atomique (Relation($4, 2, [$3;$5]))) }
| terme RELBIN terme EQ terme { And(Formule_atomique (Relation($2, 2, [$1;$3])),
																				Formule_atomique (Eq($3,$5))) }																				
| terme EQ terme EQ terme { And(Formule_atomique (Eq($1,$3)),
																				Formule_atomique (Eq($3,$5))) }
| EXISTS var VIRG var LPAR formule RPAR { Exists($2, Exists($4,$6)) }
| FORALL var VIRG var LPAR formule RPAR { Forall($2, Forall($4,$6)) }
| EXISTS EXCLAM var LPAR formule RPAR { 
                                      	let x = $3
                                      	and y = Var(new_var())
	                                      and f = $5
	                                      in
	                                      And(Exists(x,f),
			                                     	Forall(x, Forall (y, Imply(And (f, subst_terme (V y) (V x) f), Formule_atomique(Eq(V x, V y)) ))))
                                      }
																				
