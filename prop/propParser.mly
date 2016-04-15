%{
open Formule_prop
open PropLexer
     %}

%token <int> VAR
             %token LPAR RPAR
             %token LAND LOR LIMPLY LNOT
             %nonassoc LNOT LAND LOR LIMPLY
             %start formule
             %type <Formule_prop.pformule> formule
                                           %%
                                           formule:
                     | VAR       { PVar($1) }
                 | LPAR formule LPAR { $2 } 
                 | LNOT VAR  { PNeg(PVar($2)) }
                 | LNOT LPAR formule LPAR { PNeg($3) }
                 | formule LAND formule   { PAnd($1, $3) } 
                 | formule LOR formule    { POr($1, $3) }
                 | formule LIMPLY formule { PImpl($1, $3) } 
  ;
