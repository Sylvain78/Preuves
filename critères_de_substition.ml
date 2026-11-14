open Signes_et_assemblages
open Notations

type identite = 
  | Id of notation * notation 
  | Unknown

let cs1 (a:assemblage) (b:assemblage) (x:lettre) (x':lettre) =
  if not( figure x' a)
  then Id(Subst([x], [Assemblage b], Assemblage a) , Subst([x'],[Assemblage b],Subst([x],[Assemblage [Lettre x']],Assemblage a)))
  else Unknown
