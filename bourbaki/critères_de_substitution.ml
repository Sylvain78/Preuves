open Signes_et_assemblages
open Notations

type identite = 
  | Id of notation * notation 
  | Unknown

let cs1 (a:assemblage) (b:assemblage) (x:lettre) (x':lettre) =
  if not( figure x' a)
  then Id(Subst([x], [Assemblage b], Assemblage a) , Subst([x'],[Assemblage b],Subst([x],[Assemblage [Lettre x']],Assemblage a)))
  else Unknown


let cs2 (a:assemblage) (b:assemblage) (c:assemblage) (x:lettre) (y:lettre) =
  if (x != y)
  then 
    if not (figure y b)
    then 
      let c' = Subst([x], [Assemblage b], Assemblage c)
      in
      Id(Subst([x], [Assemblage b], Subst([y], [Assemblage c],Assemblage a)) , 
         Subst([y],[c'],Subst([x],[Assemblage b],Assemblage a)))
    else Unknown
  else Unknown

let cs3 (a:assemblage) (x:lettre) (x':lettre) =
  if not (figure x a)
  then
    let a' = normalize(Subst([x], [Assemblage([Lettre x'])],Assemblage a))
    in
    Id(Assemblage (tau x a),Assemblage(tau x' a'))
  else Unknown

let cs4 (a:assemblage) (b:assemblage) (x:lettre) (y:lettre) = 
  if (x != y)
  then
    let a' = normalize(Subst([y], [Assemblage b], Assemblage a))
    in
    Id(Subst([y],[Assemblage b],Assemblage(tau x a)), Assemblage(tau x a'))
  else Unknown

let cs5_i (a:assemblage) (c:assemblage) (x:lettre) =
  let a' = normalize(Subst([x],[Assemblage c],Assemblage a))
  in
  Id(Subst([x],[Assemblage c],Concat([Non],a)),Concat([Non],a'))

let cs5_ii (a:assemblage) (b:assemblage) (c:assemblage) (x:lettre) =
  let a' = normalize(Subst([x],[Assemblage c],Assemblage a))
  and b' = normalize(Subst([x],[Assemblage c],Assemblage b))
  in
  Id(Subst([x],[Assemblage c],Concat( normalize(Concat([Ou],a)),b)),Concat(normalize(Concat([Ou],a')), b'))

let cs5_iii (a:assemblage) (b:assemblage) (c:assemblage) (x:lettre) =
  let a' = normalize(Subst([x],[Assemblage c],Assemblage a))
  and b' = normalize(Subst([x],[Assemblage c],Assemblage b))
  in
  Id(Subst([x],[Assemblage c],Concat( normalize(Concat(impl,a)),b)),Concat(normalize(Concat(impl,a')), b'))
     
let cs5_iv (a:assemblage) (b:assemblage) (c:assemblage) (x:lettre) ((s,n):string*int)=
  let a' = normalize(Subst([x],[Assemblage c],Assemblage a))
  and b' = normalize(Subst([x],[Assemblage c],Assemblage b))
  in
  Id(Subst([x],[Assemblage c],Concat( normalize(Concat([Specifique(s,n)],a)),b)),Concat(normalize(Concat([Specifique(s,n)],a')), b'))
