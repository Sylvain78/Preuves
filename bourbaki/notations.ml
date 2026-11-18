open Signes_et_assemblages

type notation = ..
type notation += Assemblage of assemblage
type notation += Concat of assemblage * assemblage
type notation += Tau of lettre * assemblage
type notation += Subst of lettre list * notation list * notation

let rec normalize = function
  | Assemblage a -> a
  | Concat(a,b) -> concat_assemblage a b
  | Tau(x,a) -> tau x a
  | Subst(lv,lb,a) -> subst lv (List.map normalize lb) (normalize a)
  | _ ->  failwith "notation inconnue"
