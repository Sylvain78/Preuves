open Signes_et_assemblages
open Théorie
open Constructions_formatives

let cf1 (th:théorie) (Relation(a,Construction_formative(th',cfa))) (Relation(b,Construction_formative(th'',cfb))) =
  assert (th = th');
  assert (th = th'');
  let a_ou_b = Ou :: (concat_assemblage a b)
  in
  Relation(a_ou_b, Construction_formative(th, a_ou_b :: cfb @ cfa))

