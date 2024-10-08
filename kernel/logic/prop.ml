open Logic2

module Formula_Prop = struct
  let name = "\\mathfrak{L}_\\bullet"

  type formula = ..

  type formula +=
    | PVar of int
    | PAnd of formula * formula
    | POr of formula * formula
    | PImpl of formula * formula

  let of_string _ = PVar 0
  let to_string _ = ""


  let c1 = function PVar _ | PAnd _ |POr _ | PImpl _ | _ -> 0;; 
  let a = PVar 0
  let b = PAnd(a,a)
  let c = POr(b,b)
  let d = PImpl(c,c);;
  ignore (d,c1)

end

module Prop : LOGIC with type formula = Formula_Prop.formula = struct
  let name = "Prop"
  module L = Formula_Prop
  type formula = L.formula
  type rule =  formula list -> formula
  let cut = function 
    |[f;L.PImpl(f',g)] when f=f' -> g
    | _ -> failwith "cut inapplicable"
  
  let rules = [ cut]
 (*TODO regle coupure*)
  let a1 = L.of_string "X_1 \\implies (X_2 \\implies X_1)"
  let axiom f = f = a1
  let heuristic_proof ?(premisses = empty_family) formula = ignore (premisses,formula);None

  type demonstration = { hypotheses : formula family ; demonstration : formula list }

  let verification _ = false
end
