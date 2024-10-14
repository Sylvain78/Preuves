open Logic2

module Formula_Prop = struct
  let name = "\\mathfrak{L}_\\bullet"
  type formula = PFormula.formula = 
    | PVar of int
    | PNeg of formula
    | PAnd of formula * formula
    | POr of formula * formula
    | PImpl of formula * formula
  let of_string  = Prop_parser.formula_from_string
  let to_string _ = ""
 end

module Prop : LOGIC with type formula = Formula_Prop.formula = struct
  let name = "Prop"

  module L = Formula_Prop

  type formula = L.formula
  type rule = formula list -> formula

  let cut = function
    | [ f; L.PImpl (f', g) ] when f = f' -> g
    | _ -> failwith "cut inapplicable"

  let rules = [ cut ]

  (*TODO regle coupure*)
  let a1 = L.(PImpl(PVar 1, PImpl (PVar 2, PVar 1)))(*L.of_string "X_1 \\implies (X_2 \\implies X_1)"*)
  let a2 = L.(PImpl(PImpl(PVar 1,PImpl(PVar 2, PVar 3)),PImpl(PImpl(PVar 1, PVar 2),PImpl(PVar 1,PVar 3))))(*L.of_string "(X_1 \\implies (X_2 \\implies X_3)) \\implies ((X_1 \\implies X_2) \\implies (X_1 \\implies X_3))"*)
  let axiomes = ["A_1"; "A_2" ; "A_3"; "A_4"; "A_5"; "A_6; ""A_7"; "A_8"; "A_9" ]
  let axiom (axiom:string) f =
    match axiom with 
    | "A_1" -> is_instance f a1
    | "A_2" -> is_instance f a2
    | "A_3" -> is_instance f a3
    | "A_4" -> is_instance f a4
    | "A_5" -> is_instance f a5
    | "A_6" -> is_instance f a6
    | "A_7" -> is_instance f a7
    | "A_8" -> is_instance f a8
    | "A_9" -> is_instance f a9
    | _ -> false
  let heuristic_proof ?(premisses = empty_family) formula =
    ignore (premisses, formula);
    None

  type demonstration = {
    hypotheses : formula family;
    demonstration : formula list;
  }

  let verification _ = false
end
