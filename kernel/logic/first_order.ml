open Logic2

module Formula_First_order (Signature : SIGNATURE) = struct
  let name = "\\mathfrak{L}_{" ^ Signature.name ^ "}"

  type formula = ..

  type formula +=
    | FVar of int
    | FAnd of formula * formula
    | FOr of formula * formula
    | FImpl of formula * formula
    | FBind of Signature.symbol * int * formula

  let of_string _ = FVar 0
  let to_string _ = ""
  let c1 = function FVar _ | FAnd _ |FOr _ | FImpl _ | _ -> 0;; 
  let a = FVar 0
  let b = FAnd(a,a)
  let c = FOr(b,b)
  let d = FImpl(c,c)
  let e = FBind(Signature.new_symbol(), 0, d);;
  ignore (e,c1)
end

module First_order (Signature : SIGNATURE) : LOGIC with type formula := Formula_First_order(Signature).formula = struct
  let name = "First order"
  module L =Formula_First_order(Signature)
  (*TODO coupure généralisation*)
  type L.formula += FEq of L.formula * L.formula
  let _ = FEq(L.FVar 1, L.FVar 2)

  type formula = L.formula
  type cut =  formula * formula -> formula
  let cut = function 
    | (f, L.FImpl(f',g)) when f=f' -> g
    | _ -> failwith "cut inapplicable"
  type generalisation = int -> formula -> formula
  let generalisation i f = 
    let forall =
      Signature.of_string("\\forall")
    in
    if Signature.binder(forall)
    then L.FBind(forall, i, f)
    else failwith "generalisation not applicable"

  type rule = 
    | Cut of cut 
    | Generalisation of generalisation
  let rules = [Cut cut; Generalisation generalisation]
  let axiom (_:string) f = f= L.of_string "v1"
  let heuristic_proof ?(premisses = empty_family) formula = ignore (premisses,formula);None
  type demonstration
  let verification _ = false
end
