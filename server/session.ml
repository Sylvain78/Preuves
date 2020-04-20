
type save = Text | Binary
type mode = Prop | First_order

let mode = ref Prop

module type P = module type of Prop.Proof_prop
module type F = module type of First_order.Formula

type session =
  {
    mutable mode : mode ;
    mutable history : string list ;
    mutable prop : (module P) ;
    mutable first_order : (module F) ;
  }
