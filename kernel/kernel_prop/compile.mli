open Prop.Formula_prop
open Verif

val compile_demonstration :
  ?theory:formula_prop list ->
  demo:formula_prop list ->
  unit ->
  kernel_proof
