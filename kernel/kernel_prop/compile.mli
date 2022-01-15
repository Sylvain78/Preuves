open Prop.Formula_prop
open Prop.Theorem_prop
open Verif

val compile_demonstration :
  ?axioms:theorem_prop list ->
  ?theorems:theorem_prop list ->
  ?hypotheses:formula_prop list -> 
  demo:formula_prop list ->
  unit ->
  kernel_proof
