open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Theorem_prop
open Step
open Verif

val compile_demonstration :
  ?axioms:theorem_prop list ->
  ?theorems:theorem_prop list ->
  ?hypotheses:formula_prop list -> 
  demo:step list ->
  unit ->
  kernel_proof
