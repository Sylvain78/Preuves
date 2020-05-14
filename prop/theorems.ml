open Formula_prop

type theorem_prop = 
  {
    kind_prop : Kind_prop.kind;
    name_theorem_prop : string;
    parameters_prop : [`PVar of int | `PMetaVar of string] list;
    premisses_prop : formula_prop list;
    proof_prop : proof_prop;
    conclusion_prop: formula_prop;
  }

and term_proof_prop  = 
  (*TODO | TPPAxiom   of string * formula_prop *)
  | TPPFormula of formula_prop
  (*TODO  | TPPTheorem of formula_prop * (theorem_prop * (formula_prop list)(*parametres*) * (formula_prop list)(* premisses*))*)

and proof_prop = term_proof_prop list 
