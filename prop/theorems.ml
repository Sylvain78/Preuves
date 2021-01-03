open Formula_prop

type theorem_prop = 
  {
    kind_prop : Kind_prop.kind;
    name_theorem_prop : string;
    parameters_prop : [`PVar of int | `PMetaVar of string] list;
    premisses_prop : formula_prop list;
    proof_prop : formula_prop list;
    conclusion_prop: formula_prop;
  }

