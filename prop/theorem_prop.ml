open Formula_prop

type step = 
  | Step of formula_prop 
  | Call of string * formula_prop list

type theorem_prop = 
  {
    kind_prop : Kind_prop.kind;
    name_theorem_prop : string;
    proof_prop : step list;
    conclusion_prop: formula_prop;
  }
