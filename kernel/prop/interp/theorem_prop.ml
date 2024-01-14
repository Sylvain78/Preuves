open Formula_prop

type theorem_prop = 
  {
    kind_prop : Kind_prop.kind;
    name_theorem_prop : string;
    proof_prop : formula_prop list;
    conclusion_prop: formula_prop;
  }
