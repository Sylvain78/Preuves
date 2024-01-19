open Formula_prop

type theorem_prop = 
  {
    kind : Kind_prop.kind;
    name : string;
    params : formula_prop list;
    premisses : formula_prop list;
    demonstration : formula_prop list;
    conclusion : formula_prop;
  }
