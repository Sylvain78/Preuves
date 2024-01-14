open Formula_prop

type kernel_theorem_prop = 
  {
    kernel_kind_prop : Kind_prop.kind;
    kernel_name_theorem_prop : string;
    kernel_proof_prop : formula_prop list;
    kernel_conclusion_prop: formula_prop;
  }
