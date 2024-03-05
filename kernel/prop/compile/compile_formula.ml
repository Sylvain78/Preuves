include  Kernel_prop_interp.Formula

let update_parser_notations l =
  Dyp.update_pp (Kernel_prop_interp.Parser.pp()) [
    Add_rules (List.map 
                 (function n ->
                    let rule       = ("expr", Kernel_prop_interp.Parser.notation_elements_to_regexp n.notation_prop_notation, "default_priority",[])
                    and action _ l = Kernel_prop_interp.Parser.Obj_formula1 (PApply_notation({apply_notation_prop = n;
                                                                                                apply_notation_prop_params = 
                                                                                                  List.filter_map  (function 
                                                                                                      |Kernel_prop_interp.Parser.Obj_formula1 e -> Some e
                                                                                                      | _ -> None) l
                                                                                               })),
                                     []
                    in
                    (rule,action)
                 ) l); Dyp.Keep_grammar] 
