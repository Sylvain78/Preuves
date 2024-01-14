open  Kernel_prop_interp.Formula_prop

let update_parser_notations l =
  Dyp.update_pp (Kernel_prop_interp.Prop_parser.pp()) [
    Add_rules (List.map 
                 (function n ->
                    let rule       = ("expr", Kernel_prop_interp.Prop_parser.notation_elements_to_regexp n.notation_prop_notation, "default_priority",[])
                    and action _ l = Kernel_prop_interp.Prop_parser.Obj_expr1 (PApply_notation({apply_notation_prop = n;
                                                                                                apply_notation_prop_params = 
                                                                                                  List.filter_map  (function 
                                                                                                      |Kernel_prop_interp.Prop_parser.Obj_expr1 e -> Some e 
                                                                                                      | _ -> None) l
                                                                                               })),
                                     []
                    in
                    (rule,action)
                 ) l); Dyp.Keep_grammar] 
