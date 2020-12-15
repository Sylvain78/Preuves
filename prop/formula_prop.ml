type notation_prop_element = Param of string | String of string

type formula_prop =
  | PVar of int
  | PMetaVar of string
  | PNeg of formula_prop
  | PAnd of formula_prop * formula_prop
  | POr of formula_prop * formula_prop
  | PImpl of formula_prop * formula_prop
  | PApply_notation of apply_notation_prop
and apply_notation_prop =
  {
    apply_notation_prop : notation_prop;
    apply_notation_prop_params : formula_prop list; (*SKE TODO create database of notations*)
  }
and notation_prop =
  {
    notation_prop_name : string;
    notation_prop_params : notation_prop_element list;
    notation_prop_notation : notation_prop_element list;
    notation_prop_semantique : notation_prop_element list;
  }  

exception Failed_Unification of formula_prop * formula_prop

(*SKE Example of notation
  "
  Notation equiv
  Params a b
  a \equiv b 
  (a \imply b)\\land(b \imply a)
  End
  "
*)

let formula_from_string = ref  (fun _ -> failwith "undefined")
let get_semantique_aux to_string_formula_prop formula_from_string ({apply_notation_prop; apply_notation_prop_params}:apply_notation_prop) =
  let map_params = List.combine apply_notation_prop.notation_prop_params apply_notation_prop_params
  in
  let replace = function 
    | String s -> " " ^ s ^ " "
    | Param _ as p -> "(" ^ (to_string_formula_prop (List.assoc p map_params)) ^ ")"
  in
  formula_from_string
    (List.fold_left (fun s e -> s^(replace e)) "" apply_notation_prop.notation_prop_semantique)

(**	@param l list of PVariables of g already instanciated in f *)
let instance_aux to_string_formula_prop formula_from_string f g =
  let rec instance_aux l f g  = match f, g 
    with
    | _, (PVar _ as g) -> begin
        try
          let (_, t) = List.find (fun (v1, _) -> v1 = g) l
          in
          if (t = f) then l
          else raise (Failed_Unification(f, g))
        with Not_found -> (g, f)::l (*g=Xi bound to f*)
      end
    | PNeg f1 , PNeg g1 -> instance_aux l f1 g1
    | PAnd(f1, f2) , PAnd(g1, g2) 
    | POr(f1, f2) , POr(g1, g2) 
    | PImpl(f1, f2) , PImpl(g1, g2) -> instance_aux (instance_aux l f2 g2) f1 g1
    | PApply_notation {apply_notation_prop=apply_notation_prop_f; apply_notation_prop_params = apply_notation_prop_params_f}, 
      PApply_notation {apply_notation_prop=apply_notation_prop_g; apply_notation_prop_params=apply_notation_prop_params_g} -> 
      if  (apply_notation_prop_f.notation_prop_name = apply_notation_prop_g.notation_prop_name) 
      then
        (List.fold_left (fun list_instances (f,g) -> instance_aux list_instances f g) l  (List.combine apply_notation_prop_params_f apply_notation_prop_params_g) )
      else raise (Failed_Unification(f, g))
    | PApply_notation f, g ->
      let f' = get_semantique_aux to_string_formula_prop formula_from_string  f in
      instance_aux l f' g
    | f,  PApply_notation g ->
      let g' = get_semantique_aux to_string_formula_prop formula_from_string g in
      instance_aux l f g'
    | _ -> raise (Failed_Unification(f, g))
  in
  try  
    instance_aux [] f g <> []
  with _ -> false


(**
   Print formatters and String conversions
*)
let rec printer_formula_prop ff f =
  let rec print_bin seq op f g =
    printer_formula_prop_aux ff seq f;
    Format.fprintf ff "%s" (" "^op^" ");
    printer_formula_prop_aux ff seq g
  and printer_formula_prop_aux ff seq =
    let print_par f =
      Format.fprintf ff "(";
      f();
      Format.fprintf ff ")";
    in
    function
    | PVar i -> Format.fprintf ff (if (0<=i && i<10) then "X_%d" else "X_{%d}") i
    | PMetaVar s -> Format.fprintf ff "\\mathbf{%s}" s
    | PNeg g -> Format.fprintf ff "\\lnot "; printer_formula_prop_aux ff "neg" g
    | PAnd(f, g) ->
      if (seq = "and" ||  seq ="init")
      then
        print_bin "and" "\\land" f g
      else
        print_par (fun () -> print_bin "and" "\\land" f g)
    | POr(f, g) ->
      if (seq = "or" || seq ="init")
      then
        print_bin "or" "\\lor" f g
      else
        print_par (fun () -> print_bin "or" "\\lor" f g)
    | PImpl(f, g) -> if (seq ="init")
      then
        print_bin "impl" "\\implies" f g
      else
        print_par (fun () -> print_bin "impl" "\\implies" f g)
    | (PApply_notation 
         {
           apply_notation_prop         = _  as n;
           apply_notation_prop_params  = _ as list_params  
         }) as f -> 
      let  replace  m = function 
        | Param a  -> begin
            try  
              match List.assoc (Param a) m
              with 
              | PVar _ | PMetaVar _ as v ->  to_string_formula_prop v
              | f      -> "(" ^ (to_string_formula_prop f) ^ ")"
            with Not_found -> failwith "apply_notations"
          end
        | String s  -> s 
      in
      let map_param_val = List.combine n.notation_prop_params list_params
      in 
      let notation_with_params_replaced = List.map (replace map_param_val ) n.notation_prop_notation
      in
      if (seq = "notation" || seq = "init") then 
        begin
          Format.fprintf ff "%s" (List.fold_left  (fun s t -> s ^ t) "" notation_with_params_replaced)
        end
      else print_par (fun () -> printer_formula_prop_aux ff "notation" f)
  in
  printer_formula_prop_aux ff "init" f
and to_string_formula_prop f =
  let b = Buffer.create 13
  in
  let ff = Format.formatter_of_buffer b
  in
  printer_formula_prop ff f;
  Format.pp_print_flush ff ();
  Buffer.contents b


let get_semantique = get_semantique_aux to_string_formula_prop !formula_from_string
let instance = instance_aux to_string_formula_prop !formula_from_string
