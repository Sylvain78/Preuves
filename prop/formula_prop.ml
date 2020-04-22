
type var_prop = 
  | PVVar of int
  | PVMetaVar of string

type formula_prop =
  | PVar of var_prop
  | PNeg of formula_prop
  | PAnd of formula_prop * formula_prop
  | POr of formula_prop * formula_prop
  | PImpl of formula_prop * formula_prop

(*SKE Example of notation
  "
  Notation equiv
  Params a b
  a \equiv b 
  (a \imply b)\\land(b \imply a)
  End
  "
*)

(**
   String conversion
*)
let to_string_formula_prop f =
  let rec to_string_bin seq op f g =
    (to_string_aux seq f) ^ " " ^ op ^ " " ^ (to_string_aux  seq g)
  and to_string_aux seq =
    let to_string_par f =
      "(" ^ f ^ ")"
    in
    function
    | PVar (PVVar i) ->  if (0<=i && i<10) then "X_" ^ (string_of_int i) else "X_{"  ^ (string_of_int i) ^ "}"
    | PVar (PVMetaVar s) -> "\\mathbb{" ^ s ^ "}"
    | PNeg g ->  "\\lnot " ^ (to_string_aux  "neg" g);
    | PAnd(f, g) ->
      if (seq = "and" ||  seq ="init")
      then
        to_string_bin "and" "\\land" f g
      else
        to_string_par (to_string_bin "and" "\\land" f g)
    | POr(f, g) ->
      if (seq = "or" || seq ="init")
      then
        to_string_bin "or" "\\lor" f g
      else
        to_string_par (to_string_bin "or" "\\lor" f g)
    | PImpl(f, g) -> if (seq ="init")
      then
        to_string_bin "impl" "\\implies" f g
      else
        to_string_par (to_string_bin "impl" "\\implies" f g)
  in
  to_string_aux  "init" f;;


(**
   Print formatters
*)
let printer_formula_prop ff f =
  let rec print_bin seq op f g =
    printer_formula_prop_aux ff seq f;
    Format.fprintf ff "%s" (" "^op^" ");
    printer_formula_prop_aux ff seq g;
  and printer_formula_prop_aux ff seq =
    let print_par f =
      Format.fprintf ff "(";
      f();
      Format.fprintf ff ")";
    in
    function
    | PVar (PVVar i) -> Format.fprintf ff (if (0<=i && i<10) then "X_%d" else "X_{%d}") i
    | PVar (PVMetaVar s) -> Format.fprintf ff "\\mathbb{%s}" s
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
  in
  printer_formula_prop_aux ff "init" f
