type notation_prop_element = Param of string | String of string
type formula_prop =
  | PVar of int
  | PNeg of formula_prop
  | PAnd of formula_prop * formula_prop
  | POr of formula_prop * formula_prop
  | PImpl of formula_prop * formula_prop
  | Abuse_notation of notation_abuse_prop
 and notation_abuse_prop =
         {
           notation_prop : string;
           notation_prop_params : formula_prop list; (*SKE TODO create database of notations*)
         }
 and notation_prop =
         Notation of 
         {
           notation_prop_name : string;
           notation_prop_params : notation_prop_element list;
           notation_prop_notation : notation_prop_element list;
           notation_prop_semantique : notation_prop_element list;
         }
;;
(*SKE Example
"
Notation equiv
Params a b
a \equiv b 
(a \imply b)/\\(b \imply a)
End
"
*)
(**
   Print formatters
*)
let printer_formula_prop ff f =
  let rec print_bin seq op f g =
    printer_formula_prop_aux ff seq f;
    Format.fprintf ff "%s" (" "^op^" ");
    printer_formula_prop_aux ff seq g;
  and printer_formula_prop_aux ff seq =
    let	print_par f =
      Format.fprintf ff "(";
      f();
      Format.fprintf ff ")";
    in
    function
    | PVar i -> Format.fprintf ff "P%d" i
    | PNeg g -> Format.fprintf ff "!"; printer_formula_prop_aux ff "neg" g;
    | PAnd(f, g) ->
      if (seq = "and" ||  seq ="init")
      then
        print_bin "and" "/\\" f g
      else
        print_par (fun () -> print_bin "and" "/\\" f g)
    | POr(f, g) ->
      if (seq = "or" || seq ="init")
      then
        print_bin "or" "\\/" f g
      else
        print_par (fun () -> print_bin "or" "\\/" f g)
    | PImpl(f, g) -> if (seq ="init")
      then
        print_bin "impl" "=>" f g
      else
        print_par (fun () -> print_bin "impl" "=>" f g);
  in
  printer_formula_prop_aux ff "init" f

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
    | PVar i ->  "P" ^ (string_of_int i)
    | PNeg g ->  "!" ^ (to_string_aux  "neg" g);
    | PAnd(f, g) ->
      if (seq = "and" ||  seq ="init")
      then
        to_string_bin "and" "/\\" f g
      else
        to_string_par (to_string_bin "and" "/\\" f g)
    | POr(f, g) ->
      if (seq = "or" || seq ="init")
      then
        to_string_bin "or" "\\/" f g
      else
        to_string_par (to_string_bin "or" "\\/" f g)
    | PImpl(f, g) -> if (seq ="init")
      then
        to_string_bin "impl" "=>" f g
      else
        to_string_par (to_string_bin "impl" "=>" f g);
  in
  to_string_aux  "init" f;;

