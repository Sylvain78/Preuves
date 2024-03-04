open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp.Instance_notation_printers

type kernel_proof_term =
  | Ax of int * (int * formula_prop) list (*instantce of axiom i, with list of simulatenous substitution X_j => F_k*)
  | Th of int * (formula_prop * formula_prop) list (*instantce of theorem i, with list of simulatenous substitution for params *)
  | Known of int (*formula already known in the demonstration*)
  | Cut of int * int (*cut Fj, (Fj=>Fk) : Fk*)
  | BeginHyp of int
  | HypDecl of formula_prop (*declaration of a hypothesis*)
  | HypUse of int (*use of a hypothesis*)
  | EndHyp

let printer_kernel_proof_term out =
  function 
  | Ax(i,l) -> Format.fprintf out "Ax(%d,[%a])" i 
                 (fun out list_proof_term -> 
                    Format.pp_print_list 
                      ~pp_sep:(fun out () -> Format.pp_print_char out ',') 
                      (fun out (i,f) -> Format.fprintf out "(%d,\"%a\")" i printer_formula_prop f) 
                      out list_proof_term) l; 
    Format.fprintf out "%s" (Format.flush_str_formatter()) 
  | Th(i,l) -> Format.fprintf out "Th(%d,[%a])" i 
                 (fun out list_proof_term -> 
                    Format.pp_print_list 
                      ~pp_sep:(fun out () -> Format.pp_print_char out ',') 
                      (fun out (f,g) -> Format.fprintf out "(%a,\"%a\")" printer_formula_prop f printer_formula_prop g) 
                      out list_proof_term) l; 
    Format.fprintf out "%s" (Format.flush_str_formatter()) 
  | Known i -> Format.fprintf out "Known(%d)" i
  | Cut(i,j) -> Format.fprintf out "Cut(%d,%d)" i j
  | BeginHyp n -> Format.fprintf out "Begin Hypotheses(%d)" n
  | HypDecl f -> Format.fprintf out "Hypothese %a"printer_formula_prop f
  | HypUse i -> Format.fprintf out "Hyp(%d)" i
  | EndHyp -> Format.fprintf out "End hypotheses"

type kernel_compiled_proof =
  {
    theorem : formula_prop ;
    demonstration : kernel_proof_term  list ;
  }
