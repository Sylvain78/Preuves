open OUnit2
open First_order.Formula
open First_order.Signature
open Util

module FormulaTest = struct
  include Formula(SignatureMinimal)
  let r = SignatureMinimal.of_string "s"
  let h = SignatureMinimal.of_string "h"
  let () = SignatureMinimal.binary_relations := [r]; 
    SignatureMinimal.operations := [(h,1)];
    let  printer_h ff = function
      | TOperation(op, [x;y]) when op = SignatureMinimal.of_string "h"-> 
        Format.fprintf ff "h ("; print_term ff x; Format.fprintf ff ", " ; print_term ff y; Format.fprintf ff ")"
      | _ -> failwith "printer_h appelé sur autre chose que l'opérateur h"
    in
    Hashtbl.add printers_operations h printer_h

end
open FormulaTest

let printer =(fun s ->  (printer_first_order_formula Format.str_formatter s; let s = Format.flush_str_formatter () in s))   
let printer_base_term =(fun s ->  (print_term Format.str_formatter s; let s = Format.flush_str_formatter () in s))   

let v1 = Var (new_var())
let v2 = Var (new_var())
let v3 = Var (new_var())
let v4 = Var (new_var())
let v11 = Var 11

let x1,x2,x3,x4,x11 = TV v1, TV v2, TV v3, TV v4, TV v11
let f1 = Eq(x1, x2)
let f2 = Eq(x3, x4)

let g1 = FForall(v1, FAtomic_formula(Eq(x1, x2)))
let g2 = FExists(v1, FAtomic_formula(Eq(x1, x2)))

let nf1 = FNeg (FAtomic_formula f1)
let nf2 = FNeg (FAtomic_formula f2)

let test_initialization_printers_relations test_ctxt =
  assert_equal 0 (Hashtbl.length printers_relations)

let test_simultaneous_substitution_atomic_formula_eq test_ctxt =
  assert_equal f2 (simultaneous_substitution_atomic_formula [v1 ; v2] [x3 ; x4] f1)

let test_simultaneous_substitution_atomic_formula_relation test_ctxt =
  assert_equal (Relation(r,[x3 ; x4])) (simultaneous_substitution_atomic_formula [v1 ; v2] [x3 ; x4] (Relation(r, [x1 ; x2])))

let test_simultaneous_substitution_formula test_ctxt =
  assert_equal ~printer:printer (FAtomic_formula f2) (simultaneous_substitution_formula [v1 ; v2] [TV(v3) ; TV(v4)] (FAtomic_formula f1))

let test_simultaneous_substitution_formula_neg test_ctxt =
  assert_equal ~printer:printer nf2 (simultaneous_substitution_formula [v1 ; v2] [TV(v3) ; TV(v4)]  nf1)

let test_simultaneous_substitution_formula_and test_ctxt =
  assert_equal ~printer:printer (FAnd((FAtomic_formula f2), (FAtomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2] 
                                                                                   (FAnd((FAtomic_formula f1), (FAtomic_formula f2))))

let test_simultaneous_substitution_formula_or test_ctxt =
  assert_equal ~printer:printer (FOr((FAtomic_formula f2), (FAtomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2] 
                                                                                  (FOr((FAtomic_formula f1), (FAtomic_formula f2))))

let test_simultaneous_substitution_formula_imply test_ctxt =
  assert_equal ~printer:printer (FImply((FAtomic_formula f2), (FAtomic_formula f1))) (simultaneous_substitution_formula [v1 ; v2 ; v3 ;v4 ] [x3 ; x4 ; x1 ; x2]
                                                                                     (FImply((FAtomic_formula f1), (FAtomic_formula f2))))

let test_simultaneous_substitution_formula_capturing test_ctxt =
  let f = FForall(v1,  FAtomic_formula(Eq(x1, x1)))
  in
  let f_susbt =  (simultaneous_substitution_formula [v1] [x2] f)
  in
  match f_susbt with 
  | FForall (v,FAtomic_formula(Eq(TV v',TV v''))) ->
    assert_equal ~printer:(fun v -> printer_base_term (TV v)) v v';
    assert_equal ~printer:(fun v -> printer_base_term (TV v)) v v'';
    assert_bool "" (v != v2)
  | _ -> assert_failure "Unreachable"


let test_simultaneous_substitution_formula_capturing_inside_terms test_ctxt =
  let f = FForall(v1,  FAtomic_formula(Eq(x1, x2)))
  in
  let f_susbt = simultaneous_substitution_formula [v2] [TOperation (h,[x1])] f
  in
  assert_equal ~printer:printer f_susbt f_susbt


let test_simultaneous_substitution_formula_forall_nominal test_ctxt =
  let ff1 = (FForall(v1, FAtomic_formula f1)) 
  in
  let f'1= (simultaneous_substitution_formula [v1 ] [x2]  ff1)
  in
  let new_variable = match f'1 with FForall(v,_) -> v | _ -> failwith "unreachable"
  in
  assert_equal ~printer:printer (FForall(new_variable, FAtomic_formula(Eq(TV new_variable, x2)))) f'1

let test_simultaneous_substitution_formula_forall_nominal_2 test_ctxt =
  let ff2 = (FForall(v1, FAtomic_formula f1)) 
  in
  let f'2 = (simultaneous_substitution_formula [v1 ; v2 ] [x2 ; x3]  ff2)
  in
  let new_variable = match f'2 with FForall(v,_) -> v | _ -> failwith "unreachable"
  in
  assert_equal ~printer:printer (FForall(new_variable, FAtomic_formula(Eq(TV new_variable, x3)))) f'2 

let test_simultaneous_substitution_formula_forall_nominal_3 test_ctxt =
  let f = g1
  in 
  try
    let f' = simultaneous_substitution_formula [v2] [TOperation(h,[x3;x1])]  f 
    in 
    match f' with (FForall(v,_)) ->
      let f2 =  FForall(v,FAtomic_formula(Eq(TV v, TOperation(h,[x3;x1]))))  
      in 
      assert_equal ~printer:printer f2 f' 
  with e -> raise e

let test_simultaneous_substitution_formula_forall_nominal_4 test_ctxt =
  let f = g1
  in 
  try
    let f' = simultaneous_substitution_formula [v2] [TOperation(h,[x3;x4])]  f 
    in 
    let f2 =  FForall(v1,FAtomic_formula(Eq(x1, TOperation(h,[x3;x4]))))  
    in 
    assert_equal ~printer:printer f2 f' 
  with e -> raise e

let
  test_simultaneous_substitution_formula_exists_nominal
    test_ctxt = let ff1 = (FExists(v1, FAtomic_formula f1)) 
  in
  let f'1= (simultaneous_substitution_formula [v1 ] [x2]  ff1)
  in
  let new_variable = match f'1 with FExists(v,_) -> v | _ -> failwith "unreachable"
  in
  assert_equal ~printer:printer (FExists(new_variable, FAtomic_formula(Eq(TV new_variable, x2)))) f'1

let test_simultaneous_substitution_formula_exists_nominal_2 test_ctxt =
  let ff2 = (FExists(v1, FAtomic_formula f1)) 
  in
  let f'2 = (simultaneous_substitution_formula [v1 ; v2 ] [x2 ; x3]  ff2)
  in
  let new_variable = match f'2 with FExists(v,_) -> v | _ -> failwith "unreachable"
  in
  assert_equal ~printer:printer (FExists(new_variable, FAtomic_formula(Eq(TV new_variable, x3)))) f'2 


let test_simultaneous_substitution_formula_exists_nominal_3 test_ctxt =
  let f = g2
  in 
  try
    let f' = simultaneous_substitution_formula [v2] [TOperation(h,[x3;x1])]  f 
    in 
    match f' with (FExists(v,_)) ->
      let f2 =  FExists(v,FAtomic_formula(Eq(TV v, TOperation(h,[x3;x1]))))  
      in 
      assert_equal ~printer:printer f2 f' 
    | _ -> failwith "invalid result" 
  with e -> raise e

let test_simultaneous_substitution_formula_exists_nominal_4 test_ctxt =
  let f = g2
  in 
  try
    let f' = simultaneous_substitution_formula [v2] [TOperation(h,[x3;x4])]  f 
    in 
    let f2 =  FExists(v1,FAtomic_formula(Eq(x1, TOperation(h,[x3;x4]))))  
    in 
    assert_equal ~printer:printer f2 f' 
  with e -> raise e



let test_free_variables_of_atomic_formula_eq test_ctxt =
  assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_atomic_formula (Eq(x1,x2)))

let test_free_variables_of_atomic_formula_relation test_ctxt =
  assert_equal (FormulaTest.SetVar.of_list [v1 ; v2 ; v3]) (free_variables_of_atomic_formula (Relation(SignatureMinimal.of_string "",[x1;x2;x2;x3])))

let test_free_variables_of_formula_atomic test_ctxt =
  assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_formula (FAtomic_formula f1))

let test_free_variables_of_formula_neg test_ctxt =
  assert_equal (FormulaTest.SetVar.of_list [v1 ; v2]) (free_variables_of_formula (nf1))

let test_free_variables_of_formula_bin test_ctxt =
  assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (FAnd (FAtomic_formula f1, FAtomic_formula f2))));
  assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (FOr  (FAtomic_formula f1, FAtomic_formula f2))));
  assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.of_list [v1 ; v2 ; v3 ; v4]) (free_variables_of_formula (FImply (FAtomic_formula f1, FAtomic_formula f2))))

let test_free_variables_of_formula_quant test_ctxt =
  assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.singleton v2) (free_variables_of_formula g1));
  assert_equal 0 (FormulaTest.SetVar.compare (FormulaTest.SetVar.singleton v2) (free_variables_of_formula g2))

let test_term_free_for_var_atomic test_ctxt =
  let t,x = x1,v1
  in
  assert_bool "term not free for var [Atomic formula]" (term_free_for_var t x (FAtomic_formula f1));
  assert_bool "term not free for var [FNeg]" (term_free_for_var t x nf1);
  assert_bool "term not free for var [FAnd]" (term_free_for_var t x (FAnd(nf1,nf2)));
  assert_bool "term not free for var [FAnd]" (term_free_for_var t x (FOr(nf1,nf2)));
  assert_bool "term not free for var [FAnd]" (term_free_for_var t x (FImply(nf1,nf2)));
  assert_bool "term not free for var [FForall not]" (not (term_free_for_var x1 x g1));
  assert_bool "term not free for var [FForall]" (term_free_for_var x2 x g1);
  assert_bool "term not free for var [FExists not]" (not (term_free_for_var x1 x g2));
  assert_bool "term not free for var [FExists]" (term_free_for_var x2 x g2)

let test_printer_first_order_atomic_formula_eq test_ctxt =
  ignore (Format.flush_str_formatter ()) ;
  (printer_first_order_atomic_formula Format.str_formatter f1);
  let s = Format.flush_str_formatter ()  
  in
  assert_equal ~printer:(fun s -> s) s "X_1 = X_2"

let test_printer_first_order_atomic_formula_relation_bin test_ctxt =
  ignore (Format.flush_str_formatter ()) ;
  (printer_first_order_atomic_formula Format.str_formatter (Relation(r,[x1;x2])));
  let s = Format.flush_str_formatter ()
  in
  assert_equal s "X_1 s X_2"

let test_printer_first_order_atomic_formula_relation_bin_11 test_ctxt =
  ignore (Format.flush_str_formatter ()) ;
  (printer_first_order_atomic_formula Format.str_formatter (Relation(r,[x1;x11])));
  let s = Format.flush_str_formatter ()
  in
  assert_equal ~printer:(fun s -> s) "X_1 s X_{11}" s

let test_printer_first_order_atomic_formula_relation test_ctxt =
  (printer_first_order_atomic_formula Format.str_formatter (Relation(r,[])));
  let s = Format.flush_str_formatter ()
  in
  assert_equal s "s()"

let test_printer_first_order_formula_neg test_ctxt =
  (printer_first_order_formula Format.str_formatter (nf1));
  let s = Format.flush_str_formatter () 
  in
  assert_equal s "\\lnot (X_1 = X_2)"

let test_printer_first_order_formula_and test_ctxt =
  (printer_first_order_formula Format.str_formatter (FAnd (FAtomic_formula f1, FAtomic_formula f2)));
  let s = Format.flush_str_formatter () 
  in
  assert_equal  s "X_1 = X_2 \\land X_3 = X_4"

let test_printer_first_order_formula_and_imply_equiv test_ctxt =
  (printer_first_order_formula Format.str_formatter (FAnd(FImply(FAtomic_formula f1,FAtomic_formula f2), FImply(FAtomic_formula f2,FAtomic_formula f1))));
  let s = Format.flush_str_formatter () 
  in
  assert_equal  s "X_1 = X_2 <=> X_3 = X_4"

let test_printer_first_order_formula_and_imply test_ctxt =
  (printer_first_order_formula Format.str_formatter (FAnd(FImply(FAtomic_formula f1,FAtomic_formula f2), FImply(nf1,nf2))));
  let s = Format.flush_str_formatter () 
  in
  assert_equal  s "(X_1 = X_2 => X_3 = X_4) \\land (\\lnot (X_1 = X_2) => \\lnot (X_3 = X_4))"

let test_printer_first_order_formula_or_and_imply test_ctxt =
  (printer_first_order_formula Format.str_formatter (FOr(FAtomic_formula f1,FAnd(FImply(FAtomic_formula f1,FAtomic_formula f2),FImply(FAtomic_formula f1,FAtomic_formula f2)))));
  let s = Format.flush_str_formatter () 
  in
  assert_equal  s "X_1 = X_2 \\lor ((X_1 = X_2 => X_3 = X_4) \\land (X_1 = X_2 => X_3 = X_4))"

let test_printer_first_order_formula_or_and test_ctxt =
  (printer_first_order_formula Format.str_formatter (FOr(FAtomic_formula f1,FAnd(FAtomic_formula f1,FAtomic_formula f2))));
  let s = Format.flush_str_formatter () 
  in
  assert_equal s "X_1 = X_2 \\lor (X_1 = X_2 \\land X_3 = X_4)"

let test_printer_first_order_formula_and_or test_ctxt =
  (printer_first_order_formula Format.str_formatter (FAnd(FAtomic_formula f1,FOr(FAtomic_formula f1,FAtomic_formula f2))));
  let s = Format.flush_str_formatter () 
  in
  assert_equal s "X_1 = X_2 \\land (X_1 = X_2 \\lor X_3 = X_4)"

let test_printer_first_order_formula_and_and test_ctxt =
  (printer_first_order_formula Format.str_formatter (FAnd(FAnd(FAtomic_formula f1, FAtomic_formula f2), nf1)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal s "X_1 = X_2 \\land X_3 = X_4 \\land \\lnot (X_1 = X_2)"

let test_printer_first_order_formula_imply_imply test_ctxt =
  (printer_first_order_formula Format.str_formatter (FImply(FImply(FAtomic_formula f1, FAtomic_formula f2), FAtomic_formula f1)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal s "(X_1 = X_2 => X_3 = X_4) => X_1 = X_2"

let test_printer_first_order_formula_forall test_ctxt =
  (printer_first_order_formula Format.str_formatter g1);
  let s = Format.flush_str_formatter ()
  in 
  assert_equal  s "\\forall X_1, X_1 = X_2"

let test_printer_first_order_formula_forall_forall test_ctxt =
  (printer_first_order_formula Format.str_formatter (FForall(v2, g1)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "\\forall X_2, X_1, X_1 = X_2"

let test_printer_first_order_formula_and_forall test_ctxt =
  (printer_first_order_formula Format.str_formatter  (FAnd(FAtomic_formula(f1), g1)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "X_1 = X_2 \\land (\\forall X_1, X_1 = X_2)" 

let test_printer_first_order_formula_forall_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter (FForall((Metavar "s"), FAtomic_formula(f1))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "\\forall s, X_1 = X_2"

let test_printer_first_order_formula_forall_forall_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter (FForall(v1, FForall (Metavar "s", FAtomic_formula(f1)))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) "\\forall X_1, s, X_1 = X_2" s

let test_printer_first_order_formula_and_forall_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter  (FAnd(FAtomic_formula(f1), (FForall(Metavar "s", FAtomic_formula(f1))))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) "X_1 = X_2 \\land (\\forall s, X_1 = X_2)" s

let test_printer_first_order_formula_exists test_ctxt =
  (printer_first_order_formula Format.str_formatter g2);
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "\\exists X_1, X_1 = X_2"

let test_printer_first_order_formula_exists_exists test_ctxt =
  (printer_first_order_formula Format.str_formatter (FExists(v2, g2)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "\\exists X_2, X_1, X_1 = X_2"

let test_printer_first_order_formula_and_exists test_ctxt =
  (printer_first_order_formula Format.str_formatter  (FAnd(FAtomic_formula(f1), g2)));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) "X_1 = X_2 \\land (\\exists X_1, X_1 = X_2)" s

let test_printer_first_order_formula_exists_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter (FExists(Metavar "s", FAtomic_formula(f1))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal s "\\exists s, X_1 = X_2"

let test_printer_first_order_formula_exists_exists_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter (FExists(v1, FExists (Metavar "s", FAtomic_formula(f1)))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "\\exists X_1, s, X_1 = X_2"

let test_printer_first_order_formula_and_exists_meta test_ctxt =
  (printer_first_order_formula Format.str_formatter  (FAnd(FAtomic_formula(f1), (FExists(Metavar "s", FAtomic_formula(f1))))));
  let s = Format.flush_str_formatter ()
  in 
  assert_equal ~printer:(fun s -> s) s "X_1 = X_2 \\land (\\exists s, X_1 = X_2)"

let test_equiv test_ctxt =
  assert_equal ~printer:printer (FAnd(FImply(nf1,nf2), FImply(nf2,nf1))) (equiv nf1 nf2) 

let formula_suite = "First order formula tests">:::
                    [ 
                      "Test of initialization of printers_relations">::test_initialization_printers_relations;
                      "test_simultaneous_substitution_atomic_formula (case Eq) ">::test_simultaneous_substitution_atomic_formula_eq; 
                      "test_simultaneous_substitution_atomic_formula (case Relation)">::test_simultaneous_substitution_atomic_formula_relation;
                      "test_simultaneous_substitution_formula (case FAtomic_formula">::test_simultaneous_substitution_formula;
                      "test_simultaneous_substitution_formula_neg">::test_simultaneous_substitution_formula_neg;
                      "test_simultaneous_substitution_formula_and">::test_simultaneous_substitution_formula_and;
                      "test_simultaneous_substitution_formula_or">::test_simultaneous_substitution_formula_or;
                      "test_simultaneous_substitution_formula_imply">::test_simultaneous_substitution_formula_imply;
                      "test_simultaneous_substitution_formula_forall_nominal">::test_simultaneous_substitution_formula_forall_nominal;
                      "test_simultaneous_substitution_formula_forall_nominal2">::test_simultaneous_substitution_formula_forall_nominal_2;
                      "test_simultaneous_substitution_formula_forall_nominal3">::test_simultaneous_substitution_formula_forall_nominal_3;
                      "test_simultaneous_substitution_formula_forall_nominal4">::test_simultaneous_substitution_formula_forall_nominal_4;
                      "test_simultaneous_substitution_formula_exists_nominal">::test_simultaneous_substitution_formula_exists_nominal;
                      "test_simultaneous_substitution_formula_exists_nominal2">::test_simultaneous_substitution_formula_exists_nominal_2;
                      "test_simultaneous_substitution_formula_exists_nominal3">::test_simultaneous_substitution_formula_exists_nominal_3;
                      "test_simultaneous_substitution_formula_exists_nominal4">::test_simultaneous_substitution_formula_exists_nominal_4;
                      "test_free_variables_of_atomic_formula_eq">::test_free_variables_of_atomic_formula_eq;
                      "test_simultaneous_substitution_formula_capturing">::test_simultaneous_substitution_formula_capturing;
                      "test_free_variables_of_atomic_formula_relation">::test_free_variables_of_atomic_formula_relation;
                      "test_free_variables_of_formula_atomic">::test_free_variables_of_formula_atomic;
                      "test_free_variables_of_formula_neg>">::test_free_variables_of_formula_neg;
                      "test_free_variables_of_formula_bin">::test_free_variables_of_formula_bin;
                      "test_free_variables_of_formula_quant">::test_free_variables_of_formula_quant;
                      "test_term_free_for_var_atomic">::test_term_free_for_var_atomic;
                      "test_printer_first_order_atomic_formula_eq">::test_printer_first_order_atomic_formula_eq;
                      "test_printer_first_order_atomic_formula_relation_bin">::test_printer_first_order_atomic_formula_relation_bin;
                      "test_printer_first_order_atomic_formula_relation_bin_11">::test_printer_first_order_atomic_formula_relation_bin_11;
                      "test_printer_first_order_atomic_formula_relation">::test_printer_first_order_atomic_formula_relation;
                      "test_printer_first_order_formula_neg">::test_printer_first_order_formula_neg;
                      "test_printer_first_order_formula_and">::test_printer_first_order_formula_and;
                      "test_printer_first_order_formula_and_imply_equiv">::test_printer_first_order_formula_and_imply_equiv;
                      "test_printer_first_order_formula_and_imply">::test_printer_first_order_formula_and_imply;
                      "test_printer_first_order_formula_and_and">::test_printer_first_order_formula_and_and;
                      "test_printer_first_order_formula_or_and_imply">::test_printer_first_order_formula_or_and_imply;
                      "test_printer_first_order_formula_or_and">::test_printer_first_order_formula_or_and;
                      "test_printer_first_order_formula_and_or">::test_printer_first_order_formula_and_or;
                      "test_printer_first_order_formula_imply_imply">::test_printer_first_order_formula_imply_imply;

                      "test_printer_first_order_formula_forall">::test_printer_first_order_formula_forall;
                      "test_printer_first_order_formula_forall_forall">::test_printer_first_order_formula_forall_forall;
                      "test_printer_first_order_formula_and_forall">::test_printer_first_order_formula_and_forall;

                      "test_printer_first_order_formula_forall_meta">::test_printer_first_order_formula_forall_meta;
                      "test_printer_first_order_formula_forall_forall_meta">::test_printer_first_order_formula_forall_forall_meta;
                      "test_printer_first_order_formula_and_forall_meta">::test_printer_first_order_formula_and_forall_meta;

                      "test_printer_first_order_formula_exists">::test_printer_first_order_formula_exists;
                      "test_printer_first_order_formula_exists_exists">::test_printer_first_order_formula_exists_exists;
                      "test_printer_first_order_formula_and_exists">::test_printer_first_order_formula_and_exists;

                      "test_printer_first_order_formula_exists_meta">::test_printer_first_order_formula_exists_meta;
                      "test_printer_first_order_formula_exists_exists_meta">::test_printer_first_order_formula_exists_exists_meta;
                      "test_printer_first_order_formula_and_exists_meta">::test_printer_first_order_formula_and_exists_meta;
                      "test_equiv">::test_equiv;

                    ]

let () = run_test_tt_main formula_suite
