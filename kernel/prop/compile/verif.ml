open Kernel.Logic
open Kernel_prop_interp.Formula_prop
open Kernel_prop_interp
open Ast
open Theorem_compile

module Prop:(LOGIC 
             with type formula = formula_prop 
              and type notation = notation_prop
              and type demonstration = demonstration_compile
              and type theorem = theorem_compile
              and type step = step_compile) =
struct

  include Axioms_prop
  include Instance_notation_printers
  include Theorem_prop
  (*TODO open Substitution_prop*)
  include (Prop_parser : sig 
             val formula_from_string : string -> Formula_prop.formula_prop
             val notation_from_string : string -> Formula_prop.notation_prop
             (* TODO one day ... 
              * val save_parser : string -> unit
              * *)
           end)

  type formula = formula_prop
  type notation = notation_prop
  type demonstration = demonstration_compile
  type theorem = theorem_compile = Theorem of (formula_prop, demonstration_compile) theorem_logic [@@unboxed]
  let theorems = ref ([] : theorem list)
  type step = step_compile =   
    | Single of formula 
    | Call of {theorem : theorem; params :  formula list}
  type theorem_unproved = (formula, step list) Kernel.Logic.theorem_logic 

  exception Invalid_demonstration of theorem_unproved

  let (axioms:theorem list ref)  =  ref(List.map (function (Theorem_prop.Theorem t) -> 
      Theorem_compile.Theorem ({kind=t.kind;name=t.name; params=t.params;premisses=t.premisses;conclusion=t.conclusion; demonstration = ((Demonstration []):demonstration)})) !axioms_prop)
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

  let find_index_instance f list_props =
    let rec find_aux index l =
      match l with
        [] -> None
      | prop :: list_props' ->
        try Some (index,instance f prop.conclusion )
        with Failed_Unification _ -> find_aux (index+1) list_props'
    in
    find_aux 1 list_props

  (*instance of axiom*)
  let is_instance_of_axiom axioms f =
    match find_index_instance f (List.map (function Theorem_compile.Theorem t -> t) axioms)
    with
    | Some (i,subst) ->
      begin
        try
          let subst' = List.rev_map
              (function
                | PVar i, f -> (i,f)
                | _ -> raise Not_found)
              subst
          in
          Fmt_tty.setup_std_outputs ();
          let pp ppf i =
            Fmt.pf ppf "%a%a" Fmt.(styled `Cyan (styled `Bold string)) "Ax" Fmt.(parens int) i;
          in
          Logs.debug (fun m -> m "%a" ~header:"Ax" pp i);
          Some(Ax(i,subst'))
        with
        | Not_found -> None
      end
    | None -> None

  let find_index f lf =
    let rec find_aux i f l=
      match l with
      | [] -> None
      | f1::_ when f=f1 -> Some i
      | _::l1 -> find_aux (i+1) f l1
    in 
    find_aux 1 f lf

  (*cut*)
  let is_cut_aux demo f =
    let pp ppf f =
      Fmt.pf ppf "%a" Fmt.(styled `Red  (styled `Bold string)) (Kernel_prop_interp.Instance_notation_printers.to_string_formula_prop f);
    in
    Logs.debug (fun m -> m "%a" pp f);
    Logs.debug (fun m -> m "%s" "[");
    List.iter (function f -> Logs.debug (fun m -> m "%a\n" pp f)) demo;
    Logs.debug (fun m -> m "%s" "]");
    let find_cut f1 l =
      let rec search_impl i  = function
        | PImpl(g,h) :: l1  when f1=h ->
          Logs.debug (fun m -> m "%a" pp g);
          let left = find_index g l 
          in
          begin
            match left with 
            | None -> search_impl (i+1) l1
            | Some lind -> 
              begin 
                lind , i
              end
          end
        | _ :: l1 -> search_impl (i+1) l1
        | [] -> raise Not_found
      in
      search_impl 1 l
    in
    try
      let (li, ri) = find_cut f (List.map expand_all_notations demo)
      in 
      let pp ppf (i,j) =
        Fmt.pf ppf "%a%a" Fmt.(styled `Green (styled `Bold string)) "Cut" Fmt.(parens (pair ~sep:Fmt.comma int int)) (i,j);
      in
      Logs.debug (fun m -> m "%a" pp (li,ri));
      Some(Cut(li,ri))
    with
    | Not_found -> None

  (*hypotesis*)
  let is_hypothesis hypotheses f =
    match find_index f hypotheses
    with
    | None -> None
    | Some i -> Some (HypUse i)

  (*known theorem*)
  let is_known_theorem_aux theorems f =
    let rec find_aux i f l=
      match l with
      | [] -> None
      | f1::_ when f=f1.conclusion -> Some(Known i)
      | _::l1 -> find_aux (i+1) f l1
    in find_aux 1 f (List.map (function Theorem_compile.Theorem th -> th) theorems)

  (*instance of theorem*)
  let is_instance_of_theorem_aux theorems  f =
    let find_index_instance f list_theorems =
      let rec find_aux index l =
        match l with
          [] -> None
        | th :: list_theorems' ->
          try Some (index,instance f th.conclusion )
          with Failed_Unification _ -> find_aux (index+1) list_theorems'
      in
      find_aux 1 list_theorems
    in
    match find_index_instance f (List.map (function Theorem_compile.Theorem th -> th) theorems)
    with
    | Some (i,subst) ->
      begin
        try
          let subst' = List.rev subst
          in
          Fmt_tty.setup_std_outputs ();
          let pp ppf i =
            Fmt.pf ppf "%a%a" Fmt.(styled `Cyan (styled `Bold string)) "Th" Fmt.(parens int) i;
          in
          Logs.debug (fun m -> m "%a" ~header:"Th" pp i);
          Some(Th(i,subst'))
        with
        | Not_found -> None
      end
    | None -> None

  let compile ~speed ?(hypotheses=[]) ~(demonstration: step list) () =
    let rec compile_aux ~depth ~(proof : demonstration) ~proved = 
      let lift n  = function
        | ( Ax _ | BeginHyp _ | HypDecl _ | HypUse _ | EndHyp | Th _) as kpt -> kpt
        | Known n' -> Known (n+n')
        | Cut(i,j) -> Cut(i+n,j+n)
      in
      function
      | [] -> proof
      | (Single f) :: demo_tail ->
        Logs.debug (fun m -> m "formule expansée : %s" (Kernel_prop_interp.Instance_notation_printers.to_string_formula_prop (expand_all_notations f)));
        let  proof_term = List.find_map (fun func -> func (expand_all_notations f)) 
            [ 
              is_instance_of_axiom !axioms; 
              is_cut_aux (List.rev proved);
              is_hypothesis hypotheses; 
              is_known_theorem_aux !theorems; 
              is_instance_of_theorem_aux !theorems;
            ]
        in
        begin
          match proof_term with
          | Some step_compiled -> 
            Logs.debug(fun m -> pp_formula Fmt.stdout f;Fmt.flush Fmt.stdout ();m "proof_term");
            compile_aux ~depth:(depth+1) ~proved:(f::proved)  ~proof:(match proof with Demonstration proof ->  Demonstration (([step_compiled],(Single f)) :: proof)) demo_tail
          | None -> 
            Logs.err (fun m -> pp_formula Fmt.stdout f;m "compile: Invalid_demonstration ");
            failwith "formula not compilable (msg TODO)"
        end
      | Call {theorem; params } :: l ->
        let theorem = match theorem with Theorem t -> t
        in
        let substituted = Substitution_prop.simultaneous_substitution_formula_prop ~vars:theorem.params ~terms:params
        in
        match speed with
        | Fast -> (failwith "to implement"  (*compile_aux ~depth:(depth+1) l*))
        | Paranoid -> ignore (substituted,lift);failwith "to implement"
        (*BeginHyp (List.length theorem.premisses) :: (List.map (fun p -> HypDecl(substituted p)) theorem.premisses)  @
          (List.map (function kpt -> lift (depth + 1 + (*BeginHyp*)+ (List.length theorem.premisses)) kpt) theorem.demonstration) 
          @ (EndHyp :: (compile_aux ~depth l))  *)
    in compile_aux ~depth:0 ~proved:[] ~proof:(Demonstration []) demonstration

  let verif_compile ~name ~(hypotheses:formula list) ~(proved:(formula list * step) list) ~(to_prove:demonstration) ~(original_proof:theorem_unproved) =
    let formula_stack = ref []
    and hypotheses_stack = Stack.create ()
    in
    Stack.push (Array.of_list hypotheses) hypotheses_stack;
    let formula_from_proof_term step_index 
        (theorems : theorem list) = 
      let hyp = ref 0
      in
      function
      | Known i -> Some (match List.nth theorems (i-1) with Theorem t -> t).conclusion
      | Ax (i,subst) ->
        let Theorem axiom = List.nth !axioms_prop (i-1)
        in
        let  lv,lt = List.split subst
        in
        Some(Kernel_prop_interp.Substitution_prop.simultaneous_substitution_formula_prop ~vars:(List.map (fun i -> PVar i) lv) ~terms:lt axiom.conclusion)
      | Th (i,subst) ->
        let theorem = 
          match List.nth theorems (i-1) 
          with Theorem t -> t
        in
        let  lv,lt = List.split subst
        in
        let substitute_in = Kernel_prop_interp.Substitution_prop.simultaneous_substitution_formula_prop ~vars:lv ~terms:lt 
        in
        (*verify premisses*)
        if not (List.for_all (fun p -> List.mem (substitute_in p) !formula_stack) theorem.premisses)
        then 
          begin
            failwith ( theorem.name ^ "premisse " ^ "not verified")
          end;
        Some (substitute_in theorem.conclusion)
      | Cut(j,k) -> 
        let rev_stack = List.rev !formula_stack
        in
        let fj,fk= List.nth rev_stack (j-1), List.nth rev_stack (k-1)
        in
        begin
          match fk with
          | PImpl(f,g) when f=fj -> Some g
          | _ -> failwith @@ "Proof term " ^ "Cut(" ^ (string_of_int j) ^ ", " ^ (string_of_int k) ^ ")"
        end
      | BeginHyp n -> 
        Stack.push (Array.make n (PVar 0)) hypotheses_stack ;
        None
      | HypDecl f -> 
        if (List.mem f !formula_stack) 
        then 
          begin
            (Stack.top hypotheses_stack).(!hyp) <- f ;
            incr hyp;
            Some f
          end
        else 
          begin
            Logs.err (fun m ->  m ("verif : premisse %a not verified at step %d")  pp_formula f step_index);
            raise (Invalid_demonstration ({original_proof
                                           with conclusion=f 
                                              ;demonstration =
                                                 List.of_seq @@Seq.take step_index @@ List.to_seq @@ original_proof.demonstration}))
          end
      | HypUse i -> Some (Stack.top hypotheses_stack).(i)
      | EndHyp -> hyp:= 0; None
    in
    List.iteri 
      (fun  step_index proof_term ->
         match formula_from_proof_term step_index !theorems proof_term 
         with
         | Some f -> formula_stack := f :: !formula_stack
         | None -> ()
      )
      (failwith "to_prove");
    Ok (failwith "original_proof")

  let kernel_prop_compile_verif ~speed theorem_unproved =
    let compiled_proof = 
      compile ~speed ~demonstration:(failwith "theorem_unproved.demonstration") ()
    in
    verif_compile ~name:theorem_unproved.name ~hypotheses:theorem_unproved.premisses ~proved:[] ~to_prove:(compiled_proof) ~original_proof:theorem_unproved
  ;;

  let add_axiom ax = axioms := ax :: !axioms
  let is_instance_axiom f =
    match is_instance_of_axiom !axioms f 
    with 
    | Some _ -> true 
    | None -> false 

  let print_invalid_demonstration = Theory.Prop.print_invalid_demonstration;;

  Printexc.register_printer (print_invalid_demonstration)

  (* f is at the end of the proof *)
  let is_formula_at_end f t =
    let rev_t = List.rev t
    in
    try
      match List.hd rev_t
      with 
      | Single g when g = f -> true
      | _ -> failwith "to implement"
    with
    | Failure _ -> false

  let verif ~speed (theorem_unproved: theorem_unproved) = 
    if not (is_formula_at_end theorem_unproved.conclusion (failwith " theorem_unproved.demonstration"))
    then 
      Error ("Formula is not at the end of the proof", Invalid_demonstration (failwith "theorem_unproved"))
    else
      kernel_prop_compile_verif ~speed (failwith "theorem_unproved")

  let string_to_formula = formula_from_string
  let formula_to_string = to_string_formula_prop
  let printer_formula = printer_formula_prop
  let string_to_notation = notation_from_string
  let printer_demonstration ff d=
    failwith "to implement : (Format.pp_print_list ~pp_sep:Format.pp_print_newline printer_formula) ff d"
  let printer_step = failwith "to implement"
end
