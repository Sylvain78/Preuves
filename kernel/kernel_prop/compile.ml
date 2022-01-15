open Prop.Formula_prop
open Prop.Formula_tooling
open Prop.Theorem_prop
open Verif

let find_index f lf =
  let rec find_aux i f l=
    match l with
    | [] -> None
    | f1::_ when f=f1 -> Some i
    | _::l1 -> find_aux (i+1) f l1
  in 
  find_aux 1 f lf

(*instance of axiom*)
let is_instance_of_axiom_aux axioms f =
  let find_index_instance f list_axioms =
    let rec find_aux index l =
      match l with
        [] -> None
      | ax :: list_axioms' ->
        try Some (index,instance f ax.conclusion_prop )
        with Failed_Unification _ -> find_aux (index+1) list_axioms'
    in
    find_aux 1 list_axioms
  in
  match find_index_instance f axioms
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
        Logs.info (fun m -> m "%a" ~header:"Ax" pp i);
        Some(Ax(i,subst'))
      with
      | Not_found -> None
    end
  | None -> None

(*known theorem*)
let is_known_theorem_aux theorems f =
  let rec find_aux i f l=
    match l with
    | [] -> None
    | f1::_ when f=f1.conclusion_prop -> Some(Known i)
    | _::l1 -> find_aux (i+1) f l1
  in find_aux 1 f theorems

(*hypotesis*)
let is_hypothesis hypotheses f =
  match find_index f hypotheses
  with
  | None -> None
  | Some i -> Some (Hyp i)

(*cut*)
let is_cut_aux demo f =
  let find_cut f1 l =
    let rec search_impl i  = function
      | PImpl(g,h) :: l1  when f1=h -> let left =  find_index g l in
        begin match left with 
          | None -> search_impl (i+1) l1
          | Some lind -> lind , i
        end
      | _ :: l1 -> search_impl (i+1) l1
      | [] -> raise Not_found
    in
    search_impl 1 l
  in
  try
    let (li, ri) = find_cut f demo
    in 
        let pp ppf (i,j) =
          Fmt.pf ppf "%a%a" Fmt.(styled `Green (styled `Bold string)) "Cut" Fmt.(parens (pair ~sep:Fmt.comma int int)) (i,j);
        in
        Logs.info (fun m -> m "%a" pp (li,ri));
    Some(Cut(li,ri))
  with
  | Not_found -> None

let compile_demonstration ?(axioms=[]) ?(theorems=[]) ?(hypotheses=[]) ~demo () =
  let rec compile_demo_aux ~demo ~proof ~proved =
    match demo with
    | [] ->List.hd proved, proof
    | f :: demo_tail ->
      let  proof_term = List.find_map (fun func -> func (expand_all_notations f)) [is_hypothesis hypotheses; is_instance_of_axiom_aux axioms; is_known_theorem_aux theorems; is_cut_aux (List.rev proved) ]
      in
      match proof_term with
      | Some step -> 
        Logs.debug(fun m -> pp_formula Fmt.stdout f;m "proof_term");
        compile_demo_aux ~demo:demo_tail ~proved:(f::proved)  ~proof:(step :: proof)
      | None -> 
        Logs.debug (fun m -> pp_formula Fmt.stdout f;m "Invalid_demonstration");
        raise (Prop.Verif.Invalid_demonstration (f, List.rev (f::proved)))
  in
  let theorem, demonstration = compile_demo_aux ~demo:demo ~proved:[] ~proof:[]
  in
  {
    theorem ;
    demonstration=List.rev demonstration;
  }
