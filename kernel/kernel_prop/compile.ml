open Prop.Formula_prop
open Prop.Kernel_theorem_prop
open Verif

let compile_demonstration ~demo ~theory=
  let theorem = List.hd demo 
  in
  let demo_rev = List.rev demo 
  in
  let rec compile_demo_aux ~demo (*TODO DELETE axiomes en debut de liste, formuels complexes a la fin*)  
      ~proof ~proved  (*TODO DELETE axiomes en fin de liste, formules compleexes au debut *)
    = 
    let find_index_instance f list_axioms =
      let rec find_aux index l =
        match l with 
          [] -> None
        | ax :: list_axioms' ->
          try Some (index,instance f ax.kernel_conclusion_prop )
          with Failed_Unification _ -> find_aux (index+1) list_axioms' 
      in
      find_aux 1 list_axioms
    in
    (*TODO refactor the chaining*)
    match demo with 
    | [] -> proof 
    | f :: demo_tail -> 
      (*instance of axiom*)
      match 
        begin
          match find_index_instance f !Prop.Axioms_prop.axioms_prop
          with
          | Some (i,subst) -> 
            begin
              try 
                let subst' = List.rev_map (function (PVar i, f) -> (i,f) | _ -> raise Not_found) subst
                in
                Some(i,subst')
              with Not_found -> None
            end
          | None -> None
        end
      with
      | Some (i,subst) -> compile_demo_aux ~demo:demo_tail ~proved:(f::proved)  ~proof:(Ax(i,subst) :: proof)
      | None -> 
        (*known theorem*)
        begin
          let find_index f lf =
            let rec find_aux i f l= 
              match l with
              | [] -> None
              | f1::_ when f=f1 -> Some i
              | _::l1 -> find_aux (i+1) f l1
            in find_aux 1 f lf
          in
          match find_index f theory
          with 
          | Some i -> compile_demo_aux ~demo:demo_tail ~proved:(f::proved)  ~proof:(Known i :: proof)
          | None ->
            (*cut*)
            begin
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
                search_impl  0 l
              in
              try 
                let (li, ri) = find_cut f proved
                in 
               compile_demo_aux ~demo:demo_tail ~proved:(f::proved)  ~proof:(Cut(li, ri) :: proof) 
              with _ -> raise (Prop.Proof_prop.Invalid_demonstration (f,demo))
            end (*end cut*)
        end (* end known theorem*)
  in
  { 
    theorem = theorem ;
    demonstration = compile_demo_aux ~demo:demo_rev ~proved:[] ~proof:[];
  }
