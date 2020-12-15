open Prop.Formula_prop
open Prop.Kernel_theorem_prop
open Prop.Axioms_prop
open Kernel_prop__Kernel_prop_proof

let compile_demonstration ~demo ~theory=
  let theorem = List.hd demo 
  in
  let demo_rev = List.rev demo 
  and index = ref 1
  in
  let rec compile_demo_aux ~demo (*TODO DELETE axiomes en debut de liste, formuels complexes a la fin*)  
      ~proved  (*TODO DELETE axiomes en fin de liste, formules compleexes au debut *)
    = 
    match demo with 
    | [] -> []
    | f :: demo_tail -> 
      let find_index pred l =
        let rec find_aux i li = 
          match li with 
          | [] -> None
          | x :: ls -> 
            if pred x 
            then 
              Some i
            else find_aux (i+1) ls
        in
        find_aux 1 l
      in
      (*instance of axiom*)
      match 
        find_index (fun axiom -> instance f axiom.kernel_conclusion_prop) !Prop.Axioms_prop.axioms_prop
      with
      | Some i -> compile_demo_aux ~demo:demo_tail ~proved:(Ax i :: proved)
      | None -> 
        (*known theorem*)
        begin
          match find_index (fun theorem  -> f = theorem) theory
          with 
          | Some i -> Known i
          | None ->
            (*cut*)
            begin
              let rec find_cut f1 l =
                let rec search_impl i  = function
                  | PImpl(g,h) :: l1  when f1=h -> let left =  find_index (fun k -> k=g) l in
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
                Cut(li, ri)
              with _ -> raise Invalid_demonstration (f,demo)
            end (*end cut*)
        end (* end known theorem*)
  in
  { 
    theorem = theorem ;
    demonstration = compile_demo_aux ~demo:demo_rev ~proved:[];
  }
