open Signature

module type TERM = functor (Sig:SIGNATURE) -> 
sig
  type var =
    | Var of int
    | Metavar of string
  val compare_var : var -> var -> int
  module SetVar : (Set.S with type elt = var) 

  type term =
    | V of var
    | Constant of Sig.symbol
    | Operation of Sig.symbol * term list
  val printers_constants :  (Sig.symbol, Format.formatter -> unit) Hashtbl.t
  val printers_operations : (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
  val printers_relations :  (Sig.symbol, Format.formatter -> term -> unit) Hashtbl.t
  val variables_term : term -> SetVar.t
  type substitution = term -> term			
  val simultaneous_substitution_term : var list -> term list -> term -> term
  val print_term : Format.formatter -> term -> unit
end

module Term = (functor (Sig:SIGNATURE) -> 
  struct
    type var =
      | Var of int
      | Metavar of string (* TODO Verify if Metavar are still useful *)

    type term =
      | V of var
      | Constant of Sig.symbol
      | Operation of Sig.symbol * term list

    let printers_constants = Hashtbl.create 3;;
    let printers_operations = Hashtbl.create 3;;
    let printers_relations = Hashtbl.create 3;;
    (**Comparaison de variables, les variables précèdent les métavariables **)
    let compare_var v1 v2 =
      match v1,v2 with
      | Var i1, Var i2 -> (i2-i1)
      | Metavar v1, Metavar v2 -> String.compare v1 v2
      | Metavar _, Var _ -> 1
      | Var _, Metavar _ -> -1


    (** Ensemble de variables d'un term **)
    module SetVar = Set.Make (struct type t = var let compare = compare_var end)


    (** Ensemble des variables d'un term **)
    let rec variables_term = function
      | V(Var _ as t) | V(Metavar _ as t) -> SetVar.singleton t
      | Constant _ -> SetVar.empty
      | Operation(_, lt) -> let liste_vars = List.map (variables_term) lt
        in
        List.fold_left SetVar.union SetVar.empty liste_vars


    (** Remplace la liste des variable lx par la liste des terms lt **)		
    let rec simultaneous_substitution_term lx lt = function
      | Constant _ as c -> c
      | V x' as v -> 
        (try List.assoc x' (List.combine lx lt)
         with | Not_found -> v 
        )
      | Operation(s,lt') -> 
        let lt'' = List.map (simultaneous_substitution_term lx lt) lt'
        in 
        Operation(s,lt'')  

    (** Algorithme de Robinson **)
    type substitution = term -> term			

    let unifier_term, unifier_liste_term =
      let rec unifier_aux : (term * term) list * substitution -> substitution  = function
        | [ ],mu -> mu (* mu est la substitution *)
        | ((V var1 as x,u1)::lt),mu ->
          if (x = u1) then 
            unifier_aux (lt,mu)
          else
          if SetVar.mem var1 (variables_term u1) then
            failwith "unification circulaire"
          else
            let mu1 = fun u ->  simultaneous_substitution_term [var1] [u1] u
            in 
            let l1,l2 = List.split lt
            in
            let l1',l2' = List.map mu1 l1, List.map mu1 l2
            in
            unifier_aux ((List.combine l1' l2'),(fun u -> mu1 (mu u)))
        | ((u1, (V x1 as x))::lt),mu -> unifier_aux (((x,u1)::lt),mu)
        | (Constant c1, Constant c2)::lt,mu -> if c1 = c2 then
            mu
          else 
            failwith "constants non unifiables"
        | ((Operation(o1,l1)),(Operation(o2, l2)))::lt,mu -> 
          if (o1 = o2) && (List.length l1 = List.length l2) then
            unifier_aux ((List.combine l1 l2)@lt,mu)
          else
            failwith "operations non unifiables"
        | _ -> failwith "terms non unifiables"
      in 
      (fun t u -> unifier_aux ([(t,u)],(fun x -> x))),
      (fun l   -> unifier_aux       (l,(fun x -> x)))







    (** Formateurs d'affichage **)
    let rec print_term ff = function
      | V(Var i) -> if 0 <= i && i < 10 then Format.fprintf ff "X_%u" i else Format.fprintf ff "X_{%u}" i
      | V(Metavar s) -> Format.fprintf ff "%s" s
      | Constant c -> (Hashtbl.find printers_constants c) ff
      | Operation(op, _) as term -> (Hashtbl.find printers_operations op) ff term
  end: TERM)

