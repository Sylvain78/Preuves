module type SYMB =
	sig
		type t
		val to_string : t -> string
                val of_string : string -> t
	end

module type SIGNATURE =
	sig 
		type symbol 
		val to_string : symbol -> string
                val of_string : string -> symbol
                val is_symbol : symbol -> bool
		
		(* References on lists of symbols *)
                val constants : symbol list ref
		val operations : (symbol * int) list ref
		val binary_operations : symbol list ref
		val relations  : (symbol * int) list ref
		val binary_relations  : symbol list ref
		
                (* Mandatory to temporarily create the schematic variables *)
                val create_meta_symbol : symbol  -> symbol
                val is_meta_symbol : symbol -> bool

		(** Returns Some(arity) or None if undefined operation *)
		val operation_arity : symbol -> int option
		val relation_arity : symbol -> int option

		(** Tests based on arity *)
		val is_operation : symbol -> bool
		val is_relation : symbol -> bool
	end

module AbstractSignature (Symb: SYMB) : (SIGNATURE) = 
	struct
		type symbol = Symbol of Symb.t | MetaSymbol of Symb.t 
                let of_string s = Symbol (Symb.of_string s)
                let to_string = function 
                  | Symbol s -> Symb.to_string s 
                  | MetaSymbol s -> "\\mathbb{"^(Symb.to_string s)^"}"
		let constants = ref ([] : symbol list)
		let operations = ref  ([] : (symbol * int) list)
		let binary_operations = ref ([] : symbol list)
		let relations = ref ([] : (symbol * int) list)
		let binary_relations = ref ([] : symbol list)
	
                let create_meta_symbol  = function Symbol s | MetaSymbol s ->  MetaSymbol s
                let is_meta_symbol = function 
                  | MetaSymbol _ -> true 
                  | Symbol _ -> false
		(*TODO verify all the lists*)
		let is_symbol s = List.mem s !constants
		
		let arity s liste_bin liste =
			if List.mem s !liste_bin
			then Some 2
			else try Some (snd (List.find (fun (op,_) -> op = s) !liste))
					 with Not_found -> None 
		
		let operation_arity s = arity s binary_operations operations
		let relation_arity s = arity s binary_relations  relations
		
		let is_relation s =
			match relation_arity s 
			with
				| Some _ -> true
				| None -> false  
		
		let is_operation s =
			match operation_arity s 
			with
				| Some _ -> true
				| None -> false  
						
	end 

module SymbChar = struct type t = Char.t let to_string = String.make 1 let of_string c = c end	
module SymbString = struct type t = string let to_string s =s let of_string s = s end	
module SignatureMinimal = AbstractSignature(SymbString)

module Ens = 
struct 
        include SignatureMinimal 
        let is_in = of_string "\\in"
        let _ = binary_relations := [is_in] 
end
	
