module type SYMB =
	sig
		type t
		val to_string : t -> string
                val of_string : string -> t
	end

module type SIGNATURE =
	sig 
		type symbole 
		val to_string : symbole -> string
                val of_string : string -> symbole
                val is_symbole : symbole -> bool
		
		(* Références sur les listes de symboles *)
                val constantes : symbole list ref
		val operations : (symbole * int) list ref
		val operations_binaires : symbole list ref
		val relations  : (symbole * int) list ref
		val relations_binaires  : symbole list ref
		
                (* Nécessaire pour créer temporairement les variables
                 * schématiques *)
                val create_meta_symbole : symbole  -> symbole
                val is_meta_symbole : symbole -> bool

		(** Renvoie Some(arité) ou None si opération non définie*)
		val arite_operation : symbole -> int option
		val arite_relation : symbole -> int option

		(** Test basé sur l'arité *)
		val is_operation : symbole -> bool
		val is_relation : symbole -> bool
	end

module AbstractSignature (Symb: SYMB) : (SIGNATURE) = 
	struct
		type symbole = Symbole of Symb.t | MetaSymbole of Symb.t 
                let of_string s = Symbole (Symb.of_string s)
                let to_string = function 
                  | Symbole s -> Symb.to_string s 
                  | MetaSymbole s -> "\\mathbb{"^(Symb.to_string s)^"}"
		let constantes = ref ([] : symbole list)
		let operations = ref  ([] : (symbole * int) list)
		let operations_binaires = ref ([] : symbole list)
		let relations = ref ([] : (symbole * int) list)
		let relations_binaires = ref ([] : symbole list)
	
                let create_meta_symbole  = function Symbole s | MetaSymbole s ->  MetaSymbole s
                let is_meta_symbole = function 
                  | MetaSymbole _ -> true 
                  | Symbole _ -> false
		(*TODO verifier toutes les listes*)
		let is_symbole s = List.mem s !constantes
		
		let arite s liste_bin liste =
			if List.mem s !liste_bin
			then Some 2
			else try Some (snd (List.find (fun (op,_) -> op = s) !liste))
					 with Not_found -> None 
		
		let arite_operation s = arite s operations_binaires operations
		let arite_relation  s = arite s relations_binaires  relations
		
		let is_relation s =
			match arite_relation s 
			with
				| Some _ -> true
				| None -> false  
		
		let is_operation s =
			match arite_operation s 
			with
				| Some _ -> true
				| None -> false  
						
	end 

module SymbChar = struct type t = Char.t let to_string = String.make 1 let of_string c = c end	
module SymbString = struct type t = string let to_string s =s let of_string s = s end	
module SignatureMinimale = AbstractSignature(SymbString)

module Ens = 
struct 
        include SignatureMinimale 
        let is_in = of_string "\\in"
        let _ = constantes := [is_in] 
end
	
