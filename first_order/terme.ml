(*open Parser*)
module Term = functor (Sig:Signature.SIGNATURE) -> 
struct
	include Base_terme.Term(Sig)
	
	(*TODO let parse = Parser.start*)
end
