(*open Parser*)
module Terme = functor (Sig:Signature.SIGNATURE) -> 
struct
	include Base_terme.Terme(Sig)
	
	(*TODO let parse = Parser.start*)
end