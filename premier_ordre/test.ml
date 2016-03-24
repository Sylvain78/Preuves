open Formules
open Theorie
module Test_sig =	struct
	let constantes = []
	let operations = []
	let relations = ["\\in", 2]
end

module T = Theorie(Test_sig);;
open T;;
module F = Formules(Test_sig)
open F
let th =
	{
		axiomes = [];
		schemas = [];
		symboles_definis = (Hashtbl.create 0);
		operations_definies = (Hashtbl.create 0);
		relations_definies = (Hashtbl.create 0);
	};;
open Util
let test =
	let (c: T.terme) = Constante "0"
	in
	verification_preuve ~theorie: th ~hyp:[] ~proof:
		[c^= c] (c^= c);;
