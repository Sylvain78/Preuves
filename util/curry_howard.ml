type lambda =
	| LK
	| LS
	| LI
	| LV of string
	| LApp of lambda * lambda
	| LAbs of lambda * lambda
;;


let rec print_lambda ff = function
	| LK -> Format.fprintf ff "K"
	| LI -> Format.fprintf ff "I"
	| LS -> Format.fprintf ff "S"
	| LV x -> Format.fprintf ff "%s" x
	| LApp(e1,e2) -> Format.fprintf ff "(";print_lambda ff e1; Format.fprintf ff " "; print_lambda ff e2;Format.fprintf ff ")";
	| LAbs(v, e) ->  Format.fprintf ff "l";print_lambda ff v; Format.fprintf ff "("; print_lambda ff e;Format.fprintf ff ")";
		  
module S = Set.Make(String)

let rec free_vars = function 
	| LV x -> S.add x S.empty
	| LAbs(LV y,e1) -> S.remove y (free_vars e1)
	| LApp (e1,e2)  -> S.union (free_vars e1) (free_vars e2)
	| LI | LK | LS -> S.empty
	

let rec conversion = function
	| LV s -> LV s
	| LI -> LI
	| LK -> LK
	| LS -> LS
	| LAbs(LV x,LV y) when x=y -> LI
	| LAbs(LV x, LAbs(LV y, e)) when (x!=y) & (S.mem x (free_vars e)) -> conversion(LAbs(LV x,conversion(LAbs(LV y,e))))
	| LAbs(LV x,e) when  (not (S.mem x (free_vars e))) -> LApp (LK,conversion e)
	| LApp (l1,l2) -> LApp (conversion l1, conversion l2)
	| LAbs(LV x, LApp(e1,e2)) -> LApp(LApp(LS, (conversion(LAbs(LV x,e1)))), conversion(LAbs(LV x, e2)))

let c6 = LAbs(LV "a->b", LAbs(LV "b->c", LAbs(LV "a", LApp (LV "b->c", LApp(LV "a->b",LV "a")))));;
let but = conversion c6;;



let s abc ab a= abc a (ab a) ;;
let k a b = a;;
let i a =a;;
((s (k (s ((s (k s)) ((s (k k)) i))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i))));;

let c = LAbs(LV "a", LAbs(LV "b", LAbs(LV "c", LAbs (LV "d", LV "b"))));;
let but = conversion c;;

let c7 = LAbs(LV "a->c", LAbs(LV "a",LAbs(LV "b", LApp(LV "a->c", LV "a"))));;
let but = conversion c7;;


type sk =
| V of string 
| K 
| S 
| App of sk*sk


let k a b = App(App(K,a), b)

let s a b c = App(App(App(S,a),b),c)
let i  = (s k k) 
let but a aentb = s(k(s i))k a aentb

