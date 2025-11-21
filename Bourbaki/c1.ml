type lettre = 
        | Lettre of char (**TODO private in .mli**)
        | Prime of lettre

module Ordered_lettre =
struct
        type t = lettre
        let rec compare l l' =
                match (l,l') with 
                | Lettre l, Lettre l' ->  Char.compare l l'
                | Lettre _, Prime _ -> -1
                | Prime _, Lettre _ -> 1
                | Prime l, Prime l' -> compare l l'
end        
module LettreSet = Set.Make(Ordered_lettre)

let is_alpha = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false

let char_to_lettre : char -> lettre = function c -> assert (is_alpha c) ; Lettre c
let fresh_letter = 
        let c = ref (Lettre '_') 
        in
        function () -> 
                let l = !c
                in 
                c := Prime !c;
                l

type signe_logique  = 
        | Square
        | Tau
        | Ou
        | Non
type signe_specifique = Signe_specifique of string * int

type signe = 
        | Signe_logique of signe_logique
        | Signe_lettre of lettre
        | Signe_specifique of signe_specifique

type assemblage = 
        { assemblage : signe array ; liens :  (int * int) list}
        
let collecte_lettres set = 
Array.fold_left (function s -> function | (Signe_lettre (Lettre l as lettre)) -> LettreSet.add lettre s | _ -> s ) set
     
let naked_assemblage text = {assemblage = [|text|]; liens=[]}
let a = naked_assemblage (Signe_lettre (char_to_lettre 'A'))
let b = naked_assemblage (Signe_lettre (char_to_lettre 'B'))

let impl: assemblage = {assemblage =[| Signe_logique Ou; Signe_logique Non |] ; liens = [] }

let concat a b = 
        let lift = Array.length b.assemblage
        in
        { 
                assemblage = Array.concat [a.assemblage ; b.assemblage]; 
                liens =(List.map (function (i,j) -> (i+lift, j+lift)) a.liens) @ b.liens 
}

let (=>) = fun a b -> concat (concat impl a) b

type 'th relation = Relation of assemblage * 'th  (*constraint 'th = #theorie, but mutually recursive type and class type are forbidden*)
type 'th terme = Terme of assemblage * 'th  (*constraint 'th = #theorie, but mutually recursive type and class type are forbidden*)
type 'th bien_forme = (*constraint 'th = #theorie, but mutually recursive type and class type are forbidden*)
        | T of 'th terme 
        | R of 'th relation
type 'th axiome = Axiome of { nom : string ; axiome : 'th relation }
type 'th axiome_implicite = Axiome_implicite of {nom : string ; regle : ('th bien_forme list) -> 'th relation} (*constraint 'th = #theorie, but mutually recursive type and class type are forbidden*)
type 'th demonstration = Demonstration of ('th relation * 'th relation list) (*constraint 'th = #theorie, but mutually recursive type and class type are forbidden*)
class ['th] theorie signes (axiomes_explicites : 'th axiome list) (axiomes_implicites : 'th axiome_implicite list)=
object(self : 'th)
  method axiomes_explicites = axiomes_explicites
  method axiomes_implicites = axiomes_implicites
  method constantes = 
          let set = LettreSet.empty in
          List.fold_left collecte_lettres set (List.map (function Axiome { axiome=Relation(assemblage,_); _ } -> assemblage.assemblage) axiomes_explicites)
  method verifie_theoreme  = function 
                | Demonstration(r, (Relation(a, t))::l) when t = self  -> List.mem a (List.map (function Axiome { axiome=Relation(assemblage,_); _ } -> assemblage) axiomes_explicites)
                | _ -> false
end

                   

class logique  = 
object(self : 'logique)
        inherit ['logique] theorie [||] [] []
        val signes : signe array = [||]
        method  s1 (a : 'logique relation) ( b : 'logique relation) = 
                match a,b with
                | Relation(a,t), Relation(b,u) when t=u && t= self-> 
                        (Relation( (a => (b => a)), t) : 'logique relation)
                | _ -> failwith "s1 invalid use"
end

class egalitaire = 
object(self :'egalitaire) 
        inherit logique 
        method s2 (a: 'egalitaire relation) = a
end

let l = new logique
let s1 =
l#s1 (Relation(a,l))(Relation(b,l))

