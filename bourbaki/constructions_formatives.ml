open Signes_et_assemblages
open Théorie

let espèce = function 
  | [Lettre _] | Tau _ :: _ -> 1
  |  _ -> 2

type construction_formative = Construction_formative of théorie * assemblage list

module Set_Lettres = Set.Make(struct type t = lettre let compare = Stdlib.compare end : Set.OrderedType with type t = lettre)
let rec lettres = function 
  | Lettre l :: tl -> Set_Lettres.add l (lettres tl)
  | _ :: tl -> lettres tl
  | [] -> Set_Lettres.empty

let collecte_lettres (l: assemblage list) = List.fold_left Set_Lettres.union Set_Lettres.empty  (List.map (function (assemblage:assemblage) -> lettres assemblage) l)

let rec vérification_construction_formative th = function 
  | [Lettre l]  :: tl -> vérification_construction_formative th tl
  | (Non :: b) as a  :: tl -> espèce b = 2 && List.mem a tl && vérification_construction_formative th tl
  | (Ou :: reste) :: tl -> List.exists2 (fun b c -> espèce b = 2 && espèce c = 2 && concat_assemblage b c = reste) tl tl && vérification_construction_formative th tl
  | (Tau _ :: ba as a) :: tl -> List.exists (fun b -> espèce b = 2 &&
                                                      let lettres_tl = collecte_lettres tl 
                                                      in  
                                                      Set_Lettres.exists (function l ->  tau l b = a) lettres_tl) tl
  | (Specifique(s,n) :: reste) :: tl ->  
    (assert (n > 0);
     List.mem (s,n) th.signes_spécifiques &&
     let rec find_ass m l = 
       match m  with 
         1 -> List.exists (function ass -> espèce ass = 1 && List.fold_right (fun ass acc -> concat_assemblage ass acc) l  [] = reste) tl
       | m' -> List.exists (function ass -> find_ass (m'-1) (ass::l)) tl
     in find_ass n []
    )
  | _ -> false


type terme = Terme of assemblage * construction_formative
type relation = Relation of assemblage * construction_formative 

let vérif_terme (Terme(terme, Construction_formative(théorie,cf))) = espèce terme = 1 && vérification_construction_formative théorie cf
let vérif_relation (Relation(relation, Construction_formative(théorie,cf))) = espèce relation = 2 && vérification_construction_formative théorie cf

