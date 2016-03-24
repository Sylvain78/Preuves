type buffer = string

type interpretations = formule list

type notation = {
        contraintes : string * ~propriete:string
        notation:string;
        valeur : formule;
        

}

let rec analyse : buffer -> proprietes_connues -> notation list -> interpretations


