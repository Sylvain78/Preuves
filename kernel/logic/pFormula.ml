  type formula =
    | PVar of int
    | PNeg of formula
    | PAnd of formula * formula
    | POr of formula * formula
    | PImpl of formula * formula
