type kind = Axiom | Theorem | Assumed
let kind_to_string = function
    | Axiom -> "Axiom"
    | Theorem -> "Theorem"
    | Assumed -> "Assumed"
