open Signes_et_assemblages

type notation = ..
type notation += Assemblage of assemblage
type notation += Concat of assemblage * assemblage
type notation += Tau of lettre * assemblage
type notation += Subst of lettre list * notation list * notation
