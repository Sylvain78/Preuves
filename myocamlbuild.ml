open Ocamlbuild_plugin;;
dispatch begin function
  | After_rules ->
    rule "dypgen"
      ~prods:["%.ml";"%.mli"]
      ~deps:["%.dyp"]
      begin fun env _ ->
        let dyp = env "%.dyp" in
(*        Cmd(S[A"dypgen"; A"--no-mli"; Px dyp])
 *)
          Cmd(S[A"dypgen"; A"--ocamlc"; A"-I `ocamlfind query dyp` -I prop -I first_order"; Px dyp])
      end;
  | _ ->  ()
end
