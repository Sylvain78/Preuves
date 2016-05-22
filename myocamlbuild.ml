open Ocamlbuild_plugin;;
dispatch begin function
  | After_rules ->
    rule "dypgen"
      ~prods:["%.ml";]
      ~deps:["%.dyp"]
      begin fun env _ ->
        let dyp = env "%.dyp" in
(*        Cmd(S[A"dypgen"; A"--no-mli"; Px dyp])
 *)
          Cmd(S[A"dypgen"; A"--ocamlc"; A "-I `ocamlfind query dyp`";Px dyp])
      end;
  | _ ->  ()
end
