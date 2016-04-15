open Ocamlbuild_plugin;;
dispatch begin function
  | After_rules ->
    rule "dypgen"
      ~tags:["dypgen"]
      ~prods:["%.ml";]
      ~deps:["%.dyp"]
      begin fun env _ ->
        let dyp = env "%.dyp" in
        Cmd(S[A"dypgen"; A"--no-mli"; Px dyp])
      end;
end
