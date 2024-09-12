(**
 * Code inspired by the ocaml debugger socket managment
 * Logging reporter from https://github.com/dinosaure/docteur/blob/main/bin/verify.ml
 **)
open UnixLabels
open Protocol
open Session
open Utilities.Unix_tools

module type SESSION = module type of Session

let buffer_size = 4096
let socket_name =
  ref None
let nb_session =
  ref 0
let file_name = ref (None : string option)
let version = "α"
let print_version_string () =
  print_string "proof-server, version ";
  print_endline version
let start_time = Unix.gettimeofday()
(*
let stamp_tag : float  Logs.Tag.def =
        Logs.Tag.def "stamp" ~doc:"Relative monotonic time stamp" (fun ff -> Format.fprintf ff "%f")
let stamp  = Logs.Tag.(empty |> add stamp_tag (Sys.time ()))
*)
let pad n x =
  if String.length x > n then x else x ^ String.make (n - String.length x) ' '
let pp_header ppf (level, header) =
  let level_style =
    match level with
    | Logs.App -> Logs_fmt.app_style
    | Logs.Debug -> Logs_fmt.debug_style
    | Logs.Warning -> Logs_fmt.warn_style
    | Logs.Error -> Logs_fmt.err_style
    | Logs.Info -> Logs_fmt.info_style
  in
  let level = Logs.level_to_string (Some level)
  in
  Fmt.pf ppf "[%a][%a]"
    (Fmt.styled level_style Fmt.string) level
    (Fmt.option Fmt.string) ((*Option.map (pad 10)*) header)
let reporter ppf =
  let report src level ~over k msgf =
    let k _ =
      over () ;
      k ()
    in
    let with_src_and_stamp h _ k fmt =
      Fmt.kpf k ppf
        ("%s %a %a: @[" ^^ fmt ^^ "@]@.")
        (pad 8
           (Format.fprintf Stdlib.Format.str_formatter  "%f" (Unix.gettimeofday() -. start_time);Stdlib.Format.flush_str_formatter())

           (*
        (if (dt <1_000.)
        then Fmt.str "%#4.0fµs" dt
                else if (dt/.1_000. <1_000.)
        then Fmt.str "%#4.0fms" (dt/.1_000.)
        else Fmt.str "%#4.0fs" (dt/.1_000_000.))
        *)
        )
        pp_header (level, h)
        Fmt.(styled `Magenta string)
        (pad 10 @@ Logs.Src.name src)
    in
    msgf @@ fun ?header ?tags fmt ->
    match header with
    | None -> with_src_and_stamp (Some(string_of_int (Unix.getpid()) |> String.cat @@ string_of_int (Thread.id (Thread.self())))) tags k fmt
    | Some _ -> with_src_and_stamp header tags k fmt
  in
  { Logs.report = report }

let setup_logs style_renderer level =
  Fmt_tty.setup_std_outputs ?style_renderer () ;
  Logs.set_level level ;
  Logs.set_reporter (reporter Fmt.stderr) ;
  let quiet =
    match level
    with
    | Some _ -> false
    | None -> true
  in
  quiet

let setup_logs =
  Cmdliner.Term.(const setup_logs $ Fmt_cli.style_renderer () $ Logs_cli.level ())


let session =
  {
    mode = { verbose_level = 1; order = Session.Prop; expand_notations = Expand_Notations; expand_calls = Expand_Calls; evaluation = Interpreted };
    name = "Init";
    history = [];
    theory = (module Kernel_prop_interp.Theory.Prop : Kernel.Logic.LOGIC);
    user = "";
  }

let save_session mode file=
  let oc = open_out file
  in
  begin
    match mode with
    | Modes.Text -> Format.pp_print_list ~pp_sep:(fun out () -> Format.pp_print_newline out ())
                      (fun ff -> Format.fprintf ff "%s")
                      (Format.formatter_of_out_channel oc)
                      (List.map (function c -> Protocol_commands.encode_command c |> Bytes.to_string) session.history)
    | Modes.Binary ->
      (*TODO one day....
       * let (base,ext) = Filename.remove_extension file, Filename.extension file
       *

        in
       * print_endline ("Save parser to : "^"\""^base^"_parser"^ext^"\"");
       * Kernel_prop_interp.Kernel_prop_interp_parser.save_parser ("\""^base^"_parser"^ext^"\"");
      *)
      Marshal.to_channel oc
        (session : Session.session)
        [Closures]
  end;
  close_out oc

let send_answer oc answer =
  (*      let buf = Stdio.In_channel.input_all in_channel in
          let reader = Ocaml_protoc_plugin.Reader.create buf in
          match Oprotom.from_proto reader with
  *)
  (* Create a Protobuf encoder and encode value *)

  (*  let encoder = Ocaml_protoc_plugin.Writer.create ()
      in
  *)
  let message = Protocol.encode_answer answer
  in
  (* Output size *)
  let size = Bytes.length message
  in
  output_binary_int oc size;
  flush oc;
  (* Output the protobuf message to a file *)
  Logs.info (fun m -> m "send response = %s" (Bytes.to_string message));
  Stdlib.(flush stdout);
  output_bytes oc (message);
  flush oc

let session_level = ref 0
let rec load_session mode file out_channel =
  incr session_level;
  let ic =
    open_in file
  in
  begin
    match mode with
    | Modes.Text ->
      begin
        try
          repl ic out_channel
        with
        | _ -> ()
      end
    | Modes.Binary ->
      let (session_loaded : Session.session) = (Marshal.from_channel ic)
      in
      session.mode <- session_loaded.mode;
      (*TODO tree of history by session ?*)
      session.history <- session_loaded.history;
      session.theory <- session_loaded.theory;
      (*session.parser <- session_loaded.parser;*)
  end;
  close_in ic
and eval command  out_channel =
  Logs.debug (fun m -> m "eval" );
  let log_number label lf =
    Logs.debug (fun m-> m "number of %s : %d" label (List.length lf))
  in
  let module Th = (val session.theory)
  in
  log_number "theorems" (Th.Theorems.get_theorems());
  try
    match (command : Protocol_commands.command) with
    | Comment com ->
      Logs.info (fun m -> m "comment :%s" com);
      Protocol.Ok(command)
    | Quit -> raise Exit
    | Verbose level ->
      session.mode.verbose_level <- level;
      Protocol.Ok(command)
    | Prop ->
      Logs.info(fun m -> m "Kernel_prop_interp");
      session.mode.order<-Session.Prop;
      Protocol.Ok (command)
    | First_Order ->
      session.mode.order<-Session.First_Order;
      Protocol.Ok (command)
    | Keep_Notations ->
      session.mode.expand_notations<- Session.Keep_Notations;
      Protocol.Ok (command)
    | Expand_Notations ->
      session.mode.expand_notations<- Session.Expand_Notations;
      Protocol.Ok (command)
    | Keep_Calls ->
      session.mode.expand_calls<- Kernel.Logic.Keep_Calls;
      Protocol.Ok (command)
    | Expand_Calls ->
      session.mode.expand_calls<- Kernel.Logic.Expand_Calls;
      Protocol.Ok (command)
    | Compiled ->
      session.mode.evaluation <- Session.Compiled;
      Protocol.Ok (command)
    | Interpreted ->
      session.mode.evaluation <- Session.Interpreted;
      Protocol.Ok (command)
    | History ->
      Protocol.Answer (Latex,Some LText,String.concat "\n" @@ List.rev @@ (List.map (function  com -> Bytes.to_string @@ Protocol_commands.encode_command com) session.history))
    | Save (file_mode, file) ->
      begin
        save_session file_mode file;
        Protocol.Answer (Text, None, ("Saved to file "^file))
      end
    | Load (file_mode, file) ->
      begin
        send_answer out_channel (Protocol.Answer (Text, None, "Load file "^file));
        try load_session file_mode file out_channel;
          decr session_level;
          Protocol.Answer (Text, None, "# Loaded file "^file)
        with
          Sys_error s -> Protocol.Error s
      end
    | Notation n ->
      begin
        match session.mode.order with
        | Prop ->
          let buf = Buffer.create 13
          in
          Buffer.add_string buf "Notation";
          Buffer.add_char buf '\n';
          Buffer.add_string buf n.name;
          Buffer.add_char buf '\n';
          Buffer.add_string buf "Param";
          Buffer.add_char buf '\n';
          Buffer.add_string buf (String.concat " " n.params);
          Buffer.add_char buf '\n';
          Buffer.add_string buf "Syntax";
          Buffer.add_char buf '\n';
          Buffer.add_string buf (String.concat " " (List.map (function Protocol_commands.(Param s | String s) -> s) n.syntax));
          Buffer.add_char buf '\n';
          Buffer.add_string buf "Semantics";
          Buffer.add_char buf '\n';
          Buffer.add_string buf (String.concat " " (List.map (function Protocol_commands.(Param s | String s) -> s) n.semantics));
          Buffer.add_char buf '\n';
          Buffer.add_string buf "End";
          print_newline();
          (* print_string("{"^(Buffer.contents buf)^"}");Stdlib.flush Stdlib.stdout; *)
          ignore @@ Kernel_prop_interp.Parser.notation_from_string (Buffer.contents buf);
          Protocol.Ok command
        | First_Order -> Protocol.Error "Notation first_order : unimplemented"
      end
    | Axiom { name ; formula } ->
      if (session.mode.order = Session.Prop)
      then
        begin
          let module Th = (val session.theory)
          in
          if (List.exists (fun (Theorem {name=name_th; _}:Th.theorem) -> name=name_th) !Th.axioms)
          then
            Protocol.Error ("Axiom " ^ name ^ " already defined")
          else
            begin
              Th.add_axiom (Theorem { kind=KAxiom;
                                      demonstration=Th.empty_demonstration;
                                      params = [];
                                      premisses = [];
                                      name = name;
                                      conclusion=Th.string_to_formula formula
                                    });
              Protocol.Ok command
            end
        end
      else Protocol.Error "Axiom for first order unimplemented"
    | Theorem {name; kind;params;premisses; conclusion; demonstration;} ->
      Logs.info (fun m -> m "Begin verification of Theorem %s" name);
      begin
        let module Th = (val session.theory)
        in
        Logs.info (fun m -> m "%s" ((function Prop -> "Prop" | First_Order -> "First_Order") session.mode.order));
        match session.mode.order
        with
        | Session.Prop ->
          begin
            Logs.info (fun m -> m "%s" ((function Compiled -> "Compiled" | Interpreted -> "Interpreted") session.mode.evaluation));
            let verif_function = Th.verif ~keep_calls:session.mode.expand_calls
            and conclusion = 
              Th.string_to_formula conclusion
            in
            let theorem_to_prove_compiled =
              {
                Kernel.Logic.kind = kind;
                Kernel.Logic.name = name;
                params = List.map Th.string_to_formula params;
                premisses = List.map Th.string_to_formula premisses;
                conclusion;
                demonstration=
                  (List.map
                     (function
                       | Protocol_commands.Step s ->
                         Th.(Single (string_to_formula s))
                       | Protocol_commands.Call (th, params) ->
                         let theorem = fst(Th.Theorems.find_by_name ~name:th)
                         in
                         Th.Call {theorem; params = List.map Th.string_to_formula params}
                     )
                     demonstration);
              }
            in
            let verif =
              try
                let theorem_proved  = verif_function theorem_to_prove_compiled
                in
                Logs.info (fun m -> m "End verification of Theorem %s" name);
                theorem_proved
              with
              | Th.Invalid_demonstration _ as ex ->
                let error_format = format_of_string "Invalid demonstration: %a\n\n"
                in
                Logs.err (fun m -> m ~header:("Invalid demonstration") error_format
                             (fun ff ex ->
                                match Th.print_invalid_demonstration ex
                                with
                                | Some s -> Format.fprintf ff "%s" s
                                | None -> ()) ex
                         );
                Error ("Invalid demonstration", ex)
            in
            match verif with
            | Ok (Theorem t) ->
              begin
                Th.Theorems.add_theorem (Theorem {
                  kind = Kernel.Logic.KTheorem;
                  name = t.name;
                  params = List.map Th.string_to_formula params;
                  premisses = List.map Th.string_to_formula premisses;
                  demonstration = t.demonstration;
                  conclusion = conclusion;
                });
                session.theory <- (module Th);
                Protocol.Ok command
              end
            | Error (msg, exc) ->
              Protocol.Error ("Theorem " ^ name ^ " not verified.\n" ^ msg ^ (match Th.print_invalid_demonstration exc with None -> "" | Some s -> s))
          end
        | First_Order -> failwith "unimplemented"
      end
    | Invalidate theorem_name ->
      let module Th = (val session.theory)
      in
      Th.Theorems.invalidate_theorem theorem_name;
      Protocol.Warning("Invalidated " ^ theorem_name)
    | Show theorem_name ->
      let module Th = (val session.theory)
      in
      if (session.mode.order = Session.Prop)
      then
        Protocol.Answer(Latex, Some LMath, (
            List.filter (function Th.Theorem th -> th.name = theorem_name) (!Th.axioms @ (Th.Theorems.get_theorems()))
            |> List.map (fun (Th.Theorem{
                kind;
                name;
                conclusion;
                _
              }:Th.theorem) -> (Kernel.Logic.kind_to_string kind) ^ " " ^
                               name ^
                               ":" ^
                               (*TODO "(" ^
                                 (String.concat ", " @@
                                 List.map (function
                                         | PMetaVar s -> s
                                 | PVar i -> if i>0 && i<10
                                 then "X_"^ (string_of_int i)
                                 else "X_{"^ (string_of_int i) ^ "}")
                                 parameters_prop) ^
                                 ") : " ^*)
                               (Th.formula_to_string conclusion)
              )
            |> String.concat "\n"))
      else
        failwith "session mode not Kernel_prop_interp.Prop"
    | List `Axioms ->
      let module Th = (val session.theory)
      in
      begin
        match session.mode.order
        with
        | Session.Prop ->
          Protocol.Answer (Latex, Some LMath,
                           (String.concat
                              "\\\\"
                              (List.map
                                 (function Th.Theorem t ->
                                    t.name ^
                                    " : " ^
                                    (Th.printer_formula Format.str_formatter t.conclusion;
                                     Format.flush_str_formatter ())
                                 )
                                 !Th.axioms
                              )
                           )
                          )




        | First_Order -> failwith "Unimplemented"
      end
    | List `Theorems ->
      let module Th = (val session.theory)
      in
      begin
        match session.mode.order
        with
        | Session.Prop ->
          Protocol.Answer(Latex, Some LMath,
                          ("\\begin{eqnarray*}" ^
                           (String.concat
                              "\\\\"
                              (List.map
                                 (function Th.Theorem t ->
                                    "\\textrm{" ^
                                    t.name ^
                                    "} & : & " ^
                                    (Th.printer_formula Format.str_formatter t.conclusion;
                                     Format.flush_str_formatter ())
                                 )
                                 (Th.Theorems.get_theorems())
                              )
                           ) ^
                           "\\end{eqnarray*}"
                          )
                         )
        | First_Order ->
          failwith "Unimplemented"
      end
    | List `Files ->
      let answer =
        let dir = Unix.opendir "."
        in
        let dir_list = ref []
        in
        begin try
            while true do
              let entry = readdir dir
              in
              if entry <> "." && entry <> ".." then
                dir_list := entry :: !dir_list
            done
          with End_of_file -> ()
        end;
        Protocol.Answer(Latex, Some LText, (String.concat ", " !dir_list))
      in answer
    | User user ->
      begin
        (
          try
            Unix.mkdir user 0o777
          with
          |  Unix.Unix_error(Unix.EEXIST, "mkdir", dir) when dir=user -> ()
        );
        Unix.chdir user;
        session.user <- user;
        Logs.debug (fun m -> m "dir : %s" (Unix.getcwd()));
        Protocol.Ok command
      end
  with
  | Failure s -> Protocol.Error s
and repl in_channel out_channel =
  Logs.info (fun m -> m "Launching repl");
        (*
         * init
         * read
         * eval
         * print
         * loop
         *)
  (*channels needed to be passed to  repl in case of executing a text file (load text)*)
  let lexbuf = Lexing.from_channel in_channel
  in
  while true
  do
    let lexbuf_contents lb =
      let open Lexing in
      let pos = lb.lex_curr_pos in
      let len = lb.lex_buffer_len - lb.lex_curr_pos in
      (Bytes.to_string (Bytes.sub lb.lex_buffer pos len))
    in
    Format.print_string "#<lexbuf:<";
    Format.print_string (lexbuf_contents lexbuf);
    Format.print_string ">>";
    Stdlib.(flush stdout);

    let command = decode lexbuf
    in
    Logs.debug (fun m -> m "command read\n");
    let answer = eval command out_channel
    in
    if (!session_level = 0)
    then
      (session.history <- command :: (List.map (function s -> Protocol_commands.Comment s) !Protocol_lexer.comments) @ session.history);
    (* eval *)
    (* print *)
    send_answer out_channel answer
    (* loop *)
    (*;flush out_channel*)
  done


let main _ (*quiet*) socket_val (max_session : int option)  version=
  if version
  then
    begin
      print_version_string ();
      exit 0;
    end;
  socket_name := Some socket_val;
  nb_session := (match max_session with
      | None -> -1
      | Some n -> n);
  let address = match !socket_name with
      Some x -> x
    | None ->
      match Sys.os_type with
        "Win32" ->
        (Unix.string_of_inet_addr Unix.inet_addr_loopback)^ ":"^ (string_of_int (1_0000 + ((Unix.getpid ()) mod 1_0000)))
      | _ -> Filename.concat (Filename.get_temp_dir_name ())
               ("student_socket" ^ (string_of_int (Unix.getpid ())))
  in
  let socket_domain,socket_address = convert_address address
  in
  file_name :=
    (match socket_address with
     | ADDR_UNIX file ->
       Some file
     | _ ->
       None);
  let sock_listen = socket ~cloexec:true ~domain:socket_domain ~kind:SOCK_STREAM ~protocol:0
  in
  let close_sock_listen () =
    match !file_name
    with
    | Some file -> unlink file
    | None -> close sock_listen
  in
  (try
     Logs.app (fun m -> m "Listening on %s" address);
     establish_server repl ~addr:socket_address
   (*     setsockopt sock_listen SO_REUSEADDR true;
          bind sock_listen ~addr:socket_address;
          if socket_domain = PF_INET
          then
                  begin
                          match getsockname sock_listen
          with
          | ADDR_INET(_,port) -> Logs.app (fun m -> m "port = %d" port)
          | _ -> ()
          end;
          listen sock_listen ~max:3;
          while (Printf.printf "nb session : %d\n" !nb_session;!nb_session <> 0)

          do
          let (sock, _) = accept sock_listen
          in
          Logs.info (fun m -> m "sock rcv timeout =%f" (Unix.getsockopt_float sock SO_RCVTIMEO));
          Logs.info (fun m -> m "sock snd timeout =%f" (Unix.getsockopt_float sock SO_SNDTIMEO));

          decr nb_session;
          let pid = fork()
          in
          match pid with
          | 0 -> (*child*)
                          let io_chan = io_channel_of_descr sock
          in
          begin
                  try
                          repl io_chan
          with
          | End_of_file | Exit ->
                          begin
                                  Logs.info (fun m -> m "repl exited");
          close io_chan.io_fd;
          exit 0 (*child quit the loop*)
          end
                      end
          | id -> (*father*)
                    Unix.close sock; ignore(Unix.waitpid [] id)
          done;
                        (close_sock_listen());Ok command ()
   *)
   with
   (*| Error error ->
           begin
                   close_sock_listen();
       Logs.err(fun m -> m "%s" ("Invalid demonstration: " ^ error))
     end
   *)| Stdlib.Exit ->
     begin
       close_sock_listen();
       Logs.info (fun m -> m "In memoriam Alexandre Grothendieck, 1928 ̶ 2013")
     end
  )

let () =
  let socket =
    let default = "localhost:5757"
    in
    let info =
      Cmdliner.Arg.info ["s"; "socket"]
        ~docv:"SOCKET"
        ~doc:"socket value : ip:port, hostname:port"
    in
    Cmdliner.Arg.value (Cmdliner.Arg.opt Cmdliner.Arg.string default info)
  and max_session =
    let info_max_session =
      Cmdliner.Arg.info ["m"; "max-session"]
        ~docv:"MAX SESSION"
        ~doc:"maximum number of sessions accepted by the server before shutdown"
    in
    Cmdliner.Arg.(value (opt (some int) None info_max_session))
  and version =
    let info =
      Cmdliner.Arg.info ["vnum"; "version"]
        ~docv:"VERSION"
        ~doc:"Print version and exit"
    in
    Cmdliner.Arg.value (Cmdliner.Arg.flag info)
  in
  let command =
    let doc ="Launch the proof server"
    in
    Cmdliner.Cmd.v (Cmdliner.Cmd.info "main" ~doc) (Cmdliner.Term.(const main $ setup_logs $ socket $ max_session $ version))
  in
  exit(Cmdliner.Cmd.eval ~catch:true command)
