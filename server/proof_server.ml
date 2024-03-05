(**
 * Code inspired by the ocaml debugger socket managment
 * Logging reporter from https://github.com/dinosaure/docteur/blob/main/bin/verify.ml
 **)
open UnixLabels
open Protocol
open Session
open Utilities.Unix_tools

module type SESSION = module type of Session

let buffer_size = 65536
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
    mode = { verbose_level = 1; order = Session.Prop; expand_notations = Keep_notations; expand_calls = Fast; evaluation = Interpreted };
    name = "Init";
    history = [] ;
    theory = (module Kernel_prop_interp.Theory.Prop : Kernel.Logic.LOGIC);
    user = "";
  }

let save_session mode file=
  let oc = open_out file
  in
  begin
    match mode with
    | Modes.Text ->
      List.iter (fun s -> Printf.fprintf oc "%s\n\n" s) (List.rev session.history);
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

let rec command_stack = Queue.create ()
and command_sem = Semaphore.Counting.make 0
and command_queue_mutex = Mutex.create()
and session_level = ref 0
and load_session mode file out_channel =
  incr session_level;
  let ic = open_in file
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
and eval s out_channel =
  Logs.debug (fun m -> m "eval %s" s);
  let log_number label lf =
    Logs.debug (fun m-> m "number of %s : %d" label (List.length lf))
  in
  let module Th = (val session.theory)
  in
  log_number "theorems" !Th.theorems;
  try
    let command = decode s
    in
    match (command : Protocol_commands.command) with
    | Quit -> raise Exit
    | Verbose level ->
      session.mode.verbose_level <- level;
      Protocol.Ok(command)
    | Prop ->
      Logs.info(fun m -> m "Kernel_prop_interp");
      session.mode.order<-Session.Prop;
      Protocol.Ok (command)
    | First_order ->
      session.mode.order<-Session.First_order;
      Protocol.Ok (command)
    | Keep_notations ->
      session.mode.expand_notations<- Session.Keep_notations;
      Protocol.Ok (command)
    | Expand_notations ->
      session.mode.expand_notations<- Session.Expand_notations;
      Protocol.Ok (command)
    | Compiled ->
      session.mode.evaluation <- Session.Compiled;
      Protocol.Ok (command)
    | Interpreted ->
      session.mode.evaluation <- Session.Interpreted;
      Protocol.Ok (command)
    | History ->
      Protocol.Answer (Latex,Some LText,String.concat "\n" @@ List.rev @@ session.history)
    | Save (file_mode, file) ->
      begin
        save_session file_mode file;
        Protocol.Answer (Text, None, ("Saved to file "^file))
      end
    | Load (file_mode, file) ->
      begin
        send_answer out_channel (Protocol.Answer (Text, None, "Load file "^file));
        load_session file_mode file out_channel;
        decr session_level;
        Protocol.Answer (Text, None, "# Loaded file "^file)
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
        | First_order -> Protocol.Error "Notation first_order : unimplemented"
      end
    | Protocol_commands.Axiom { name ; formula } ->
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
    | Theorem {name; kind;params;premisses; conclusion; demonstration; _} ->
      Logs.info (fun m -> m "Begin verification of Theorem %s" name);
      begin
        Logs.info (fun m -> m "%s" ((function Prop -> "Prop" | First_order -> "First_order") session.mode.order));
        match session.mode.order
        with
        | Session.Prop ->
          begin
            Logs.info (fun m -> m "%s" ((function Compiled -> "Compiled" | Interpreted -> "Interpreted") session.mode.evaluation));
            let verif_function = Th.verif ~speed:session.mode.expand_calls
            and conclusion = Th.string_to_formula conclusion
            in
            let theorem_to_prove_compiled =  {
              Kernel.Logic.kind = kind;
              Kernel.Logic.name = name;
              params = List.map Th.string_to_formula params;
              premisses = List.map Th.string_to_formula premisses;
              conclusion;
              demonstration= (List.map 
                                   (function 
                                     | Protocol_commands.Step s -> 
                                       Th.(Single (string_to_formula s))
                                     | Protocol_commands.Call (th, params) ->
                                       Th.Call {theorem=List.find (function Th.Theorem theorem -> theorem.name =  th) !Th.theorems; 
                                                params=List.map Th.string_to_formula params}
                                   ) 
                                   demonstration);
            }
            in
            let verif =
              try
                (
                  try
                    let theorem_proved  = verif_function theorem_to_prove_compiled
                    in
                    Logs.info (fun m -> m "End verification of Theorem %s" name);
                    theorem_proved 
                  with
                  | _ -> failwith "XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX"
                )
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
                Th.theorems := Th.Theorem {
                  kind = Kernel.Logic.KTheorem;
                  name = t.name;
                  params = List.map Th.string_to_formula params;
                  premisses = List.map Th.string_to_formula premisses;
                  demonstration = t.demonstration;
                  conclusion = conclusion;
                }
                  :: !Th.theorems;
                Protocol.Ok command
              end
            | Error (msg, exc) -> 
              Protocol.Error ("Theorem " ^ name ^ " not verified.\n" ^ msg ^ (match Th.print_invalid_demonstration exc with None -> "" | Some s -> s))
          end
        | First_order -> failwith "unimplemented"
      end
    | Show theorem_name ->
      if (session.mode.order = Session.Prop)
      then
        Protocol.Answer(Latex, Some LMath,(
            List.filter (function Th.Theorem th -> th.name = theorem_name) (!Th.axioms @ !Th.theorems)
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
      begin
        match session.mode.order
        with
        | Session.Prop ->
          Protocol.Answer (Latex, Some LMath,
                           (String.concat
                              "\n"
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




        | First_order -> failwith "Unimplemented"
      end
    | List `Theorems ->
      begin
        match session.mode.order
        with
        | Session.Prop -> Protocol.Answer(Latex, Some LMath,
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
                                                 !Th.theorems
                                              )
                                           ) ^
                                           "\\end{eqnarray*}"
                                          )
                                         )
        | First_order -> failwith "Unimplemented"
      end
    | List `Files ->
      let answer =
        let dir = Unix.opendir session.user
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
  let command = Buffer.create buffer_size
  in
  (* read in_channel and put one command in a stack*)
  let read_and_enqueue_command in_channel =
    Logs.info (fun m -> m "read_and_enqueue_commands\n");
    let must_read = ref true
    in
    while !must_read
    do
      let s1 =
        (try
           input_line in_channel
         with
         | End_of_file -> 
           begin 
             Logs.info (fun m -> m "end of file") ;
             raise Stdlib.Exit 
           end
         |  e -> Logs.err (fun m -> m " read error : %s" (Printexc.to_string e));raise e
        )
      in
      must_read := s1 <> String.empty;
      if (!must_read)
      then 
        begin
          Buffer.add_string command s1;
          Buffer.add_char command '\n'
        end
    done;
    if (Buffer.length command > 0) then 
      begin 
        Mutex.lock command_queue_mutex;
        Buffer.truncate command (max 0 ((Buffer.length command) - 1));
        Queue.add  (Buffer.contents command) command_stack;
        Mutex.unlock command_queue_mutex;
      end;
    Semaphore.Counting.release command_sem;
    Buffer.clear command
  and eval_commands command_stack = 
    (*pop stack *)
    (* read *)
    Semaphore.Counting.acquire command_sem;
    Mutex.lock command_queue_mutex;
    let com = 
      try
        Queue.take command_stack
      with Queue.Empty -> 
        begin
          Mutex.unlock command_queue_mutex;raise Stdlib.Exit
        end
    in
    Mutex.unlock command_queue_mutex;
    if (!session_level = 0) 
    then
      (session.history <- com :: session.history);
    (* eval *)
    (*channels needed to be passed to  repl in case of executing a text file (load text)*)
    let answer = eval com out_channel
    in
    (* print *)
    send_answer out_channel answer
    (* loop *)
    (*;flush out_channel*)
  in
  while true
  do
    read_and_enqueue_command in_channel;
    eval_commands command_stack
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
