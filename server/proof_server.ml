(**
 * Code inspired by the ocaml debugger socket managment
 **)
open UnixLabels
open Prop
open Prop__Kernel_theorem_prop
open Prop__Kind_prop
open Protocol
open Protocol_commands
open Session
open Util__Unix_tools

module type SESSION = module type of Session

let socket_name = 
  ref None
let max_session =
  ref None
let file_name = ref (None : string option)

let usage = "usage: proof-server [options] "

let version = "α"

let print_version_num () =
  print_endline version;
  exit 0

let print_version_string () =
  print_string "proof-server, version ";
  print_endline version;
  exit 0

let specs =
  [
    "-socket", Arg.String (fun x -> socket_name := Some x),
    " <socket>  Set socket name to <socket> : filename, host:port, ip:port";
    "-max_session", Arg.Int (fun x -> max_session := Some x), " maximum number of sessions accepted by the server before shutdown";
    "-v",  Arg.Unit print_version_string, " Print version and exit";
    "-version",  Arg.Unit print_version_string, " Print version and exit";
    "-vnum",  Arg.Unit print_version_num, " Print version number and exit";
  ]

let session =
  {
    mode = Session.Prop ; 
    name = "Init";
    speed = Session.Paranoid;
    history = [] ;
    axioms = [];
    theorems = [];
  }

let save_session mode file= 
  let oc = open_out file
  in
  begin
    match mode with 
    | Session.Text ->
      List.iter (fun s -> Printf.fprintf oc "%s\n\n" s) (List.rev session.history);
    | Session.Binary -> 
      List.iter (fun s -> print_string s  ) session.history;
      (*TODO one day....
       * let (base,ext) = Filename.remove_extension file, Filename.extension file
       * in
       * print_endline ("Save parser to : "^"\""^base^"_parser"^ext^"\"");
       * Prop.Prop_parser.save_parser ("\""^base^"_parser"^ext^"\"");
      *)
      Marshal.to_channel oc 
        (session: Prop.Kernel_theorem_prop.kernel_theorem_prop Session.session) 
        []
  end;
  close_out oc

let rec load_session mode file channels = 
  let ic = open_in file
  in
  begin
    match mode with 
    | Session.Text -> 
      repl {io_in=ic ; io_out = channels.io_out ; io_fd = channels.io_fd} 
    | Session.Binary ->
      let (session_loaded : Prop.Kernel_theorem_prop.kernel_theorem_prop Session.session) =  (Marshal.from_channel ic) 
      in
      List.iter print_string session_loaded.history;
      session.mode <- session_loaded.mode;
      session.history <- session_loaded.history;
      (*session.parser <- session_loaded.parser;*)
      session.axioms <- session_loaded.axioms;
      session.theorems <- session_loaded.theorems;

  end;
  close_in ic

and eval s channels =  
  print_endline ("eval : " ^ s); 
  (*let module M = (val session.prop : Session.P) 
    in 
    print_endline ("number of axioms : "^ (string_of_int @@ List.length @@ !M.axioms_prop));
  *)
  try
    let command = decode s
    in
    match command with 
    | Quit -> raise Exit
    | Prop ->  
      session.mode<-Session.Prop;
      Ok
    | First_order -> 
      session.mode<-Session.First_order;
      Ok
    | Fast ->
      session.speed<- Session.Fast;
      Ok
    | History ->
      Answer (String.concat "\n" @@ List.rev @@ session.history)
    | Save (mode,file) -> 
      begin
        save_session mode file; 
        Answer ("Saved to file "^file)
      end
    | Load (mode,file) ->
      begin
        load_session mode file channels;
        Answer ("Loaded file "^file)
      end
    | Notation n ->
      begin
        match session.mode with
        | Prop ->
          let notation = 
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
            Buffer.add_string buf (String.concat " " (List.map (function Param s | String s -> s) n.syntax));
            Buffer.add_char buf '\n';
            Buffer.add_string buf "Semantics";
            Buffer.add_char buf '\n';
            Buffer.add_string buf (String.concat " " (List.map (function Param s | String s -> s) n.semantics));
            Buffer.add_char buf '\n';
            Buffer.add_string buf "End";
            print_newline();
            print_string("{"^(Buffer.contents buf)^"}");Stdlib.flush Stdlib.stdout;
            Prop.Prop_parser.notation_from_string (Buffer.contents buf) 
          in
          Answer ("Notation "^notation.Formula_prop.notation_prop_name)
        | First_order -> Answer "Notation first_order : unimplemented"
      end
    | Axiom { name ; formula } -> 
      if (session.mode = Session.Prop) 
      then
        begin
          if (List.exists (fun {kernel_name_theorem_prop; _} -> name=kernel_name_theorem_prop) session.axioms)
          then
            Answer ("Axiom " ^ name ^ " already defined")  
          else 
            begin
              session.axioms <- {kernel_kind_prop=Axiom;kernel_proof_prop=[];kernel_name_theorem_prop = name;kernel_conclusion_prop=Prop.Prop_parser.formula_from_string formula} :: session.axioms;
              Ok
            end
        end
      else Answer("Axiom for first order unimplemented")
    | Theorem {name; params=_; premisses; conclusion; demonstration; status=_} ->
      if session.mode = Session.Prop (*TODO remplacer par un match sur mode*)
      then
        begin
          let verif_function = Prop.Proof_prop.prop_proof_verif
          in
          let verif =  (verif_function ~hyp:(List.map Prop.Proof_prop.formula_from_string premisses) 
                          (Prop.Proof_prop.formula_from_string conclusion) 
                          ~proof:(List.map (fun s -> Prop.Proof_prop.formula_from_string s) demonstration)) 
          in
          (* TODO Add theorem to the list, with its status*)
          if verif then
            Answer ("Theorem " ^ name ^ " verified.")
          else
            Answer ("Theorem " ^ name ^ " not verified.")
        end
      else if session.mode = Session.First_order
      then 
        failwith "TheoremFirst_order"
      else
        failwith "session mode not Prop neither First_order"
    | Show theorem_name ->
      if (session.mode = Session.Prop)
      then
        Answer(
          List.filter  (fun th -> th.kernel_name_theorem_prop = theorem_name) (session.axioms @ session.theorems)
          |> List.map (fun {
              kernel_kind_prop;
              kernel_name_theorem_prop;
              kernel_conclusion_prop;
              _
            } -> (kind_to_string kernel_kind_prop) ^ " " ^
                 kernel_name_theorem_prop ^ 
                 ":" ^
                 (*TODO "(" ^ 
                   (String.concat ", " @@ 
                   List.map (function 
                      | `PMetaVar s -> s 
                      | `PVar i -> if i>0 && i<10 
                        then "X_"^ (string_of_int i) 
                        else "X_{"^ (string_of_int i) ^ "}")
                    parameters_prop)  ^ 
                   ") : " ^*) 
                 (Prop.Proof_prop.to_string_formula_prop kernel_conclusion_prop)
            )  
          |> String.concat "\n" 
        )
      else 
        failwith "session mode not Prop "
  with 
  | Failure s -> Answer s

and repl channels =
  let command = Buffer.create 1024
  in
  (* 
   * read 
 * eval 
 * print 
 * loop
 *)
  let command_pattern = "\n\n"
  in
  let r = Str.regexp command_pattern
  in  
  let buffer = BytesLabels.make 1024 '\000'
  in
  let index_end_of_command = ref 0
  in
  while true 
  do 
    (* read *)
    let nb_read = read channels.io_fd  ~buf:buffer ~pos:0 ~len:1024
    in
    if nb_read=0 then raise End_of_file;
    Buffer.add_subbytes command buffer 0 nb_read;
    let s = ref ""
    in
    while 
      s := (Buffer.contents command);
      let test = 
        try 
          index_end_of_command := (Str.search_forward r !s 0);true
        with Not_found -> false
      in
      test
    do
      let com = Str.string_before !s !index_end_of_command
      in
      session.history <- com :: session.history;
      print_string  @@ String.concat "\n" @@ List.rev @@  session.history;
      let command_next = Str.string_after !s (!index_end_of_command + (String.length command_pattern))
      in
      Buffer.clear command;
      Buffer.add_string command command_next;
      (* eval *)
      (*channels needed to cause repl in case of executing a text file (load text)*)
      let answer = eval com channels

      in 
      (* print *)
      begin
        match answer with
        | Ok -> output_string channels.io_out "Ok.\n"
        | Answer s -> output_string channels.io_out (s^"\n")
      end;
      flush channels.io_out
      (* loop *)
    done
  done

let main () = 
  Arg.parse specs ignore usage;
  let address = match !socket_name with 
      Some x -> x
    | None -> 
      match Sys.os_type with
        "Win32" ->
        (Unix.string_of_inet_addr Unix.inet_addr_loopback)^ ":"^ (string_of_int (10000 + ((Unix.getpid ()) mod 10000)))
      | _ -> Filename.concat (Filename.get_temp_dir_name ())
               ("student_socket" ^ (string_of_int (Unix.getpid ())))
  in
  let socket_domain,socket_address = convert_address address in
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
     setsockopt sock_listen SO_REUSEADDR true;
     bind sock_listen ~addr:socket_address;

     if socket_domain = PF_INET then 
       begin
         match getsockname sock_listen
         with 
         | ADDR_INET(_,port) -> print_int port;print_newline()
         | _ -> ()
       end;

     listen sock_listen ~max:3;
     while (match !max_session 
            with 
            | None -> true 
            | Some n -> Format.printf  "max_sessions = %d\n" n; flush Stdlib.stdout;n > 0)
     do
       let (sock, _) = accept sock_listen
       in
       begin
         match !max_session
         with 
         | Some n -> max_session:= Some (n-1) 
         | None -> ()
       end; 

       let pid = fork()
       in
       match pid with 
       | 0      -> (*child*)
         let io_chan = io_channel_of_descr sock 
         in
         begin 
           try 
             repl io_chan  
           with 
           | End_of_file | Exit -> 
             begin 
               close io_chan.io_fd;
               exit 0 (*child quit the loop*)
             end
         end
       | _ -> (*father*) 
         ()
     done;
     close_sock_listen();
   with x -> Printexc.print_backtrace Stdlib.stdout ; close_sock_listen(); raise x)


let _ = main()
