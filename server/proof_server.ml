(**
 * Code inspired by the ocaml debugger socket managment
 **)
open UnixLabels

open Protocol
open Session
open Unix_tools

module type SESSION = module type of Session 

let socket_name = 
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
    " <socket>  Set socket name to <socket>";
    "-v",  Arg.Unit print_version_string, " Print version and exit";
    "-version",  Arg.Unit print_version_string, " Print version and exit";
    "-vnum",  Arg.Unit print_version_num, " Print version number and exit";
  ]

let session =
  {
     mode = Session.Prop ; 
     history = [] ;
     prop = (module Proof_prop : Session.P);
     first_order = (module Formula : Session.F);
  }

let save_session mode file= 
  let oc = open_out file
  in
  begin
    match mode with 
    | Session.Text ->
      List.iter (fun s -> Printf.fprintf oc "%s\n\n" s) (List.rev session.history);
    | Session.Binary -> 
      print_string "history:\n";
      List.iter (fun s -> print_string s  ) session.history;
      Marshal.to_channel oc session [Marshal.Closures]
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
      let (session_loaded : Session.session) =  (Marshal.from_channel ic) 
      in
      print_string "history read :\n";
      List.iter print_string session_loaded.history;
      Pervasives.flush Pervasives.stdout;
      session.mode <- session_loaded.mode;
      session.history <- session_loaded.history;
      session.prop <- session_loaded.prop;
      session.first_order <- session_loaded.first_order;

  end;
  close_in ic

and eval s channels =  
  let command = decode s
  in
  match command with 
  | Prop ->  
    session.mode<-Session.Prop;
    print_string s;Pervasives.flush Pervasives.stdout;
    Ok
  | First_order -> 
    session.mode<-Session.First_order;
    print_string s;Pervasives.flush Pervasives.stdout;
    Ok
  | Save (mode,file) -> 
    begin
      save_session mode file; 
      Answer ("Saved to file "^file)
    end
  | Load (mode,file) ->
    begin
      print_string "command : load\n";
      Pervasives.flush Pervasives.stdout;
      load_session mode file channels;
      Answer ("Loaded file "^file)
    end
  | Notation s ->
    if (!Session.mode = Session.Prop) (*Replace if on Session.mode by match.*)
    then
      let module M = (val session.prop : Session.P) 
      in 
      let n = print_string ("XXX\n"^s ^"\nXXX\n");M.notation_from_string s
      in
      Answer ("Notation"^n.Formula_prop.notation_prop_name)
    else
        Answer "Notation first_order : unimplemented"
  | Axiom { name ; formula } -> 
    if (!Session.mode = Session.Prop) 
    then
      begin
        let module M = (val session.prop : Session.P) 
        in 
        if (List.exists (fun {Axioms_prop.name_proposition_prop;Axioms_prop.proposition_prop} -> name=name_proposition_prop)  !M.axioms_prop) then
          Answer ("Axiom " ^ name ^ " already defined")  
        else 
          begin
            M.axioms_prop := {Axioms_prop.name_proposition_prop = name;Axioms_prop.proposition_prop=M.formula_from_string formula} :: !M.axioms_prop;
            Ok
          end
      end
    else Answer("Axiom for first order unimplemented")
  | Theorem {name; premisses;conclusion;demonstration} ->
    if session.mode = Session.Prop
    then
      begin
        print_string "WWW\n";Pervasives.flush Pervasives.stdout;
        let module P = (val session.prop : Session.P)
        in
        print_string "ZZZ\n";Pervasives.flush Pervasives.stdout;
        P.proof_verification ~hyp:(List.map P.formula_from_string premisses) (P.formula_from_string conclusion) ~proof:(List.map P.formula_from_string demonstration);
        print_string "TTT\n";Pervasives.flush Pervasives.stdout;
      end
    else if session.mode = Session.First_order
    then 
      failwith "TheoremFirst_order"
    else
      failwith "session mode not Prop neither First_order";
    Ok
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
  let test = ref 0
  in
  while true 
  do 
    print_endline ("boucle "^ (string_of_int !test));incr test;
    (* read *)
    let nb_read = print_endline "avant read";read channels.io_fd  buffer 0 1024
    in
    print_endline ("apres read (lu" ^ (BytesLabels.to_string buffer)^")");
    Buffer.add_subbytes command buffer 0 nb_read;
    print_endline ("nouvelle commande : "^ (Buffer.contents command)^"XXX");
    let s = ref ""
    in
    while 
      s := (Buffer.contents command);
      print_endline "deuxieme while";
      print_endline ("analyse de "^ !s ^ "XXX");
      let test = 
        try 
          index_end_of_command := (Str.search_forward r !s 0);true
        with Not_found -> false
      in
      print_endline @@ "test = "^ (string_of_bool test);
      test
    do
      let com = Str.string_before !s !index_end_of_command
      in
      session.history <- com :: session.history;
      print_string "new history : \n";
      List.iter print_string session.history;
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
        | Ok -> output_string channels.io_out "Ok" 
        | Answer s -> output_string channels.io_out s
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
  let socket_domain,socket_address = convert_address address  in
  file_name :=
    (match socket_address with
     | ADDR_UNIX file ->
       Some file
     | _ ->
       None);
  let sock_listen = socket socket_domain SOCK_STREAM 0 in
  (try
     setsockopt sock_listen SO_REUSEADDR true;
     bind sock_listen socket_address;
     listen sock_listen 3;
     while true do
       let (sock, _) = accept sock_listen
       in
       let pid = fork()
       in
       match pid with 
       | 0      -> (*child*)
         ()
       | _ -> (*father*) 
         let io_chan = io_channel_of_descr sock 
         in
         print_endline "lancement repl";
         repl io_chan  

     done
   with x -> (match !file_name with Some file -> unlink file | None -> ());close sock_listen; raise x)


let _ = main()
