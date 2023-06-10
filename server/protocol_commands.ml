type notation_element = Param of string | String of string

type demonstration_step =
  | Step of string
  | Big_step of string * (string list)

type command =
  | Verbose of int
  | Prop
  | First_order
  | Keep_notations
  | Expand_notations
  | Compiled
  | Interpreted
  | Save of Modes.ascii_mode * string
  | Load of Modes.ascii_mode * string
  | Notation of { name:string ; params: string list ; syntax : notation_element list ; semantics : notation_element list }
  | Theorem of {name:string ; params: string list; premisses: string list; conclusion : string ; demonstration : demonstration_step list; status : Session.status}
  | Axiom of {name:string; formula:string} 
  | History
  | Show of string
  | List of [`Axioms | `Theorems | `Files]
  | User of string
  | Quit

let encode_command = 
  let encode_string s =
    let l = String.length s
    in
    let b =Bytes.create(4 + l)
    in
    BytesLabels.(set_int32_be b 0 (Int32.of_int l);blit_string ~src:s ~src_pos:0 ~dst:b ~dst_pos:4 ~len:l);b
  in
  let encode_notation_element = function
    | Param p -> Bytes.cat (encode_string "Param") (encode_string p)
    | String s -> Bytes.cat (encode_string "Param") (encode_string s)
  in
  function
  | Prop -> encode_string "Prop"
  | First_order -> encode_string "First_order"
  | Compiled -> encode_string "Compiled"
  | Interpreted -> encode_string "Interpreted"
  | Notation { name ; params; syntax; semantics }  -> 
    let b = Bytes.create 0
    in 
    Bytes.concat b
      ([ encode_string "Notation";
         encode_string name;
         encode_string "Params"] 
       @ List.map encode_string params
       @ [ encode_string "Syntax" ]
       @ List.map encode_notation_element syntax
       @ [ encode_string "Semantics" ]
       @ List.map encode_notation_element semantics
      )
  | Theorem { name ; conclusion (*params; premisses; conclusion ; demonstration ; status*) ; _ } ->
    let b = Bytes.create 0
    in 
    Bytes.concat b
      ([ encode_string "Theorem";
         encode_string name;
         encode_string ("\\("^conclusion^"\\)")]
      )
    | User user -> 
    let b = Bytes.create 0
    in 
      Bytes.concat b (List.map encode_string (["User"; user]))
    | _ -> failwith "unimplemented1"
