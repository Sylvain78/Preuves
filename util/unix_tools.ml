(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*           Jerome Vouillon, projet Cristal, INRIA Rocquencourt          *)
(*           OCaml port by John Malecki and Xavier Leroy                  *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(****************** Tools for Unix *************************************)

open Unix

(*** Convert a socket name into a socket address. ***)
let convert_address address =
  try
    let n = String.index address ':' in
    let host = String.sub address 0 n
    and port = String.sub address (n + 1) (String.length address - n - 1)
    in
    (PF_INET,
     ADDR_INET
       ((try inet_addr_of_string host with Failure _ ->
          try (gethostbyname host).h_addr_list.(0) with Not_found ->
            prerr_endline ("Unknown host: " ^ host);
            failwith "Can't convert address"),
        (try int_of_string port with Failure _ ->
           prerr_endline "The port number should be an integer";
           failwith "Can't convert address")))
  with Not_found ->
  match Sys.os_type with
  | "Win32" -> failwith "Unix sockets not supported"
  | _ -> (PF_UNIX, ADDR_UNIX address)

(*** I/O channels ***)

type io_channel = {
  io_in : in_channel;
  io_out : out_channel;
  io_fd : Unix.file_descr
  }

let io_channel_of_descr fd = {
  io_in = Unix.in_channel_of_descr fd;
  io_out = Unix.out_channel_of_descr fd;
  io_fd = fd
  }

let close_io io_channel =
  close_out_noerr io_channel.io_out;
  close_in_noerr io_channel.io_in;
;;

let std_io = {
  io_in = Pervasives.stdin;
  io_out = Pervasives.stdout;
  io_fd = Unix.stdin
  }

