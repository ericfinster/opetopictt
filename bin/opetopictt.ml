(*****************************************************************************)
(*                                                                           *)
(*                                Main module                                *)
(*                                                                           *)
(*****************************************************************************)

(* open Base
 * open Fmt *)

open Format
    
open Opetopictt.Io
open Opetopictt.Typecheck
       
(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "opetopictt [options] [file]"

let spec_list = []

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)
                            
let () = 
  let file_in = ref [] in
  set_margin 80;
  open_vbox 0; (* initialize the pretty printer *)
  Arg.parse spec_list (fun s -> file_in := s::!file_in) usage;
  let files = List.rev (!file_in) in
  let _ = check_files empty_ctx [] files in
  ()


(* let rec repl_loop _ =
 *   print_string "#> " ; 
 *   let str = read_line () in
 *   if (String.equal str "quit") then
 *     exit 0
 *   else
 *     let _ = Printf.printf "You said: %s\n" str in 
 *     repl_loop ()
 * 
 * let () = repl_loop () *)
