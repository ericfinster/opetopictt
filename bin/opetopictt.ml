(*****************************************************************************)
(*                                                                           *)
(*                                Main module                                *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Opetopictt.Io
open Opetopictt.Typecheck

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "catt [options] [file]"

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
  let defs = parse_all files in
  match check_defs empty_ctx defs with
  | Ok _ -> 
    printf "----------------@,Success!";
    print_newline ();
    print_newline ()
  | Error err -> Fmt.pr "@,Typing error: @,@,%a@,@," pp_error err

