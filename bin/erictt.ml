(*****************************************************************************)
(*                                                                           *)
(*                                Main module                                *)
(*                                                                           *)
(*****************************************************************************)

open Format

open Erictt.Io
open Erictt.Typecheck

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "catt [options] [file]"

let spec_list = []

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)

let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg  
  | `PastingError msg -> Fmt.pf ppf "Error while checking pasting context: %s" msg
  | `FullnessError msg -> Fmt.pf ppf "Fullness error: %s" msg 
  | `IcityMismatch (_, _) -> Fmt.pf ppf "Icity mismatch"
  | `BadCohQuot msg -> Fmt.pf ppf "%s" msg 
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
  | `InvalidCylinder msg -> Fmt.pf ppf "Invalid cylinder: %s" msg 
  | `InternalError -> Fmt.pf ppf "Internal Error"

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

