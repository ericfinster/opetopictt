(*****************************************************************************)
(*                                                                           *)
(*                                     IO                                    *)
(*                                                                           *)
(*****************************************************************************)

open Fmt

(*****************************************************************************)
(*                                  Parsing                                  *)
(*****************************************************************************)

module I = Parser.MenhirInterpreter

exception Parse_error of ((int * int) option * string)

let get_parse_error env =
    match I.stack env with
    | lazy Nil -> "Invalid syntax"
    | lazy (Cons (I.Element (state, _, _, _), _)) ->
        try (Parser_messages.message (I.number state)) with
        | Not_found -> "Invalid syntax (no specific message for this error)"

let rec parse lexbuf (checkpoint : 'a I.checkpoint) =
  match checkpoint with
  | I.InputNeeded _env ->
    let token = Lexer.token lexbuf in
    let (startp,endp) = Sedlexing.lexing_positions lexbuf in
    let checkpoint = I.offer checkpoint (token, startp, endp) in
    parse lexbuf checkpoint
  | I.Shifting _
  | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parse lexbuf checkpoint
  | I.HandlingError _env ->
    let line, pos = Lexer.get_lexing_position lexbuf in
    let err = get_parse_error _env in
    raise (Parse_error (Some (line, pos), err))
  | I.Accepted v -> v
  | I.Rejected ->
    raise (Parse_error (None, "Invalid syntax (parser rejected the input)"))

let parse_file f =
  let fi = open_in f in
  let lexbuf = Sedlexing.Utf8.from_channel fi in
  try
    let chkpt = Parser.Incremental.prog (fst (Sedlexing.lexing_positions lexbuf)) in
    let (imprts,defs) = parse lexbuf chkpt in
    close_in fi;
    (imprts,defs)
  with
  | Parse_error (Some (line,pos), err) ->
    pr "Parse error: %s@,Line: %d, Pos: %d@," err line pos;
    close_in fi;
    exit (-1)
  | Parse_error (None, err) ->
    pr "Parse error: %s" err;
    close_in fi;
    exit (-1)
  | Lexer.Lexing_error (Some (line,pos), err) ->
    close_in fi;
    pr "Lexing error: %s@,Line: %d, Pos: %d@," err line pos;
    exit (-1)
  | Lexer.Lexing_error (None, err) ->
    close_in fi;
    pr "Lexing error: %s@," err;
    exit (-1)

let parse_cmd s =
  let lexbuf = Sedlexing.Utf8.from_string s in
  let chkpt = Parser.Incremental.cmd (fst (Sedlexing.lexing_positions lexbuf)) in
  parse lexbuf chkpt

let rec check_files ctx checked to_check =
  let open Typecheck in
  let open Syntax in
  match to_check with
  | [] -> ctx
  | f::fs ->
    let (imprts,defs) = parse_file f in
    let imports_to_check =
      List.filter_map
        (fun i -> let fnm = i ^ ".ott" in 
          if (List.mem fnm checked)
          then None
          else Some fnm) imprts in
    let ctx' = check_files ctx checked imports_to_check in 
    pr "-----------------@,";
    pr "Processing input file: %s@," f;
    (* let mname = Filename.basename (Filename.remove_extension f) in *)
    try begin match tcm_check_defns defs ctx' with
      | Ok ctx'' -> 
        pr "----------------@,Success!@,";
        check_files ctx'' (f::checked) fs
          
      | Error err ->
        pr "@,Typing error: @,@,%a@,@," pp_error err ; 
        empty_ctx
      
    end with
    | Internal_error msg -> 
        pr "@,An internal error has occured : @,@,%s@," msg ; 
        empty_ctx
