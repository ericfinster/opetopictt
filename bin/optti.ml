(*****************************************************************************)
(*                                                                           *)
(*                             The Interpreter                               *)
(*                                                                           *)
(*****************************************************************************)

open Opetopictt.Io
open Opetopictt.Cmd
open Opetopictt.Eval        
open Opetopictt.Term
open Opetopictt.Expr
open Opetopictt.Value       
open Opetopictt.Lexer
open Opetopictt.Syntax
open Opetopictt.Typecheck
open Opetopictt.Suite       

(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "optti [options] [file]"

let current_context = ref empty_ctx 

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)

let run_tc tc_action =
  let gma = ! current_context in 
  match tc_action gma with
    | Ok res -> Some res
    | Error err -> Fmt.pr "@,@,%a@,@," pp_error err ; None

let rec repl_loop _ =
  Fmt.pr "@[#> @]@?" ; 
  try begin match parse_cmd (read_line () ^ ";") with

    | Nop -> repl_loop () 

    | Load fnm ->
      Format.open_vbox 0 ; 
      let gma' = check_files empty_ctx [] [fnm ^ ".ott"] in
      current_context := gma' ;
      repl_loop () 

    | Quit -> Format.print_flush () ; exit 0

    | Infer e ->
      begin match run_tc (tcm_infer e) with
        | Some (_, typv) ->
          let gma = ! current_context in 
          let typt = quote false gma.level typv in 
          let typ_expr = term_to_expr (names gma) typt in
          Fmt.pr "@[%a@]@," pp_expr typ_expr ;
          repl_loop ()
        | None -> repl_loop ()
      end

    | Normalize e ->
      begin match run_tc (tcm_infer e) with
        | Some (tm,_) ->
          (* log_msg "inferrence complete" ; *)
          let gma = ! current_context in 
          (* let ty_tm = quote true gma.level ty in *)
          (* let ty_ex = term_to_expr (names gma) ty_tm in *)
          (* log_val "ty_ex" ty_ex pp_expr ; *)
          let tmv = eval (top gma) (loc gma) tm in
          (* log_msg "back from eval" ; *)
          (* log_val "tmv" tmv (pp_value_lvl gma.level) ; *)
          let tm_nf = quote true gma.level tmv in
          (* log_msg "back from quote" ;  *)
          (* Fmt.pr "@[%a@]@," pp_term tm_nf ; *)
          let typ_expr = term_to_expr (names gma) tm_nf in
          Fmt.pr "@[%a@]@," pp_expr typ_expr ;
          repl_loop ()
        | None -> repl_loop ()           
      end

    | Assume tl ->
      begin match run_tc (tcm_in_tele tl (fun _ _ -> tcm_ctx)) with
        | Some gma' -> 
          current_context := gma' ; 
          Fmt.pr "Context ok@," ; 
          repl_loop ()
        | None -> repl_loop ()
      end

    | Let (id,None,tm) ->
      begin match run_tc (tcm_infer tm) with
        | Some (tm',ty) ->
          let gma = ! current_context in 
          let tmv = eval (top gma) (loc gma) tm' in
          let gma' = { gma with
                       bindings = gma.bindings |@>
                                  (id,BoundName (ty,tmv)) } in 
          current_context := gma' ; 
          repl_loop ()
        | None -> repl_loop ()           
      end

    | Let (id,Some ty,tm) ->
      let m =
        let* ty' = tcm_check ty TypV in
        let* tyv = tcm_eval ty' in 
        let* tm' = tcm_check tm tyv in
        tcm_ok (tyv,tm') in

      begin match run_tc m with
        | Some (tyv,tm') ->
          let gma = ! current_context in 
          let tmv = eval (top gma) (loc gma) tm' in
          let gma' = { gma with
                       bindings = gma.bindings
                                  |@> (id,BoundName (tyv,tmv)) }  in
          current_context := gma' ; 
          repl_loop ()
        | None -> repl_loop ()           
      end
  end with 
  | Internal_error msg -> 
    Fmt.pr "@,An internal error has occured : @,@,%s@," msg ;
    repl_loop () 

and parse_cmd s =
  try 
    let lexbuf = Sedlexing.Utf8.from_string s in
    let chkpt = Opetopictt.Parser.Incremental.cmd
        (fst (Sedlexing.lexing_positions lexbuf)) in
    parse lexbuf chkpt
  with 
  | Parse_error (Some (_,pos), err) ->
    Fmt.pr "@[<v>Parse error: %s@, Pos: %d@,@]" err pos; Nop
  | Parse_error (None, err) ->
    Fmt.pr "@[<v>Parse error: %s@]" err; Nop
  | Lexing_error (Some (_,pos), err) ->
    Fmt.pr "@[<v>Lexing error: %s@,Pos: %d@,@]" err pos; Nop
  | Lexing_error (None, err) ->
    Fmt.pr "@[<v>Lexing error: %s@,@]" err; Nop

let () =
  (* initialize the pretty printer *)
  Fmt.pr "@[<v>Welcome to Opetopictt!@,@,@]@?";
  repl_loop ()

