(*****************************************************************************)
(*                                                                           *)
(*                             The Interpreter                               *)
(*                                                                           *)
(*****************************************************************************)

open Opetopictt.Io
open Opetopictt.Eval        
open Opetopictt.Term
open Opetopictt.Expr
open Opetopictt.Lexer
open Opetopictt.Syntax
open Opetopictt.Typecheck
       
(*****************************************************************************)
(*                                  Options                                  *)
(*****************************************************************************)
    
let usage = "optti [options] [file]"

let current_context = ref empty_ctx 

(*****************************************************************************)
(*                              Main Entry Point                             *)
(*****************************************************************************)

let rec repl_loop _ =
  Fmt.pr "@[#> @]@?" ; 
  let str = read_line () in
  try begin match parse_cmd (str ^ ";") with
    | Quit -> Format.print_flush () ; exit 0
    | Infer e ->
      let gma = ! current_context in 
      begin try begin match tcm_infer e gma with
        | Ok (_,typv) ->
          let typt = quote false gma.level typv in 
          let typ_expr = term_to_expr (names gma) typt in
          Fmt.pr "Inferred type: @[%a@]@," pp_expr typ_expr ;
          repl_loop ()
        | Error err ->
          Fmt.pr "@,Typing error: @,@,%a@,@," pp_error err ; 
          repl_loop ()
      end
        with
        | Internal_error msg -> 
          Fmt.pr "@,An internal error has occured : @,@,%s@," msg ; 
          repl_loop ()
      end
    | Normalize e ->
      let gma = ! current_context in 
      begin try begin match tcm_infer e gma with
        | Ok (tm,_) ->
          let tmv = eval (top gma) (loc gma) tm in 
          let tm_nf = quote true gma.level tmv in 
          let typ_expr = term_to_expr (names gma) tm_nf in
          Fmt.pr "Normalized expression: @[%a@]@," pp_expr typ_expr ;
          repl_loop ()
        | Error err ->
          Fmt.pr "@,Typing error: @,@,%a@,@," pp_error err ; 
          repl_loop ()
      end
        with
        | Internal_error msg -> 
          Fmt.pr "@,An internal error has occured : @,@,%s@," msg ; 
          repl_loop ()
      end
    | Assume tl -> 
      let gma = ! current_context in
      let m = tcm_in_tele tl (fun _ _ -> tcm_ctx) in 
      begin try begin match m gma with
        | Ok gma' ->
          current_context := gma' ; 
          Fmt.pr "Context ok@," ; 
          repl_loop ()
        | Error err ->
          Fmt.pr "@,Typing error: @,@,%a@,@," pp_error err ; 
          repl_loop ()
      end
        with
        | Internal_error msg -> 
          Fmt.pr "@,An internal error has occured : @,@,%s@," msg ; 
          repl_loop ()
      end
      
  end with
  | Parse_error (Some (line,pos), err) ->
    Fmt.pr "@[<v>Parse error: %s@,Line: %d, Pos: %d@,@]" err line pos;
    repl_loop ()
  | Parse_error (None, err) ->
    Fmt.pr "@[<v>Parse error: %s@]" err;
    repl_loop ()
  | Lexing_error (Some (line,pos), err) ->
    Fmt.pr "@[<v>Lexing error: %s@,Line: %d, Pos: %d@,@]" err line pos;
    repl_loop ()
  | Lexing_error (None, err) ->
    Fmt.pr "@[<v>Lexing error: %s@,@]" err;
    repl_loop ()

let () =
  (* initialize the pretty printer *)
  Fmt.pr "@[<v>Welcome to Opetopictt!@,@,@]@?";
  repl_loop ()

