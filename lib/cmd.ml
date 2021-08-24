(*****************************************************************************)
(*                                                                           *)
(*                                 Commands                                  *)
(*                                                                           *)
(*****************************************************************************)

open Expr
open Term 
open Eval 
open Syntax
open Typecheck

type cmd =
  | Let of name * expr tele * expr * expr
  | Normalize of expr tele * expr  * expr
  | Infer of expr tele * expr 

let rec run_cmds gma cmds =
  match cmds with
  | [] -> Ok gma
  | (Let (id,tl,ty,tm))::cs ->
    Fmt.pr "----------------@,";
    Fmt.pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele_with_type tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in
    Fmt.pr "Checking complete for %s@," id;
    (* let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
     * let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in *)
    (* pr "Type: @[%a@]@," pp_expr ty_nf; *)
    (* pr "Term: @[%a@]@," pp_expr tm_nf; *)
    run_cmds (define gma id tm_val ty_val) cs
  | (Normalize (tl,ty,tm))::cs ->
    Fmt.pr "----------------@,";
    Fmt.pr "Normalizing: @[%a@]@," pp_expr tm;
    let* _ = with_tele gma tl (fun gma' _ _ ->
        let* ty' = check gma' ty TypV in
        let ty_v = eval gma'.top gma'.loc ty' in 
        let* tm' = check gma' tm ty_v in
        let t_nf = normalize gma tm' ty_v in 
        let t_nf_expr = term_to_expr (names gma') t_nf in
        Fmt.pr "Result: @[%a@]@," pp_expr t_nf_expr; 
        Ok ()) in  
    run_cmds gma cs 
  | (Infer (tl,tm))::cs ->
    Fmt.pr "----------------@,";
    Fmt.pr "Infering the type of: @[%a@]@," pp_expr tm;
    let* _ = with_tele gma tl (fun gma' _ _ ->
        let* (_,ty) = infer gma' tm in
        let ty_nf = quote true gma'.lvl (down_typ ty) in
        let ty_expr = term_to_expr (names gma') ty_nf in 
        Fmt.pr "Result type: @[%a@]@," pp_expr ty_expr; 
        Ok ()) in  
    run_cmds gma cs 
