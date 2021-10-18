(*****************************************************************************)
(*                                                                           *)
(*                                 Commands                                  *)
(*                                                                           *)
(*****************************************************************************)

open Base
open Expr
open Term
open Suite
open Syntax
open Typecheck

open Opetopes.Idt.IdtConv

type cmd =
  | Define of name * expr tele * expr * expr
  | Normalize of expr tele * expr  * expr
  | Expand of expr tele * expr  * expr * string tr_expr suite 

let rec run_cmds cmds =
  
  let module E = ExprUtil in
  
  match cmds with
  | [] -> tcm_ctx
  | (Define (id,tl,ty,tm))::cs ->
    Fmt.pr "----------------@,";
    Fmt.pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = E.abstract_tele_with_type tl ty tm in
    let* ty_tm = tcm_check abs_ty TypV in
    let* ty_val = tcm_eval ty_tm in
    let* tm_tm = tcm_check abs_tm ty_val in
    let* tm_val = tcm_eval tm_tm in
    Fmt.pr "Checking complete for %s@," id;
    (* let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
     * let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in *)
    (* pr "Type: @[%a@]@," pp_expr ty_nf; *)
    (* pr "Term: @[%a@]@," pp_expr tm_nf; *)
    let* gma = tcm_ctx in
    tcm_in_ctx (define gma id tm_val ty_val)
      (run_cmds cs)
      
  | (Normalize (tl,ty,tm))::cs ->
    Fmt.pr "----------------@,";
    Fmt.pr "Normalizing: @[%a@]@," pp_expr tm;
    let* _ = tcm_in_tele tl (fun _ ->
        let open Value in 
        let* ty' = tcm_check ty TypV in
        let* ty_v = tcm_eval ty' in
        log_val "ty_v" ty_v pp_value; 
        let* tm' = tcm_check tm ty_v in
        log_val "tm'" tm' pp_term;
        let* tm_v = tcm_eval tm' in
        log_val "tm_v" tm_v pp_value; 
        let* tm_nf = tcm_quote tm_v true in
        let* gma = tcm_ctx in 
        let t_nf_expr = term_to_expr (names gma) tm_nf in
        Fmt.pr "Result: @[%a@]@," pp_expr t_nf_expr; 
        tcm_ok ()) in
    run_cmds cs

  | (Expand (tl,ty,tm,op))::cs ->
    let open Eval in
    (* let open Opetopes.Complex in  *)
    Fmt.pr "----------------@,";
    Fmt.pr "Expanding: @[%a@]@," pp_expr tm;
    let* _ = tcm_in_tele tl (fun _ ->
        let* ty' = tcm_check ty TypV in
        let* ty_v = tcm_eval ty' in
        let* tm' = tcm_check tm ty_v in
        let* tm_v = tcm_eval tm' in
        let* pi = tcm_to_cmplx op in

        let* gma = tcm_ctx in
        let ex_v = refl_val Emp 0 tm_v pi in
        (* lengthen the level ? *)
        (* let cell_nms = labels pi in  *)
        let ex_nf = quote true gma.lvl ex_v in
        (* let nms =
         *   join (map_suite (names gma)
         *           ~f:(fun nm -> from_list
         *                  (List.map cell_nms ~f:(fun c -> nm ^ c)))) in
         * log_val "nms" nms (pp_suite Fmt.string); *)
        let ex_nf_expr = term_to_expr (names gma) ex_nf in 
        (* Fmt.pr "Term: @[%a@]@," pp_term ex_nf; *)
        Fmt.pr "Expression: @[%a@]@," pp_expr ex_nf_expr;
        tcm_ok ()) in
    
    run_cmds cs

  (* | (Infer (tl,tm))::cs ->
   *   Fmt.pr "----------------@,";
   *   Fmt.pr "Infering the type of: @[%a@]@," pp_expr tm;
   *   let* _ = with_tele gma tl (fun gma' _ _ ->
   *       let* (_,ty) = infer gma' tm in
   *       let ty_nf = quote true gma'.lvl (down_typ ty) in
   *       let ty_expr = term_to_expr (names gma') ty_nf in 
   *       Fmt.pr "Result type: @[%a@]@," pp_expr ty_expr; 
   *       Ok ()) in  
   *   run_cmds gma cs *)
