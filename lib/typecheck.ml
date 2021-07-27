(*****************************************************************************)
(*                                                                           *)
(*                           Typechecking Routines                           *)
(*                                                                           *)
(*****************************************************************************)

open Fmt

open Base
open Suite
open Expr
open Term
open Value
open Eval
open Syntax

       
(* Monadic bind for errors in scope *)
let (let*) m f = Base.Result.bind m ~f

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type bd =
  | Bound
  | Defined

type ctx = {
  top : top_env;
  loc : loc_env;
  lvl : lvl;
  types : (name * (bd * value)) suite;
}

let empty_ctx = {
  top = Emp;
  loc = Emp;
  lvl = 0;
  types = Emp;
}

let empty_loc gma = {
  top = gma.top;
  loc = Emp;
  lvl = 0;
  types = filter gma.types
      (fun (_,(bd,_)) ->
         match bd with
         | Defined -> true
         | Bound -> false)

}

let bind gma nm ty =
  let l = gma.lvl in {
    loc = Ext (gma.loc, varV l);
    top = gma.top;
    lvl = l+1;
    types = Ext (gma.types,(nm,(Bound,ty)));
  }

let define gma nm tm ty = {
  loc = gma.loc;
  top = Ext (gma.top,(nm,tm));
  lvl = gma.lvl;
  types = Ext (gma.types,(nm,(Defined,ty)));
}

let names gma =
  map_suite gma.types ~f:fst

(*****************************************************************************)
(*                                   Debug                                   *)
(*****************************************************************************)

let rec quote_types ufld typs =
  match typs with
  | Emp -> (Emp,0)
  | Ext (typs', (nm, (Defined,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm,typ_tm)),l)
  | Ext (typs', (nm, (_,typ))) ->
    let (res_typs, l) = quote_types ufld typs' in
    let typ_tm = quote ufld l typ in
    (Ext (res_typs,(nm, typ_tm)),l+1)

let dump_ctx ufld gma =
  let (tl,_) = quote_types ufld gma.types in
  pr "Context: @[<hov>%a@]@,"
    (pp_suite (parens (pair ~sep:(any " : ") string pp_term))) tl

(*****************************************************************************)
(*                               Typing Errors                               *)
(*****************************************************************************)
           
type typing_error = [
  | `NameNotInScope of name
  | `TypeMismatch of string
  | `InvalidShape of string
  | `NotImplemented of string
  | `InternalError
]

let pp_error ppf e =
  match e with
  | `NameNotInScope nm -> Fmt.pf ppf "Name not in scope: %s" nm
  | `IcityMismatch (_, _) -> Fmt.pf ppf "Icity mismatch"
  | `TypeMismatch msg -> Fmt.pf ppf "%s" msg  
  | `InvalidShape msg -> Fmt.pf ppf "Invalid shape: %s" msg
  | `NotImplemented f -> Fmt.pf ppf "Feature not implemented: %s" f
  | `InternalError -> Fmt.pf ppf "Internal Error"


(*****************************************************************************)
(*                             Typechecking Rules                            *)
(*****************************************************************************)
                            
let rec check gma expr typ =
  (* let typ_tm = quote false gma.lvl typ in
   * let typ_expr = term_to_expr (names gma) typ_tm in
   * pr "Checking @[%a@] has type @[%a@]@," pp_expr_with_impl expr pp_expr_with_impl typ_expr ; *)

  match (expr, typ) with

  | (e , TopV (_,_,tv)) ->
    check gma e tv

  | (LamE (nm,e) , PiV (_,a,b))  ->
    let* bdy = check (bind gma nm a) e (b $$ varV gma.lvl) in
    Ok (LamT (nm,bdy))

  (* Going to need to work on this part ... *)
  | (e, expected) ->
    let* (e',inferred) = infer gma e in
    if (Poly.(=) expected inferred) then
      Ok e'
    else
      let nms = names gma in
         let inferred_nf = term_to_expr nms (quote false gma.lvl inferred) in
         let expected_nf = term_to_expr nms (quote true gma.lvl expected) in
      let msg = String.concat [ str "@[<v>The expression: @,@, @[%a@]@,@,@]" pp_expr e;
                                str "@[<v>has type: @,@,  @[%a@]@,@,@]" pp_expr inferred_nf;
                                str "@[<v>but was expected to have type: @,@, @[%a@]@,@]"
                                 pp_expr expected_nf ]

      in Error (`TypeMismatch msg)


and infer gma expr =
  (* pr "@[<v>Inferring type of: @[%a@]@,@]"
   *   pp_expr_with_impl expr ; *)
  match expr with

  | VarE nm -> (
      try
        let (idx,(b,typ)) = assoc_with_idx nm gma.types in
        match b with
        | Bound -> Ok (VarT idx, typ)
        | Defined -> Ok (TopT nm, typ)
      with Lookup_error -> Error (`NameNotInScope nm)
    )

  | AppE (u,v) -> 
    let* (u',ut) = infer gma u in
    begin match ut with
      | PiV (_,a,b) ->
        let* v' = check gma v a in
        Ok (AppT (u', v') , b $$ eval gma.top gma.loc v')
      (* not a function type ...*)
      | _ -> Error `InternalError
    end

  | PiE (nm,a,b) ->
    let* a' = check gma a TypV in
    let* b' = check (bind gma nm (eval gma.top gma.loc a')) b TypV in
    Ok (PiT (nm,a',b') , TypV)

  | TypE -> Ok (TypT , TypV)

  (* inferrence failed *)
  | _ -> Error `InternalError

and with_tele : 'a . ctx -> expr tele
  -> (ctx -> value tele -> term tele -> ('a,typing_error) Result.t)
  -> ('a,typing_error) Result.t = fun gma tl m ->
  match tl with
  | Emp -> m gma Emp Emp
  | Ext (tl',(id,ty)) ->
    with_tele gma tl' (fun g tv tt ->
        let* ty_tm = check g ty TypV in
        let ty_val = eval g.top g.loc ty_tm in
        m (bind g id ty_val)
          (Ext (tv,(id,ty_val)))
          (Ext (tt,(id,ty_tm))))


let rec abstract_tele_with_type (tl : expr tele) (ty : expr) (tm : expr) =
  match tl with
  | Emp -> (ty,tm)
  | Ext (tl',(nm,ty')) ->
    abstract_tele_with_type tl' (PiE (nm,ty',ty)) (LamE (nm,tm))
  
let rec check_defs gma defs =
  match defs with
  | [] -> Ok gma
  | (TermDef (id,tl,ty,tm))::ds ->
    pr "----------------@,";
    pr "Checking definition: %s@," id;
    let (abs_ty,abs_tm) = abstract_tele_with_type tl ty tm in
    let* ty_tm = check gma abs_ty TypV in
    let ty_val = eval gma.top gma.loc ty_tm in
    let* tm_tm = check gma abs_tm ty_val in
    let tm_val = eval gma.top gma.loc tm_tm in
    pr "Checking complete for %s@," id;
    (* let tm_nf = term_to_expr Emp (quote (gma.lvl) tm_val false) in
     * let ty_nf = term_to_expr Emp (quote (gma.lvl) ty_val false) in *)
    (* pr "Type: @[%a@]@," pp_expr ty_nf; *)
    (* pr "Term: @[%a@]@," pp_expr tm_nf; *)
    check_defs (define gma id tm_val ty_val) ds
