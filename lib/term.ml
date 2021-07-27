(*****************************************************************************)
(*                                                                           *)
(*                              Internal Syntax                              *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Expr
open Suite
open Syntax
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type term =

  (* Primitives *)
  | VarT of idx
  | TopT of name
  | LamT of name * term
  | AppT of term * term 
  | PiT of name * term * term
  | TypT

(*****************************************************************************)
(*                            Terms to Expressions                           *)
(*****************************************************************************)

let rec term_to_expr nms tm =
  let tte = term_to_expr in
  match tm with
  | VarT i ->
    let nm = db_get i nms in VarE nm
  | TopT nm -> VarE nm
  | LamT (nm,bdy) ->
    LamE (nm, tte (Ext (nms,nm)) bdy)
  | AppT (u,v) ->
    AppE (tte nms u, tte nms v)
  | PiT (nm,a,b) ->
    PiE (nm, tte nms a, tte (Ext (nms,nm)) b)
  | TypT -> TypE

(*****************************************************************************)
(*                                 Telescopes                                *)
(*****************************************************************************)

let rec tele_to_pi tl ty =
  match tl with
  | Emp -> ty
  | Ext (tl',(nm,ty_tm)) ->
    tele_to_pi tl' (PiT (nm,ty_tm,ty))

let pi_to_tele ty =
  let rec go tl ty =
    match ty with
    | PiT (nm,a,b) ->
      go (Ext (tl,(nm,a))) b
    | _ -> (tl,ty)
  in go Emp ty

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let is_app_tm tm =
  match tm with
  | AppT (_,_) -> true
  | _ -> false

let is_pi_tm tm =
  match tm with
  | PiT (_,_,_) -> true
  | _ -> false

let rec pp_term ppf tm =
  match tm with
  | VarT i -> int ppf i
  | TopT nm -> string ppf nm
  | LamT (nm,t) ->
    pf ppf "\\%s. %a" nm pp_term t
  | AppT (u,v) ->
    (* Need's a generic lookahead for parens routine ... *)
    let pp_v = if (is_app_tm v) then
        parens pp_term
      else pp_term in
    pf ppf "%a %a" pp_term u pp_v v
  | PiT (nm,a,p) when Poly.(=) nm "" ->
    let pp_a = if (is_pi_tm a) then
        parens pp_term
      else pp_term in
    pf ppf "%a -> %a"
      pp_a a pp_term p
  | PiT (nm,a,p) ->
    pf ppf "(%s : %a) -> %a" nm
      pp_term a pp_term p
  | TypT -> pf ppf "U"

