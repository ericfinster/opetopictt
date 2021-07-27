(*****************************************************************************)
(*                                                                           *)
(*                              User Expressions                             *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Syntax

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type expr =

  (* Type theory primitives *)
  | VarE of name
  | LamE of name * expr
  | AppE of expr * expr 
  | PiE of name * expr * expr
           
  | PosE
  | ElE of expr
  | PosPiE of name * expr * expr 
  | PosSigE of name * expr * expr 

  | TypE

(* This probably belongs elsewhere .... *)
type defn =
  | TermDef of name * expr tele * expr * expr

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)

let is_app e =
  match e with
  | AppE (_, _) -> true
  | _ -> false

let is_pi e =
  match e with
  | PiE (_,_,_) -> true
  | _ -> false

let tele_to_pd_dummy _ =
  Error "dummy"

let rec pp_expr_gen ~si:show_imp ppf expr =
  let ppe = pp_expr_gen ~si:show_imp in
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,bdy) -> pf ppf "\\%s. %a" nm ppe bdy
  | AppE (u, v) ->
    let pp_v = if (is_app v) then
        parens ppe
      else ppe in
    pf ppf "%a@, %a" ppe u pp_v v
  | PiE (nm,a,b) when String.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in
    pf ppf "%a \u{2192} %a"
      pp_a a ppe b
  | PiE (nm,dom,cod) ->
    if (is_pi cod) then
      pf ppf "(%s : %a)@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "(%s : %a)@, \u{2192} %a" nm
        ppe dom ppe cod
  | PosE -> string ppf "Pos"
  | ElE p -> pf ppf "El %a" ppe p
  | PosPiE (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{2192}\u{209A} %a" nm ppe a ppe b 
  | PosSigE (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{D7}\u{209A} %a" nm ppe a ppe b 
  | TypE -> string ppf "U"
    
(*****************************************************************************)
(*                          Matching pretty printers                         *)
(*****************************************************************************)

let pp_expr = pp_expr_gen ~si:false 
let pp_expr_with_impl = pp_expr_gen ~si:true

