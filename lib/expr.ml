(*****************************************************************************)
(*                                                                           *)
(*                              User Expressions                             *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Base
open Syntax
open Suite

open Opetopes.Idt
open IdtConv
open Opetopes.Complex

(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type expr =

  (* Type theory primitives *)
  | VarE of name
  | LamE of name * icit * expr
  | AppE of expr * expr * icit
  | PiE of name * icit * expr * expr
  | HoleE
  | TypE

  (* Opetopic structure *)
  | FrmE of expr * unit tr_expr suite  

(* This probably belongs elsewhere .... *)
type defn =
  | TermDef of name * expr tele * expr * expr

(*****************************************************************************)
(*                          Parsing Tree Expressions                         *)
(*****************************************************************************)

let rec to_cmplx (s : 'a tr_expr suite) : 'a cmplx =
  match s with
  | Emp -> failwith "empty suite in to_cmplx"
  | Ext (Emp,n) -> Base (to_nst n)
  | Ext (s',n) ->  Adjoin (to_cmplx s', to_nst n)

let rec of_cmplx (c : 'a cmplx) : 'a tr_expr suite =
  match c with
  | Base n -> Ext (Emp, of_nst n)
  | Adjoin (frm,n) ->
    Ext (of_cmplx frm, of_nst n)

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)

let is_app e =
  match e with
  | AppE (_, _, _) -> true
  | _ -> false

let is_pi e =
  match e with
  | PiE (_,_,_,_) -> true
  | _ -> false

let tele_to_pd_dummy _ =
  Error "dummy"

let rec pp_expr_gen ~si:show_imp ppf expr =
  let ppe = pp_expr_gen ~si:show_imp in
  match expr with
  | VarE nm -> string ppf nm
  | LamE (nm,Impl,bdy) -> pf ppf "\\{%s}. %a" nm ppe bdy
  | LamE (nm,Expl,bdy) -> pf ppf "\\%s. %a" nm ppe bdy
  | AppE (u, v, Impl) ->
    if show_imp then
      pf ppf "%a {%a}" ppe u ppe v
    else
      pf ppf "%a" ppe u
  | AppE (u, v, Expl) ->
    let pp_v = if (is_app v) then
        parens ppe
      else ppe in
    pf ppf "%a@, %a" ppe u pp_v v
  | PiE (nm,Impl,dom,cod) ->
    if (is_pi cod) then
      pf ppf "{%s : %a}@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "{%s : %a}@, -> %a" nm
        ppe dom ppe cod
  | PiE (nm,Expl,a,b) when Poly.(=) nm "" ->
    let pp_a = if (is_pi a) then
        parens ppe
      else ppe in
    pf ppf "%a -> %a"
      pp_a a ppe b
  | PiE (nm,Expl,dom,cod) ->
    if (is_pi cod) then
      pf ppf "(%s : %a)@, %a" nm
        ppe dom ppe cod
    else
      pf ppf "(%s : %a)@, -> %a" nm
        ppe dom ppe cod
  | TypE -> string ppf "U"
  | HoleE -> string ppf "_"

  | FrmE _ -> string ppf "frm" 

(*****************************************************************************)
(*                          Matching pretty printers                         *)
(*****************************************************************************)

let pp_expr = pp_expr_gen ~si:false 
let pp_expr_with_impl = pp_expr_gen ~si:true

(*****************************************************************************)
(*                         Expr Syntax Implmentations                        *)
(*****************************************************************************)

module ExprSyntax = struct
  type s = expr
  let var _ _ nm = VarE nm 
  let app u v ict = AppE (u,v,ict)
  let lam nm ict bdy = LamE (nm,ict,bdy)
  let pi nm ict dom cod = PiE (nm,ict,dom,cod)
  let pp_s = pp_expr
end

module ExprUtil = SyntaxUtil(ExprSyntax)
