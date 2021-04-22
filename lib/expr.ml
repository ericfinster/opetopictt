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

  (* Opetopic Expressions *)
  | CellE of expr * tr_expr suite 

and tr_expr =
  | Unit
  | Expr of expr
  | Leaf of tr_expr
  | Node of tr_expr * tr_expr

(* This probably belongs elsewhere .... *)
type defn =
  | TermDef of name * expr tele * expr * expr

(*****************************************************************************)
(*                          Parsing Tree Expressions                         *)
(*****************************************************************************)

let parse_unit (t : tr_expr) : unit =
  match t with
  | Unit -> ()
  | _ -> failwith "not a unit"

let parse_expr (t : tr_expr) : expr =
  match t with
  | Expr e -> e
  | _ -> failwith "not an expression"

let rec parse_tr_expr : 'a 'b. tr_expr
  -> (tr_expr -> 'b)
  -> (tr_expr -> 'a)
  -> ('a,'b) idt = fun t lf nd -> 
  match t with
  | Unit -> failwith ""
  | Expr _ -> failwith ""
  | Leaf t -> Lf (lf t)
  | Node (a,sh) ->
    let parse_shell t =
      parse_tr_expr t lf nd in 
    let a' = nd a in
    let sh' = parse_tr_expr sh parse_unit parse_shell
    in Nd (a',sh')

let to_expr_nst (t : tr_expr) : expr nst =
  parse_tr_expr t parse_expr parse_expr

let rec from_idt : 'a 'b. ('a, 'b) idt
  -> ('b -> tr_expr)
  -> ('a -> tr_expr)
  -> tr_expr = fun t lf nd ->
  match t with
  | Lf b -> lf b
  | Nd (a,sh) ->
    let sh_expr = from_idt sh
        (fun _ -> Unit)
        (fun br -> from_idt br lf nd) in 
    Node (nd a , sh_expr)

let rec from_tr : 'a . 'a tr -> ('a -> tr_expr) -> tr_expr =
  fun t f -> 
  match t with
  | Lf _ -> Leaf Unit
  | Nd (a,sh) ->
    Node (f a, from_tr sh (fun br -> from_tr br f))
    
let rec from_expr_nst (n : expr nst) : tr_expr =
  let mk_expr e = Expr e in 
  from_idt n mk_expr mk_expr

let rec to_cmplx (s : tr_expr suite) : expr cmplx =
  match s with
  | Emp -> failwith "empty suite"
  | Ext (Emp,t) -> Base (to_expr_nst t)
  | Ext (s',t) ->  Adjoin (to_cmplx s', to_expr_nst t)

let rec from_cmplx (c : expr cmplx) : tr_expr suite =
  match c with
  | Base n -> Ext (Emp, from_expr_nst n)
  | Adjoin (frm,n) ->
    Ext (from_cmplx frm, from_expr_nst n)

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

  | CellE _ -> string ppf "cell"
    
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
