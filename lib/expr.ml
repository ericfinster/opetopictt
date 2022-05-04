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

  (* Variables *)
  | VarE of qname

  (* Let *)
  | LetE of name * expr * expr * expr 

  (* Pi Types *)
  | LamE of name * expr
  | AppE of expr * expr
  | PiE of name * expr * expr

  (* Sigma Types *)
  | PairE of expr * expr
  | FstE of expr
  | SndE of expr
  | SigE of name * expr * expr 

  (* Opetopic Reflexivity *) 
  | ReflE of expr * (name , name tr_expr suite) Either.t 
  | ExpE of idx 

  (* The Universe *) 
  | TypE

(*****************************************************************************)
(*                         Pretty Printing Raw Syntax                        *)
(*****************************************************************************)

let rec pp_qname ppf qnm =
  match qnm with
  | Name nm -> string ppf nm
  | Qual (m,qn) ->
    pf ppf "%s.%a" m pp_qname qn 

let rec pp_expr ppf expr =
  let ppe = pp_expr in
  match expr with
  | VarE qnm -> pp_qname ppf qnm

  | LetE (nm,ty,tm,exp) ->
    pf ppf "let %s : %a@ = %a in@ %a"
      nm pp_expr ty pp_expr tm pp_expr exp 

  | LamE (nm,bdy) -> pf ppf "\u{03bb} %s.@;<1 2>%a" nm ppe bdy
  | AppE (u, v) ->
    pf ppf "%a@;<1 2>%a" ppe u
      (expr_app_parens v) v
      
  | PiE (nm,a,b) when String.equal nm "" ->
    pf ppf "%a \u{2192}@ %a"
      (expr_pi_parens a) a ppe b
  | PiE (nm,dom,cod) ->
    pf ppf "(%s : %a) \u{2192}@ %a" nm
      ppe dom ppe cod

  | PairE (u,v) ->
    pf ppf "%a ,@ %a" pp_expr u pp_expr v
  | FstE u ->
    pf ppf "fst@;<1 2>%a" (expr_app_parens u) u
  | SndE u ->
    pf ppf "snd@;<1 2>%a" (expr_app_parens u) u
      
  | SigE (nm,a,b) when String.equal nm "" ->
    pf ppf "%a \u{d7}@ %a"
      pp_expr a pp_expr b 
  | SigE (nm,a,b) ->
    pf ppf "(%s : %a) \u{d7}@ %a"
      nm pp_expr a pp_expr b 

  | ReflE (a,First nm) ->
    pf ppf "[ %a %@ %s ]" pp_expr a nm
  | ReflE (a,Second pi) ->
    pf ppf "[ %a @[<v>%@ %a@] ]"
      pp_expr a (pp_suite ~sep:(any "@;| ")
                   (Fmt.box (pp_tr_expr Fmt.string))) pi
  | ExpE idx -> pf ppf "*exp* %d" idx 

  | TypE -> pf ppf "U"

and expr_app_parens e =
  match e with
  | PiE _ -> parens pp_expr
  | AppE _ -> parens pp_expr
  | LamE _ -> parens pp_expr
  | PairE _ -> parens pp_expr
  | FstE _ -> parens pp_expr
  | SndE _ -> parens pp_expr
  | SigE _ -> parens pp_expr
  | _ -> pp_expr

and expr_pi_parens e =
  match e with
  | PiE _ -> parens pp_expr
  | _ -> pp_expr
    
