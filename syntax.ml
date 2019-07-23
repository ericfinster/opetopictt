(** Syntax definitions **)

open Printf
   
type expr =
  | EType
  | EFrmEmpty
  | EFrmExt of expr * expr * expr
  | EVar of string
  | EPi of string * expr * expr
  | ELam of string * expr
  | EApp of (expr * expr)
  | ESig of string * expr * expr
  | EPair of expr * expr
  | EFst of expr
  | ESnd of expr

let rec printExpr e =
  match e with
  | EType -> "U"
  | EFrmEmpty -> "<>"
  | EFrmExt (f, s, t) ->
     sprintf "%s || %s >> %s" (printExpr f) (printExpr s) (printExpr t)
  | EVar id -> id
  | EPi (id , u , v) ->
     sprintf "(%s : %s) -> %s" id (printExpr u) (printExpr v)
  | ELam (id , u) ->
     sprintf "\\%s. %s" id (printExpr u)
  | EApp (u , v) ->
     sprintf "(%s %s)" (printExpr u) (printExpr v)
  | ESig (id , u , v) -> 
     sprintf "(%s : %s) * %s" id (printExpr u) (printExpr v)
  | EPair (u , v) -> sprintf "(%s , %s)" (printExpr u) (printExpr v)
  | EFst u -> sprintf "fst %s" (printExpr u)
  | ESnd u -> sprintf "snd %s" (printExpr u)
          
type cmd =
  | Def of (string * expr * expr)
          
type term =
  | TypeT
  | FVarT of string
  | BVarT of int
  | PiT of term * term
  | LamT of term
  | AppT of term * term
  | SigT of term * term
  | PairT of term * term
  | FstT of term
  | SndT of term

(* I see.  Here you need to use some tools from locally nameless
   syntax to abstract in a context and whatnot, lifting out the names
   of variables and so on ... *)
          
let rec printTerm tm =
  match tm with
  | TypeT -> "U"
  | FVarT id -> id
  | BVarT k ->
     sprintf "%d" k
  | PiT (u , v) ->
     sprintf "(_ : %s) -> %s" (printTerm u) (printTerm v)
  | LamT u ->
     sprintf "\\_. %s" (printTerm u)
  | AppT (u , v) ->
     sprintf "(%s %s)" (printTerm u) (printTerm v)
  | SigT (u , v) -> 
     sprintf "(_ : %s) * %s" (printTerm u) (printTerm v)
  | PairT (u , v) -> 
     sprintf "(%s , %s)" (printTerm u) (printTerm v)
  | FstT u -> sprintf "fst %s" (printTerm u)
  | SndT u -> sprintf "snd %s" (printTerm u)
