(** Syntax definitions **)

open Printf
   
type expr =
  | EType
  | EOType
  
  | EFrm of expr
  | ECell of expr * expr
  | ETree of expr * expr
  | EPos of expr * expr * expr
  | ETyp of expr * expr * expr * expr
  | EInh of expr * expr * expr * expr
          
  | EFrmEmpty
  | EFrmExt of expr * expr * expr

  | EMu of expr * expr * expr * expr
  | EEta of expr * expr * expr
  | ENd of expr * expr * expr * expr * expr * expr * expr
  | ELf of expr * expr * expr
  | EOb of expr * expr

  | EObPos of expr * expr * expr
  | ENdHere of expr * expr * expr * expr * expr * expr * expr
  | ENdThere of expr * expr * expr * expr * expr * expr * expr * expr * expr
  | EMuPos of expr * expr * expr * expr * expr * expr
  | EEtaPos of expr * expr * expr

  | EObPosElim of expr * expr * expr * expr * expr
  | ELfPosElim of expr * expr * expr * expr * expr
  | ENdPosElim of expr * expr * expr * expr * expr * expr * expr * expr * expr * expr * expr
  | EEtaPosElim of expr * expr * expr * expr * expr * expr
  | EMuPosFst of expr * expr * expr * expr * expr
  | EMuPosSnd of expr * expr * expr * expr * expr
         
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
  | EOType -> "O"
            
  | EFrm t -> sprintf "Frm %s" (printExpr t)
  | ECell (x, f) -> sprintf "Cell %s %s" (printExpr x) (printExpr f)
  | ETree (x, f) -> sprintf "Tree %s %s" (printExpr x) (printExpr f)
  | EPos (x, f, s) -> sprintf "Pos %s %s %s" (printExpr x) (printExpr f) (printExpr s)
  | ETyp (x, f, s, p) -> sprintf "Typ %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr p)
  | EInh (x, f, s, p) -> sprintf "Inh %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr p)
                       
  | EFrmEmpty -> "<>"
  | EFrmExt (f, s, t) -> sprintf "%s || %s >> %s" (printExpr f) (printExpr s) (printExpr t)

  | EMu (x, f, s, k) -> sprintf "mu %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr k)
  | EEta (x, f, a) -> sprintf "eta %s %s %s" (printExpr x) (printExpr f) (printExpr a)
  | ENd (x, f, s, t, a, d, e) -> sprintf "nd %s %s %s %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr t) (printExpr a) (printExpr d) (printExpr e)
  | ELf (x, f, a) -> sprintf "lf %s %s %s" (printExpr x) (printExpr f) (printExpr a)
  | EOb (x, a) -> sprintf "ob %s %s" (printExpr x) (printExpr a)

  | EObPos (x, f, a) -> ""
  | ENdHere (x, f, s, t, a, d, e) -> ""
  | ENdThere (x, f, s, t, a, d, e, p, q) -> ""
  | EMuPos (x, f, s, k, p, q) -> ""
  | EEtaPos (x, f, a) -> ""

  | EObPosElim (x, a, w, c, p) -> ""
  | ELfPosElim (x, f, a, w, p) -> ""
  | ENdPosElim (x, f, s, t, a, d, e, w, h, th, p) -> ""
  | EEtaPosElim (x, f, a, w, n, p) -> ""
  | EMuPosFst (x, f, s, k, p) -> ""
  | EMuPosSnd (x, f, s, k, p) -> ""
                               
  | EVar id -> id
  | EPi (id , u , v) -> sprintf "(%s : %s) -> %s" id (printExpr u) (printExpr v)
  | ELam (id , u) -> sprintf "\\%s. %s" id (printExpr u)
  | EApp (u , v) -> sprintf "(%s %s)" (printExpr u) (printExpr v)
  | ESig (id , u , v) -> sprintf "(%s : %s) * %s" id (printExpr u) (printExpr v)
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
