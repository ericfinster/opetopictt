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

  | EObPos of expr * expr 
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

  (* Opetopic Basics *)
  | EFrm t -> sprintf "Frm %s" (printExpr t)
  | ECell (x, f) -> sprintf "Cell %s %s" (printExpr x) (printExpr f)
  | ETree (x, f) -> sprintf "Tree %s %s" (printExpr x) (printExpr f)
  | EPos (x, f, s) -> sprintf "Pos %s %s %s" (printExpr x) (printExpr f) (printExpr s)
  | ETyp (x, f, s, p) -> sprintf "Typ %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr p)
  | EInh (x, f, s, p) -> sprintf "Inh %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr p)

  (* Frame Constructors *)
  | EFrmEmpty -> "<>"
  | EFrmExt (f, s, t) -> sprintf "%s || %s >> %s" (printExpr f) (printExpr s) (printExpr t)

  (* Opetopic Constructors *)                       
  | EMu (x, f, s, k) -> sprintf "mu %s %s %s %s" (printExpr x) (printExpr f) (printExpr s) (printExpr k)
  | EEta (x, f, a) -> sprintf "eta %s %s %s" (printExpr x) (printExpr f) (printExpr a)
  | ENd (x, f, s, t, a, d, e) ->
     sprintf "nd %s %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s) (printExpr t)
             (printExpr a) (printExpr d) (printExpr e)
  | ELf (x, f, a) -> sprintf "lf %s %s %s" (printExpr x) (printExpr f) (printExpr a)
  | EOb (x, a) -> sprintf "ob %s %s" (printExpr x) (printExpr a)

  (* Position Constructors *)
  | EObPos (x, a) -> sprintf "ob-pos %s %s" (printExpr x) (printExpr a)
  | ENdHere (x, f, s, t, a, d, e) ->
     sprintf "nd-here %s %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s) (printExpr t)
             (printExpr a) (printExpr d) (printExpr e)
  | ENdThere (x, f, s, t, a, d, e, p, q) ->
     sprintf "nd-there %s %s %s %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s) (printExpr t)
             (printExpr a) (printExpr d) (printExpr e) (printExpr p) (printExpr q)
  | EMuPos (x, f, s, k, p, q) ->
     sprintf "mu-pos %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s)
             (printExpr k) (printExpr p) (printExpr q)
  | EEtaPos (x, f, a) -> sprintf "eta-pos %s %s %s" (printExpr x) (printExpr f) (printExpr a)

  (* Position Eliminators *)
  | EObPosElim (x, a, w, c, p) ->
     sprintf "ob-pos-elim %s %s %s %s %s"
             (printExpr x) (printExpr a) (printExpr w)
             (printExpr c) (printExpr p)
  | ELfPosElim (x, f, a, w, p) -> 
     sprintf "lf-pos-elim %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr a)
             (printExpr w) (printExpr p)
  | ENdPosElim (x, f, s, t, a, d, e, w, h, th, p) -> 
     sprintf "nd-pos-elim %s %s %s %s %s %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s) (printExpr t)
             (printExpr a) (printExpr d) (printExpr e) (printExpr w)
             (printExpr h) (printExpr th) (printExpr p)
  | EEtaPosElim (x, f, a, w, n, p) ->
     sprintf "eta-pos-elim %s %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr a) 
             (printExpr w) (printExpr n) (printExpr p) 
  | EMuPosFst (x, f, s, k, p) -> 
     sprintf "mu-pos-fst %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s)
             (printExpr k) (printExpr p)
  | EMuPosSnd (x, f, s, k, p) -> 
     sprintf "mu-pos-snd %s %s %s %s %s"
             (printExpr x) (printExpr f) (printExpr s)
             (printExpr k) (printExpr p)

  (* Basic Type Theory *)
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
  | OTypeT
  
  | FrmT of term
  | CellT of term * term
  | TreeT of term * term
  | PosT of term * term * term
  | TypT of term * term * term * term
  | InhT of term * term * term * term
          
  | FrmEmptyT
  | FrmExtT of term * term * term

  | MuT of term * term * term * term
  | EtaT of term * term * term
  | NdT of term * term * term * term * term * term * term
  | LfT of term * term * term
  | ObT of term * term

  | ObPosT of term * term 
  | NdHereT of term * term * term * term * term * term * term
  | NdThereT of term * term * term * term * term * term * term * term * term
  | MuPosT of term * term * term * term * term * term
  | EtaPosT of term * term * term

  | ObPosElimT of term * term * term * term * term
  | LfPosElimT of term * term * term * term * term
  | NdPosElimT of term * term * term * term * term * term * term * term * term * term * term
  | EtaPosElimT of term * term * term * term * term * term
  | MuPosFstT of term * term * term * term * term
  | MuPosSndT of term * term * term * term * term
               
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
  | OTypeT -> "O"

  (* Opetopic Basics *)
  | FrmT t -> sprintf "Frm %s" (printTerm t)
  | CellT (x, f) -> sprintf "Cell %s %s" (printTerm x) (printTerm f)
  | TreeT (x, f) -> sprintf "Tree %s %s" (printTerm x) (printTerm f)
  | PosT (x, f, s) -> sprintf "Pos %s %s %s" (printTerm x) (printTerm f) (printTerm s)
  | TypT (x, f, s, p) -> sprintf "Typ %s %s %s %s" (printTerm x) (printTerm f) (printTerm s) (printTerm p)
  | InhT (x, f, s, p) -> sprintf "Inh %s %s %s %s" (printTerm x) (printTerm f) (printTerm s) (printTerm p)

  (* Frame Constructors *)
  | FrmEmptyT -> "<>"
  | FrmExtT (f, s, t) -> sprintf "%s || %s >> %s" (printTerm f) (printTerm s) (printTerm t)

  (* Opetopic Constructors *)                       
  | MuT (x, f, s, k) -> sprintf "mu %s %s %s %s" (printTerm x) (printTerm f) (printTerm s) (printTerm k)
  | EtaT (x, f, a) -> sprintf "eta %s %s %s" (printTerm x) (printTerm f) (printTerm a)
  | NdT (x, f, s, t, a, d, e) ->
     sprintf "nd %s %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s) (printTerm t)
             (printTerm a) (printTerm d) (printTerm e)
  | LfT (x, f, a) -> sprintf "lf %s %s %s" (printTerm x) (printTerm f) (printTerm a)
  | ObT (x, a) -> sprintf "ob %s %s" (printTerm x) (printTerm a)

  (* Position Constructors *)
  | ObPosT (x, a) -> sprintf "ob-pos %s %s" (printTerm x) (printTerm a)
  | NdHereT (x, f, s, t, a, d, e) ->
     sprintf "nd-here %s %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s) (printTerm t)
             (printTerm a) (printTerm d) (printTerm e)
  | NdThereT (x, f, s, t, a, d, e, p, q) ->
     sprintf "nd-there %s %s %s %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s) (printTerm t)
             (printTerm a) (printTerm d) (printTerm e) (printTerm p) (printTerm q)
  | MuPosT (x, f, s, k, p, q) ->
     sprintf "mu-pos %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s)
             (printTerm k) (printTerm p) (printTerm q)
  | EtaPosT (x, f, a) -> sprintf "eta-pos %s %s %s" (printTerm x) (printTerm f) (printTerm a)

  (* Position Eliminators *)
  | ObPosElimT (x, a, w, c, p) ->
     sprintf "ob-pos-elim %s %s %s %s %s"
             (printTerm x) (printTerm a) (printTerm w)
             (printTerm c) (printTerm p)
  | LfPosElimT (x, f, a, w, p) -> 
     sprintf "lf-pos-elim %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm a)
             (printTerm w) (printTerm p)
  | NdPosElimT (x, f, s, t, a, d, e, w, h, th, p) -> 
     sprintf "nd-pos-elim %s %s %s %s %s %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s) (printTerm t)
             (printTerm a) (printTerm d) (printTerm e) (printTerm w)
             (printTerm h) (printTerm th) (printTerm p)
  | EtaPosElimT (x, f, a, w, n, p) ->
     sprintf "eta-pos-elim %s %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm a) 
             (printTerm w) (printTerm n) (printTerm p) 
  | MuPosFstT (x, f, s, k, p) -> 
     sprintf "mu-pos-fst %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s)
             (printTerm k) (printTerm p)
  | MuPosSndT (x, f, s, k, p) -> 
     sprintf "mu-pos-snd %s %s %s %s %s"
             (printTerm x) (printTerm f) (printTerm s)
             (printTerm k) (printTerm p)

  (* Basic Type Theory *)
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
