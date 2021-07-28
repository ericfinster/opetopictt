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

  | PosT
  | ElT of term
  | PosUnitT
  | PosEmptyT
  | PosSumT of term * term 
  | PosSigT of name * term * term

  | PosTtT
  | PosInrT of term
  | PosInlT of term
  | PosPairT of term * term
                
  | PosPiT of name * term * term
  | PosLamT of name * term 
  | PosAppT of term * term

  | PosBotElimT
  | PosTopElimT of term
  | PosSumElimT of term * term
  | PosSigElimT of term 
      

(*****************************************************************************)
(*                               Term equality                               *)
(*****************************************************************************)

let rec term_eq u v =
  match (u, v) with
  | (VarT i , VarT i') -> Int.equal i i'
  | (TopT nm , TopT nm') -> String.equal nm nm'
                            
  | (LamT (_,u') , LamT (_, v')) -> term_eq u' v'
  | (AppT (a,b) , AppT (a',b')) -> term_eq a a' && term_eq b b'
  | (PiT (_,a,b) , PiT (_,a',b')) -> term_eq a a' && term_eq b b'
  | (TypT , TypT) -> true 
  
  | (PosT , PosT) -> true
  | (ElT p , ElT p') -> term_eq p p'
                          
  | (PosUnitT , PosUnitT) -> true
  | (PosEmptyT , PosEmptyT) -> true
  | (PosSumT (p,q) , PosSumT (p',q')) -> term_eq p p' && term_eq q q'
  | (PosSigT (_,p,q) , PosSigT (_,p',q')) -> term_eq p p' && term_eq q q'
  
  | (PosTtT , PosTtT) -> true
  | (PosInlT p , PosInlT p') -> term_eq p p'
  | (PosInrT p , PosInrT p') -> term_eq p p'
  | (PosPairT (p,q), PosPairT (p',q')) -> term_eq p p' && term_eq q q'
                
  | (PosPiT (_,p,q) , PosPiT (_,p',q')) -> term_eq p p' && term_eq q q'
  | (PosLamT (_,p) , PosLamT (_,p')) -> term_eq p p'
  | (PosAppT (p,q), PosAppT (p',q')) -> term_eq p p' && term_eq q q'
  
  | (PosBotElimT , PosBotElimT) -> true
  | (PosTopElimT p , PosTopElimT p') -> term_eq p p'
  | (PosSumElimT (p,q) , PosSumElimT (p',q')) -> term_eq p p' && term_eq q q'
  | (PosSigElimT p , PosSigElimT p') -> term_eq p p'

  | _ -> false 

  
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
      
  | PosT -> PosE
  | ElT t -> ElE (tte nms t)

  | PosUnitT -> PosUnitE
  | PosEmptyT -> PosEmptyE 
  | PosSumT (u,v) ->
    PosSumE (tte nms u, tte nms v) 
  | PosSigT (nm,a,b) ->
    PosSigE (nm, tte nms a, tte (Ext (nms,nm)) b)

  | PosTtT -> PosTtE 
  | PosInlT u -> PosInlE (tte nms u) 
  | PosInrT v -> PosInrE (tte nms v)
  | PosPairT (u,v) ->
    PosPairE (tte nms u, tte nms v)
                
  | PosPiT (nm,a,b) ->
    PosPiE (nm, tte nms a, tte (Ext (nms,nm)) b)
  | PosLamT (nm,b) ->
    PosLamE (nm, tte (Ext (nms,nm)) b) 
  | PosAppT (u, v) ->
    PosAppE (tte nms u, tte nms v) 

  | PosBotElimT -> PosBotElimE 
  | PosTopElimT u ->
    PosTopElimE (tte nms u)
  | PosSumElimT (u, v) ->
    PosSumElimE (tte nms u, tte nms v) 
  | PosSigElimT u ->
    PosSigElimE (tte nms u)

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
      
  | PosT -> pf ppf "Pos"
  | ElT t -> pf ppf "El %a" pp_term t 

  | PosUnitT -> pf ppf "\u{22A4}\u{209A}"
  | PosEmptyT -> pf ppf "\u{22A5}\u{209A}"
  | PosSumT (l, r) ->
    pf ppf "%a \u{2294}\u{209A} %a" pp_term l pp_term r 
  | PosSigT (nm, a, b) ->
    pf ppf "(%s : %a)@, \u{D7}\u{209A} %a" nm pp_term a pp_term b 
  | PosTtT -> pf ppf "tt\u{209A}"
  | PosInlT u -> pf ppf "inl\u{209A} %a" pp_term u 
  | PosInrT v -> pf ppf "inr\u{209A} %a" pp_term v
  | PosPairT (u,v) ->
    pf ppf "%a , %a" pp_term u pp_term v
      
  | PosPiT (nm,a,b) ->
    pf ppf "(%s : %a)@, \u{2192}\u{209A} %a" nm pp_term a pp_term b 
  | PosLamT (nm,b) ->
    pf ppf "\u{03BB}\u{209A} %s, %a" nm pp_term b 
  | PosAppT (u,v) ->
    pf ppf "%a@, @@ %a" pp_term u pp_term v

  | PosBotElimT ->
    pf ppf "\u{22A5}-elim"
  | PosTopElimT e ->
    pf ppf "\u{22A4}-elim %a" pp_term e
  | PosSumElimT (u,v) ->
    pf ppf "\u{2294}-elim %a %a" pp_term u pp_term v
  | PosSigElimT e ->
    pf ppf "\u{D7}-elim %a" pp_term e 


