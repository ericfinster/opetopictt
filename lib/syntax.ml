(*****************************************************************************)
(*                                   Syntax                                  *)
(*****************************************************************************)

open Base
open Suite


(*****************************************************************************)
(*                                 Raw Syntax                                *)
(*****************************************************************************)

type name = string
  
type expr =
  | VarE of name
  | LamE of name * expr
  | AppE of expr * expr
  | PiE of name * expr * expr
  | TypE
  | HoleE

(*****************************************************************************)
(*                              Internal Syntax                              *)
(*****************************************************************************)

type idx = int
type mvar = int

type bd =
  | Bound
  | Defined

type term =
  | VarT of idx
  | LamT of name * term
  | AppT of term * term
  | PiT of name * term * term
  | TypT
  | MetaT of mvar
  | InsMetaT of mvar * bd suite

(*****************************************************************************)
(*                                   Values                                  *)
(*****************************************************************************)

type lvl = int

type value =
  | FlexV of mvar * spine
  | RigidV of lvl * spine
  | LamV of name * closure
  | PiV of name * value * closure 
  | TypV 

and env = value suite
and spine = value suite

and closure =
  | Closure of env * term

(*****************************************************************************)
(*                           Metavariable Context                            *)
(*****************************************************************************)

type meta_entry =
  | Solved of value
  | Unsolved

type metamap = (mvar,meta_entry,Int.comparator_witness) Map.t

let next_meta : int ref = ref 0
    
let metacontext : metamap ref =
  ref (Map.empty (module Int))

exception Meta_error of string
    
let lookup_meta m =
  let mctx = ! metacontext in
  match Map.find mctx m with
  | Some mentry -> mentry
  | None -> raise (Meta_error "unrecognized metavariable")

(*****************************************************************************)
(*                                 Evaluation                                *)
(*****************************************************************************)

exception Eval_error of string

let rec eval rho tm =
  match tm with
  | VarT i -> nth i rho
  | LamT (nm,u) -> LamV (nm, Closure (rho,u))
  | AppT (u,v) -> appV (eval rho u) (eval rho v)
  | PiT (nm,u,v) -> PiV (nm, eval rho u, Closure (rho,v))
  | TypT -> TypV
  | MetaT m -> metaV m
  | InsMetaT (m,bds) -> appBdsV rho (metaV m) bds

and metaV m =
  match lookup_meta m with
  | Unsolved -> FlexV (m, Emp)
  | Solved v -> v 

and ($$) c v =
  match c with
  | Closure (rho,tm) -> eval (Ext (rho,v)) tm 

and appV t u =
  match t with
  | FlexV (m,sp) -> FlexV (m,Ext(sp,u))
  | RigidV (i,sp) -> RigidV (i,Ext(sp,u))
  | LamV (_,cl) -> cl $$ u 
  | _ -> raise (Eval_error "malformed app")

and appBdsV rho v bds =
  match (rho , bds) with
  | (Emp,Emp) -> v
  | (Ext (rho',u),Ext (bds',Bound)) -> appV (appBdsV rho' v bds') u 
  | (Ext (rho',_),Ext (bds',Defined)) -> appBdsV rho' v bds'
  | _ -> raise (Eval_error "malfomed bounding mask")

let rec appSpV v sp =
  match sp with
  | Emp -> v
  | Ext (sp',u) -> appV (appSpV v sp') u
    
let rec mforce v =
  match v with
  | FlexV (m,sp) ->
    (match lookup_meta m with
     | Unsolved -> FlexV (m,sp)
     | Solved v -> mforce (appSpV v sp))
  | _ -> v
       
(*****************************************************************************)
(*                                  Quoting                                  *)
(*****************************************************************************)

let lvl_to_idx k l = k - l - 1

let rec quote k v =
  match v with
  | FlexV (m,sp) -> quote_sp k (MetaT m) sp
  | RigidV (l,sp) -> quote_sp k (VarT (lvl_to_idx k l)) sp
  | LamV (nm,cl) -> LamT (nm, quote (k+1) (cl $$ RigidV (k,Emp)))
  | PiV (nm,u,cl) -> PiT (nm, quote k u, quote (k+1) (cl $$ RigidV (k,Emp)))
  | TypV -> TypT

and quote_sp k t sp =
  match sp with
  | Emp -> t
  | Ext (sp',u) ->
    AppT (quote_sp k t sp',quote k u)

let nf rho tm =
  quote (length rho) (eval rho tm) 

(*****************************************************************************)
(*                                Unification                                *)
(*****************************************************************************)

let fresh_meta bds =
  let mctx = ! metacontext in
  let m = ! next_meta in
  next_meta := m + 1;
  metacontext := Map.set mctx ~key:m ~data:Unsolved;
  InsMetaT (m,bds)

type perm = (lvl,lvl,Int.comparator_witness) Map.t
                       
type partial_ren = {
  dom : lvl;
  cod : lvl;
  ren : perm;
}

let lift pren = {
  dom = pren.dom + 1;
  cod = pren.cod + 1;
  ren = Map.set pren.ren ~key:pren.cod ~data:pren.dom; 
}

exception Unify_error of string
    
let invert cod sp =
  let rec go = function
    | Emp -> (0, Map.empty (module Int))
    | Ext (sp',u) ->
      let (dom, ren) = go sp' in
      (match mforce u with
       | RigidV (l,Emp) ->
         (match Map.add ren ~key:l ~data:dom  with
          | `Ok ren' -> (dom + 1,ren')
          | `Duplicate -> raise (Unify_error "non-linear pattern"))
       | _ -> raise (Unify_error "meta-var applied to non-variable")) in 
  let (dom,ren) = go sp in
  { dom = dom ; cod = cod ; ren = ren }


(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type ctx = {
  rho : env;
  lvl : lvl;
  types : (name * value) suite;
  bds : bd suite;
}
