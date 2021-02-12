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

let varV k = RigidV (k,Emp)
    
let rec quote k v =
  match v with
  | FlexV (m,sp) -> quote_sp k (MetaT m) sp
  | RigidV (l,sp) -> quote_sp k (VarT (lvl_to_idx k l)) sp
  | LamV (nm,cl) -> LamT (nm, quote (k+1) (cl $$ varV k))
  | PiV (nm,u,cl) -> PiT (nm, quote k u, quote (k+1) (cl $$ varV k))
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
       | _ -> raise (Unify_error "meta-var applied to non-bound-variable")) in 
  let (dom,ren) = go sp in
  { dom = dom ; cod = cod ; ren = ren }

let rename m pren v =

  let rec goSp pr v = function
    | Emp -> v
    | Ext (sp,u) -> AppT (goSp pr v sp, go pr u)

  and go pr v = match mforce v with
    | FlexV (m',sp) ->
      if (m <> m') then
        goSp pr (MetaT m') sp
      else raise (Unify_error "failed occurs check")
    | RigidV (i,sp) ->
      (match Map.find pr.ren i with
       | Some l -> goSp pr (VarT (lvl_to_idx pr.dom l)) sp 
       | None -> raise (Unify_error "escaped variable"))
    | LamV (nm,a) -> LamT (nm, go (lift pr) (a $$ varV pr.cod))
    | PiV (nm,a,b) -> PiT (nm, go pr a, go (lift pr) (b $$ varV pr.cod))
    | TypV -> TypT

  in go pren v

let lams l t =
  let rec go k t =
    if (k = l) then t else
      let nm = Printf.sprintf "x%d" (k+1) in
      LamT (nm, go (k+1) t)
  in go 0 t

let solve k m sp v =
  let pr = invert k sp in
  let v' = rename m pr v in
  let sol = eval Emp (lams pr.dom v') in
  let mctx = ! metacontext in
  metacontext := Map.update mctx m ~f:(fun _ -> Solved sol)

let rec unify l t u =
  match (mforce t , mforce u) with
  | (LamV (_,a) , LamV (_,a')) -> unify (l+1) (a $$ varV l) (a' $$ varV l)
  | (t' , LamV(_,a')) -> unify (l+1) (appV t' (varV l)) (a' $$ varV l)
  | (LamV (_,a) , t') -> unify (l+1) (a $$ varV l) (appV t' (varV l))
  | (TypV , TypV) -> ()
  | (PiV (_,a,b) , PiV (_,a',b')) ->
    unify l a a';
    unify (l+1) (b $$ varV l) (b' $$ varV l)
  | (RigidV (i,sp) , RigidV (i',sp')) ->
    if (i = i') then unifySp l sp sp' else
      raise (Unify_error "rigid mismatch")
  | (FlexV (m,sp) , FlexV (m',sp')) ->
    if (m = m') then unifySp l sp sp' else
      raise (Unify_error "flex mismatch")
  | (t' , FlexV (m,sp)) -> solve l m sp t'
  | (FlexV (m,sp) , t') -> solve l m sp t'
  | _ -> raise (Unify_error "could not unify")

and unifySp l sp sp' =
  match (sp,sp') with
  | (Emp,Emp) -> ()
  | (Ext (s,u),Ext(s',u')) ->
    unifySp l s s';
    unify l u u'
  | _ -> raise (Unify_error "spine mismatch")

(*****************************************************************************)
(*                                  Contexts                                 *)
(*****************************************************************************)

type ctx = {
  rho : env;
  lvl : lvl;
  types : (name * value) suite;
  bds : bd suite;
}

let bind gma nm ty =
  let l = gma.lvl in 
  { rho = Ext (gma.rho, varV l);
    lvl = l+1;
    types = Ext (gma.types,(nm,ty));
    bds = Ext (gma.bds,Bound) }

let define gma nm tm ty =
  { rho = Ext (gma.rho,tm);
    lvl = gma.lvl+1;
    types = Ext (gma.types,(nm,ty));
    bds = Ext (gma.bds,Defined) }

exception Typing_error of string

let rec check gma expr typ =
  match (expr, mforce typ) with
  
  | (LamE (nm,e) , PiV (_,a,b)) ->
    check (bind gma nm a) e (b $$ varV (gma.lvl))

  | (HoleE , _) -> fresh_meta (gma.bds)

  | (e, expected) ->
    let (e',inferred) = infer gma e in
    try unify (gma.lvl) expected inferred ; e'
    with Unify_error _ -> raise (Typing_error ("unification failed"))

and infer gma expr =
  match expr with

  | VarE nm -> (VarT gma.lvl, assoc nm gma.types )

  | LamE (nm,e) ->
    let a = eval (gma.rho) (fresh_meta gma.bds) in
    let (e', t) = infer (bind gma nm a) e in
    (LamT (nm,e') , PiV (nm,a,Closure (gma.rho,quote (gma.lvl + 1) t)))

  | AppE (u,v) ->
    let (u',ut) = infer gma u in
    let (a,b) = match mforce ut with
      | PiV (_,a,b) -> (a,b)
      | _ ->
        let a = eval (gma.rho) (fresh_meta gma.bds) in
        let b = Closure (gma.rho , fresh_meta (bind gma "x" a).bds) in
        unify gma.lvl ut (PiV ("x",a,b)); 
        (a,b)
    in let v' = check gma v a in 
    (AppT (u', v') , b $$ eval gma.rho u')

  | PiE (nm,a,b) ->
    let a' = check gma a TypV in
    let b' = check (bind gma nm (eval gma.rho a')) b TypV in
    (PiT (nm,a',b') , TypV)

  | TypE -> (TypT , TypV)

  | HoleE ->
    let a = eval (gma.rho) (fresh_meta gma.bds) in
    let t = fresh_meta gma.bds in
    (t , a)



