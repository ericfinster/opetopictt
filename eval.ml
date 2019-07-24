(** 
  * eval.ml - normalization by evaluation
  * 
  **)

open Syntax

(** 
 * The Semantic Domain 
 **)

type dom =
  | TypeD
  | VarD of int
  | PiD of dom * (dom -> dom)
  | LamD of (dom -> dom)
  | AppD of dom * dom
  | SigD of dom * (dom -> dom)
  | PairD of dom * dom
  | FstD of dom
  | SndD of dom
          
let fstD el =
  match el with
  | PairD (f , _) -> f
  | _ -> FstD el

let sndD el =
  match el with
  | PairD (_ , s) -> s
  | _ -> SndD el

let appD a b =
  match a with
  | LamD f -> f b
  | _ -> AppD (a , b)

(**
 * Reification and reflection
 **)

let rec up d e =
  match d with
  | PiD (a , p) -> LamD (fun x -> up (p x) (AppD (e , down a x)))
  | SigD (a , p) -> let x = up a (FstD e)
                    in PairD (x , up (p x) (SndD e))
  | _ -> e
       
and down d e =
  match d with
  | TypeD -> downT e
  | PiD (a , p) -> LamD (fun x -> let y = up a x
                                  in down (p y) (appD e y))
  | SigD (a , p) -> let y = fstD e
                    in PairD (down a y , down (p y) (sndD e))
  | _ -> e

and downT d =
  match d with
  | PiD (a , p) -> PiD (downT a , fun x -> downT (p (up a x)))
  | SigD (a , p) -> SigD (downT a , fun x -> downT (p (up a x)))
  | _ -> d 

(**
 * Readback
 **)

let rec rb k d =
  match d with
  | TypeD -> TypeT
  | VarD i -> BVarT (k - i - 1)
  | PiD (a , p) -> PiT (rb k a , rb (k+1) (p (VarD k)))
  | LamD f -> LamT (rb (k+1) (f (VarD k)))
  | AppD (a , b) -> AppT (rb k a , rb k b)
  | SigD (a , p) -> SigT (rb k a , rb (k+1) (p (VarD k)))
  | PairD (a , b) -> PairT (rb k a , rb k b)
  | FstD a -> FstT (rb k a)
  | SndD a -> SndT (rb k a)

(**
 * Environment
 **)

type env =
  | EmptyEnv
  | WithVar of string * dom * env
  | WithDef of string * term * term * env

type env_result =
  | NoResult
  | WasVar of dom
  | WasDef of term * term * env
   
exception Empty_environment of string

let rec printEnv rho =
  match rho with
  | EmptyEnv -> ""
  | WithVar (id , _, rho') ->
     Printf.sprintf "%s (Var: %s)" (printEnv rho') id 
  | WithDef (id , _ , _ , rho') ->
     Printf.sprintf "%s (Def: %s)" (printEnv rho') id 
                             
let rec getEnv ident rho =
  match rho with
  | EmptyEnv -> NoResult
  | WithVar (id , d , rho') ->
     if id = ident then WasVar d else
       getEnv ident rho'
  | WithDef (id , tm , ty , rho') ->
     if id = ident then WasDef (tm , ty , rho') else
       getEnv ident rho'

let rec getEnvDef ident rho =
  match rho with
  | EmptyEnv -> 
     raise (Empty_environment
              (Printf.sprintf "No definition named %s" ident))
  | WithVar (_ , _ , rho') ->
     getEnvDef ident rho'
  | WithDef (id , tm , ty , rho') ->
     if id = ident then (tm , ty) else
       getEnvDef ident rho'
  
let rec getEnvIdx k rho =
  match rho with
  | EmptyEnv ->
     raise (Empty_environment
              (Printf.sprintf "No index %d" k))
  | WithVar (_ , d , rho') -> 
      if k = 0 then d else getEnvIdx (k-1) rho'
  | WithDef (_ , _ , _ , rho') -> getEnvIdx k rho'
      
let rec envLen rho =
  match rho with
  | EmptyEnv -> 0
  | WithVar (_ , _ , rho') -> envLen rho' + 1
  | WithDef (_ , _ , _ , rho') -> envLen rho'

(**
 * Evaluation
 **)

let rec eval tm rho =
  match tm with
  | TypeT -> TypeD
  | PiT (a , p) -> PiD (eval a rho , fun x -> eval p (WithVar ("" , x , rho)))
  | LamT a -> LamD (fun x -> eval a (WithVar ("" , x , rho)))
  | AppT (a , b) -> AppD (eval a rho , eval b rho)
  | SigT (a , p) -> SigD (eval a rho , fun x -> eval p (WithVar ("" , x , rho)))
  | PairT (a , b) -> PairD (eval a rho, eval b rho)
  | FstT a -> FstD (eval a rho)
  | SndT a -> SndD (eval a rho)
  | BVarT k -> getEnvIdx k rho
  | FVarT id -> match getEnv id rho with
                | WasVar d -> d
                | WasDef (tm' , _ , rho') -> eval tm' rho'
                | NoResult ->
                   raise (Empty_environment
                            (Printf.sprintf "Environment lookup failed for %s" id))
   
