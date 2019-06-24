(** 
  * typecheck.ml - typechecking routines
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

(**
 * Typechecking Monad
 **)

type 'a tc_err =
  | Fail of string
  | Succeed of 'a

type ctxt = (string * dom) list
type tc_env = env * ctxt
type 'a tc = tc_env -> 'a tc_err
           
module TCMndImpl =
  struct
    type 'a m = 'a tc

    let map : 'a tc -> f:('a -> 'b) -> 'b tc =
      fun m ~f:f rho -> match m rho with
                     | Fail msg -> Fail msg
                     | Succeed v -> Succeed (f v)
      
    let bind : 'a tc -> f:('a -> 'b tc) -> 'b tc =
      fun m ~f:f rho -> match (m rho) with
                     | Fail msg -> Fail msg
                     | Succeed v -> f v rho
                   
    let return : 'a -> 'a tc =
      fun a _ -> Succeed a
      
  end

module TCMnd : Monad.Monad with type 'a m = 'a tc = Monad.Make(TCMndImpl)

open TCMnd

module Let_syntax =
  struct
    let map = map
    let return = return
    let bind = bind
  end

let tcDepth : int tc =
  fun (_ , gma) -> Succeed (List.length gma)

let tcFail : string -> 'a tc =
  fun msg _ -> Fail msg

let tcWithVar : string -> dom -> 'a tc -> 'a tc =
  fun id d m (rho , gma) ->
  m (WithVar (id , up d (VarD (envLen rho)), rho) , (id,d) :: gma)

let tcWithDef : string -> term -> term -> 'a tc -> 'a tc =
  fun id ty tm m (rho , gma) ->
  m (WithDef (id , ty , tm , rho) , gma)
  
let tcEnv : env tc =
  fun (rho , _) -> Succeed rho

let tcCtxt : ctxt tc =
  fun (_ , gma) -> Succeed gma
  
type ctxt_result =
  | NoCtxtResult
  | InCtxt of int * dom

let rec printCtx ctx k =
  match ctx with
  | [] -> ""
  | (id , d)::cs ->
     let t = rb k d in 
     Printf.sprintf "%s (%s : %s)" (printCtx cs k) id (printTerm t) 
        
let rec ctxtLookup ctxt ident =
  match ctxt with
  | [] -> NoCtxtResult
  | ((id , d)::cs) ->
     if id = ident then InCtxt (List.length cs , d) else
       ctxtLookup cs ident

let tcCtxtLookup ident (_ , gma) =
  match ctxtLookup gma ident with
  | NoCtxtResult -> Fail "empty context"
  | InCtxt (k , d) -> Succeed (k , d)
      
let tcExtPi d _ =
  match d with
  | PiD (a , p) -> Succeed (a , p)
  | _ -> Fail "tcExtPi"

let tcExtSig d _ =
  match d with
  | SigD (a , p) -> Succeed (a , p)
  | _ -> Fail "tcExtSig"

let tcEqNf a b e =
  let%bind k = tcDepth in
  let a' = rb k (downT a) in 
  let b' = rb k (downT b) in
  if (a' = b') then return () else
    let msg = Printf.sprintf "Error while typechecking expression %s\n  %s =/= %s\n"
                             (printExpr e) (printTerm a') (printTerm b')
    in tcFail msg

let tcPrintEnv =
  fun (rho , gma) ->
  let () = Printf.printf "Context: %s\n" (printCtx gma (List.length gma)) in 
  let () = Printf.printf "Environment: %s \n" (printEnv rho) in
  Succeed ()
  
     
(**
 * Typechecking rules
 **)

let rec check e d =
  let%bind () = tcPrintEnv in 
  match (e , d) with
    
  (* Type in Type *)
  | (EType , TypeD) -> return TypeT

  (* Pi Formation *)
  | (EPi (id , a , p) , TypeD) ->
     let%bind at = check a TypeD in
     let%bind rho = tcEnv in
     tcWithVar id (eval at rho)
               (let%bind pt = check p TypeD in
                return (PiT (at , pt)))

  (* Pi Introduction *)
  | (ELam (id, e) , PiD (a, p)) ->
     let m = let%bind i = tcDepth in
             let%bind t = check e (p (up a (VarD (i-1)))) in
             return (LamT t)
     in tcWithVar id a m

  (* Sig Formation *)
  | (ESig (id , a , p) , TypeD) ->
     let%bind at = check a TypeD in
     let%bind rho = tcEnv in
     tcWithVar id (eval at rho)
               (let%bind pt = check p TypeD in
                return (SigT (at , pt)))

  (* Sig Introduction *)
  | (EPair (u , v) , SigD (a , p)) ->
     let%bind ut = check u a in
     let%bind rho = tcEnv in
     let%bind vt = check v (p (eval ut rho)) in
     return (PairT (ut , vt))

  (* Conversion *)
  | _ -> let%bind (tm , ty) = checkI e in
         let%bind () = tcEqNf d ty e in
         return tm 
       
and checkI e =
  let%bind () = tcPrintEnv in 
  match e with

  (* Assumption *)
  | EVar id -> 
     let%bind rho = tcEnv in
     (match getEnv id rho with
      | NoResult -> tcFail (Printf.sprintf "Unknown identifier %s" id)
      | WasVar _ ->
         let%bind (k , tyD) = tcCtxtLookup id in
         let%bind i = tcDepth in 
         return (BVarT (i - k - 1) , tyD)
      | WasDef (_ , ty , rho') ->
         return (FVarT id , eval ty rho'))

  (* Pi elimination *)
  | EApp (u , v) ->
     let%bind (ut , tyD) = checkI u in
     let%bind (aD , pD) = tcExtPi tyD in
     let%bind vt = check v aD in
     let%bind rho = tcEnv in
     return (AppT (ut , vt) , pD (eval vt rho))

  (* Sig elimination (fst) *)
  | EFst u ->
     let%bind (ut , tyD) = checkI u in
     let%bind (aD , _) = tcExtSig tyD in
     return (FstT ut , aD)
     
  (* Sig elimination (snd) *)
  | ESnd u ->
     let%bind (ut , tyD) = checkI u in
     let%bind (_ , pD) = tcExtSig tyD in
     let%bind rho = tcEnv in
     return (SndT ut , pD (fstD (eval ut rho)))

  (* Type inference failure *)
  | _ -> tcFail (Printf.sprintf "Failed to infer type for expression %s" (printExpr e))

       
let checkDef ty tm =
  let%bind tyT = check ty TypeD in
  let%bind rho = tcEnv in
  let%bind tmT = check tm (eval tyT rho) in
  return (tyT , tmT)

let rec checkDefs defs =
  match defs with
  | [] -> return ()
  | (Def (id , ty , tm)) :: ds ->
     Printf.printf "Processing definition: %s\n" id;
     let%bind (tyT, tmT) = checkDef ty tm in 
     tcWithDef id tyT tmT (checkDefs ds)

  
