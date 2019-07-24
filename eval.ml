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
  | OTypeD

  | FrmD of dom
  | CellD of dom * dom
  | TreeD of dom * dom 
  | PosD of dom * dom * dom
  | TypD of dom * dom * dom * dom
  | InhD of dom * dom * dom * dom

  | FrmEmptyD
  | FrmExtD of dom * dom * dom

  | MuD of dom * dom * dom * (dom -> dom)
  | EtaD of dom * dom * dom
  | NdD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom)
  | LfD of dom * dom * dom
  | ObD of dom * dom 

  | ObPosD of dom * dom
  | NdHereD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom)
  | NdThereD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * dom * dom
  | MuPosD of dom * dom * dom * (dom -> dom) * dom * dom
  | EtaPosD of dom * dom * dom
             
  | ObPosElimD of dom * dom * (dom -> dom) * dom * dom
  | LfPosElimD of dom * dom * dom * (dom -> dom) * dom
  | NdPosElimD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * (dom -> dom) * dom * (dom -> dom -> dom) * dom
  | EtaPosElimD of dom * dom * dom * (dom -> dom) * dom * dom
  | MuPosFstD of dom * dom * dom * (dom -> dom) * dom
  | MuPosSndD of dom * dom * dom * (dom -> dom) * dom
         
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
  | OTypeD -> OTypeT

  (* Opetopic Basics *)
  | FrmD t -> FrmT (rb k t)
  | CellD (x, f) -> CellT (rb k x , rb k f)
  | TreeD (x, f) -> TreeT (rb k x , rb k f)
  | PosD (x, f, s) -> PosT (rb k x , rb k f, rb k s)
  | TypD (x, f, s, p) -> TypT (rb k x, rb k f, rb k s, rb k p)
  | InhD (x, f, s, p) -> InhT (rb k x, rb k f, rb k s, rb k p)

  (* Frame Constructors *)
  | FrmEmptyD -> FrmEmptyT
  | FrmExtD (f, s, t) -> FrmExtT (rb k f, rb k s, rb k t)

  (* Opetopic Constructors *)                       
  | MuD (x, f, s, kp) -> MuT (rb k x, rb k f, rb k s, rb (k+1) (kp (VarD k)))
  | EtaD (x, f, a) -> EtaT (rb k x, rb k f, rb k a)
  | NdD (x, f, s, t, a, dl, e) -> NdT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)))
  | LfD (x, f, a) -> LfT (rb k x, rb k f, rb k a)
  | ObD (x, a) -> ObT (rb k x, rb k a)

  (* Position Constructors *)
  | ObPosD (x, a) -> ObPosT (rb k x, rb k a)
  | NdHereD (x, f, s, t, a, dl, e) -> NdHereT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)))
  | NdThereD (x, f, s, t, a, dl, e, p, q) -> NdThereT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)), rb k p, rb k q)
  | MuPosD (x, f, s, kp, p, q) -> MuPosT (rb k x, rb k f, rb k s, rb (k+1) (kp (VarD k)), rb k p, rb k q)
  | EtaPosD (x, f, a) -> EtaPosT (rb k x, rb k f, rb k a)

  (* Position Eliminators *)
  | ObPosElimD (x, a, w, c, p) -> ObPosElimT (rb k x, rb k a, rb (k+1) (w (VarD k)), rb k c, rb k p)
  | LfPosElimD (x, f, a, w, p) -> LfPosElimT (rb k x, rb k f, rb k a, rb (k+1) (w (VarD k)), rb k p)
  | NdPosElimD (x, f, s, t, a, dl, e, w, h, th, p) ->
     (* CHECK ME: are the variable indices for "th" in the correct order? *)
     NdPosElimT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)),
                 rb (k+1) (w (VarD k)), rb k h, rb (k+2) (th (VarD (k+1)) (VarD k)), rb k p)
  | EtaPosElimD (x, f, a, w, n, p) -> EtaPosElimT (rb k x, rb k f, rb k a, rb (k+1) (w (VarD k)), rb k n, rb k p)
  | MuPosFstD (x, f, s, kp, p) -> MuPosFstT (rb k x, rb k f, rb k s, rb (k+1) (kp (VarD k)), rb k p)
  | MuPosSndD (x, f, s, kp, p) -> MuPosSndT (rb k x, rb k f, rb k s, rb (k+1) (kp (VarD k)), rb k p)
           
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
  | OTypeT -> OTypeD

  (* Opetopic Basics *)
  | FrmT t -> FrmD (eval t rho)
  | CellT (x, f) -> CellD (eval x rho, eval f rho)
  | TreeT (x, f) -> TreeD (eval x rho, eval f rho)
  | PosT (x, f, s) -> PosD (eval x rho, eval f rho, eval s rho)
  | TypT (x, f, s, p) -> TypD (eval x rho, eval f rho, eval s rho, eval p rho)
  | InhT (x, f, s, p) -> InhD (eval x rho, eval f rho, eval s rho, eval p rho)

  (* Frame Constructors *)
  | FrmEmptyT -> FrmEmptyD
  | FrmExtT (f, s, t) -> FrmExtD (eval f rho, eval s rho, eval t rho)

  (* Opetopic Constructors *)                       
  | MuT (x, f, s, k) ->
     MuD (eval x rho, eval f rho, eval s rho,
          (fun p -> eval k (WithVar ("", p, rho))))
  | EtaT (x, f, a) -> EtaD (eval x rho, eval f rho, eval a rho)
  | NdT (x, f, s, t, a, d, e) ->
     NdD (eval x rho, eval f rho, eval s rho, eval t rho, eval a rho,
          (fun p -> eval d (WithVar ("", p, rho))),
          (fun p -> eval e (WithVar ("", p, rho))))
  | LfT (x, f, a) -> LfD (eval x rho, eval f rho, eval a rho)
  | ObT (x, a) ->  ObD (eval x rho, eval a rho)

  (* Position Constructors *)
  | ObPosT (x, a) -> ObPosD (eval x rho, eval a rho)
  | NdHereT (x, f, s, t, a, d, e) ->
     NdHereD (eval x rho, eval f rho, eval s rho, eval t rho, eval a rho,
              (fun p -> eval d (WithVar ("", p, rho))),
              (fun p -> eval e (WithVar ("", p, rho))))
  | NdThereT (x, f, s, t, a, d, e, p, q) ->
     NdThereD (eval x rho, eval f rho, eval s rho, eval t rho, eval a rho,
               (fun p -> eval d (WithVar ("", p, rho))),
               (fun p -> eval e (WithVar ("", p, rho))),
               eval p rho, eval q rho)
  | MuPosT (x, f, s, k, p, q) ->
     MuPosD (eval x rho, eval f rho, eval s rho,
             (fun p -> eval k (WithVar ("", p, rho))),
             eval p rho, eval q rho)
  | EtaPosT (x, f, a) -> EtaPosD (eval x rho, eval f rho, eval a rho)

  (* Position Eliminators *)
  | ObPosElimT (x, a, w, c, p) ->
     ObPosElimD (eval x rho, eval a rho,
                 (fun p -> eval w (WithVar ("", p, rho))),
                 eval c rho, eval p rho)
  | LfPosElimT (x, f, a, w, p) ->
     LfPosElimD (eval x rho, eval f rho, eval a rho,
                 (fun p -> eval w (WithVar ("", p, rho))),
                 eval p rho)
  | NdPosElimT (x, f, s, t, a, d, e, w, h, th, p) ->
     (* CHECK ME: are the variable indices for "th" in the correct order? *)
     NdPosElimD (eval x rho, eval f rho, eval s rho, eval t rho, eval a rho,
                 (fun p -> eval d (WithVar ("", p, rho))),
                 (fun p -> eval e (WithVar ("", p, rho))),
                 (fun p -> eval w (WithVar ("", p, rho))),
                 eval h rho,
                 (fun p q -> eval th (WithVar ("", q, WithVar ("", p, rho)))),
                 eval p rho)
  | EtaPosElimT (x, f, a, w, n, p) ->
     EtaPosElimD (eval x rho, eval f rho, eval a rho,
                  (fun p -> eval w (WithVar ("", p, rho))),
                  eval n rho, eval p rho)
  | MuPosFstT (x, f, s, k, p) -> 
     MuPosFstD (eval x rho, eval f rho, eval s rho,
                (fun p -> eval k (WithVar ("", p, rho))),
                eval p rho)
  | MuPosSndT (x, f, s, k, p) -> 
     MuPosSndD (eval x rho, eval f rho, eval s rho,
                (fun p -> eval k (WithVar ("", p, rho))),
                eval p rho)
           
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
   
