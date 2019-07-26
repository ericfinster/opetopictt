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

  | FrmEmptyD  (* Ummm, do we need the type here ...? *)
  | FrmExtD of dom * dom * dom

  | MuD of dom * dom * dom * (dom -> dom)
  | EtaD of dom * dom * dom
  | GammaD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom)
  | NdD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom)
  | LfD of dom * dom * dom
  | ObD of dom * dom 

  | ObPosD of dom * dom
  | NdHereD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom)
  | NdThereD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * dom * dom
  | MuPosD of dom * dom * dom * (dom -> dom) * dom * dom
  | EtaPosD of dom * dom * dom
  | GammaInlD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * dom 
  | GammaInrD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * dom * dom
             
  | ObPosElimD of dom * dom * (dom -> dom) * dom * dom
  | LfPosElimD of dom * dom * dom * (dom -> dom) * dom
  | NdPosElimD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * (dom -> dom) * dom * (dom -> dom -> dom) * dom
  | EtaPosElimD of dom * dom * dom * (dom -> dom) * dom * dom
  | MuPosFstD of dom * dom * dom * (dom -> dom) * dom
  | MuPosSndD of dom * dom * dom * (dom -> dom) * dom
  | GammaPosElimD of dom * dom * dom * dom * dom * (dom -> dom) * (dom -> dom) * (dom -> dom) * (dom -> dom) * (dom -> dom -> dom) * dom
         
  | VarD of int
  | PiD of dom * (dom -> dom)
  | LamD of (dom -> dom)
  | AppD of dom * dom
  | SigD of dom * (dom -> dom)
  | PairD of dom * dom
  | FstD of dom
  | SndD of dom

(**
 * Type Theoretic Normalization
 *)
          
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
 * Opetopic Normalization
 **)
                                                
let rec typD x' f' s' p' =
  match s' with
  | ObD (_, _) -> FrmEmptyD
  | LfD (x, f, a) -> LfPosElimD (x, f, a, (fun _ -> FrmD x), p')
  | NdD (x, f, s, t, a, d, e) ->
     let w _ = FrmD x in
     let hr = FrmExtD (f, s, t) in
     let th p q = typD x (FrmExtD (typD x f s p, d p, inhD x f s p)) (e p) q in
     ndPosElimD x f s t a d e w hr th p'
  | EtaD (_, f, _) -> f
  | MuD (x, f, s, k) ->
     let pfst = muPosFstD x f s k p' in
     let psnd = muPosSndD x f s k p' in
     typD x (typD x f s pfst) (k pfst) psnd
  | GammaD (x, f, s, t, r, phi, psi) ->
     let w _ = FrmD x in
     let inl p = typD x (FrmExtD (f, s, t)) r p in
     let inr p q = typD x (FrmExtD (typD x f s p, phi p, inhD x f s p)) (psi p) q in
     gammaPosElimD x f s t r phi psi w inl inr p'
  | _ -> TypD (x', f', s', p')

and inhD x' f' s' p' =
  match s' with
  | ObD (_, a) -> a
  | LfD (x, f, a) ->
     let w p = CellD (x, typD x (FrmExtD (f, etaD x f a, a)) s' p) in
     LfPosElimD (x, f, a, w, p')
  | NdD (x, f, sigma, tau, alpha, delta, epsilon) ->
     let w p = CellD (x, typD x (FrmExtD (f, muD x f sigma delta, tau)) s' p) in
     let th p q = inhD x (FrmExtD (typD x f sigma p, delta p, inhD x f sigma p)) (epsilon p) q in
     ndPosElimD x f sigma tau alpha delta epsilon w alpha th p'

  (* Right, more cases here ... *)
     
  | _ -> InhD (x', f', s', p')

                
and etaD x' _ _ = x'
(* and etaD x' f' a' = x' *)
  (* match f with *)
  (* | FrmEmptyD -> ObD (x', a') *)
  (* | FrmExtD (f , s , t) -> *)
  (*    let etaDec p = etaD x f (inhD x f s p)) in *)
  (*    let lfDec p = LfD (x, typD x f s p, inhD(x, f', s, p)) in *)
  (*    NdD (x, f, s, t, a, etaDec, lfDec) *)
  (* | _ -> EtaD (x', f', a') *)

(* and etaPosD x f a = *)
(*   match f with *)
(*   | FrmEmptyD -> ObPosD (x , a) *)
(*   | FrmExtD (f' , s , t) -> *)
(*      let etaDec p = etaD x f' (inhD (x, f', s, p)) in *)
(*      let lfDec p = LfD (x, typD (x, f', s, p), inhD (x, f', s, p)) in *)
(*      NdHereD (x, f', s, t, a, etaDec, lfDec) *)
(*   | _ -> EtaPosD (x, f, a) *)

and muD x' _ _ _ = x'
(* and muD x' f' s' k' = x' *)
(*   match s with *)
(*   | ObD (x, a) -> k (ObPosD (x, a)) *)
(*   | LfD (x, f, a) -> LfD (x, f, a) *)
(*   | NdD (x, f, s, t, a, d, e) -> *)
(*      let w = k (NdHereD (x, f, s, t, a, d, e)) in *)
(*      let k' p q = k (NdThereD (x, f, s, t, a, d, e, p, q)) in  *)
(*      let psi p = muD x (typD (x, f, s, p)) (e p) (k' p) in *)
(*      gammaD x f s t w d psi *)
(*   | _ -> MuD (x, f, s, k) *)
     
(* and gammaD x f s t r phi psi = *)
(*   match r with *)
(*   | LfD (x, f, a) -> psi (etaPosD x f a) *)
(*   | NdD (x, f, sigma, tau, alpha, del, eps) -> *)
(*      let phi' p q = phi (muPosD x f sigma del p q) in *)
(*      let psi' p q = psi (muPosD x f sigma del p q) in *)
(*      let del' p = muD x f (del p) (psi' p) in *)
(*      let eps' p = gammaD x f (del p) (inhD (x , f, sigma, p)) (eps p) (phi' p) (psi' p) in  *)
(*      NdD (x, f, sigma, tau, alpha, del', eps') *)
(*   | _ -> GammaD (x, f, s, t, r, phi, psi) *)
       
and muPosD x' _ _ _ _ _ = x'
and muPosFstD x' _ _ _ _ = x'
and muPosSndD x' _ _ _ _ = x'
and ndPosElimD x' _ _ _ _ _ _ _ _ _ _ = x'
and gammaPosElimD x' _ _ _ _ _ _ _ _ _ _ = x'

                                                
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
  | MuD (x, f, s, kp) ->
     (* As an example, we implement the right unit law here,
      * We'll have to think a bit more about whether or not
      * this technique is valid.  *)
     let krb = rb (k+1) (kp (VarD k)) in
     (match krb with
      | EtaT (_, _, _) -> rb k s
      | _ -> MuT (rb k x, rb k f, rb k s, krb))
  | EtaD (x, f, a) -> EtaT (rb k x, rb k f, rb k a)
  | GammaD (x, f, s, t, r, phi, psi) -> GammaT (rb k x, rb k f, rb k s, rb k t, rb k r, rb (k+1) (phi (VarD k)), rb (k+1) (psi (VarD k)))
  | NdD (x, f, s, t, a, dl, e) -> NdT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)))
  | LfD (x, f, a) -> LfT (rb k x, rb k f, rb k a)
  | ObD (x, a) -> ObT (rb k x, rb k a)
                
  (* Position Constructors *)
  | ObPosD (x, a) -> ObPosT (rb k x, rb k a)
  | NdHereD (x, f, s, t, a, dl, e) -> NdHereT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)))
  | NdThereD (x, f, s, t, a, dl, e, p, q) -> NdThereT (rb k x, rb k f, rb k s, rb k t, rb k a, rb (k+1) (dl (VarD k)), rb (k+1) (e (VarD k)), rb k p, rb k q)
  | MuPosD (x, f, s, kp, p, q) -> MuPosT (rb k x, rb k f, rb k s, rb (k+1) (kp (VarD k)), rb k p, rb k q)
  | EtaPosD (x, f, a) -> EtaPosT (rb k x, rb k f, rb k a)
  | GammaInlD (x, f, s, t, r, phi, psi, p) -> GammaInlT (rb k x, rb k f, rb k s, rb k t, rb k r, rb (k+1) (phi (VarD k)), rb (k+1) (psi (VarD k)), rb k p)
  | GammaInrD (x, f, s, t, r, phi, psi, p, q) -> GammaInrT (rb k x, rb k f, rb k s, rb k t, rb k r, rb (k+1) (phi (VarD k)), rb (k+1) (psi (VarD k)), rb k p, rb k q)
                       
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
  | GammaPosElimD (x, f, s, t, r, phi, psi, w, il, ir, p) ->
     (* CHECK ME: are the variable indices for "ir" in the correct order? *)
     GammaPosElimT (rb k x, rb k f, rb k s, rb k t, rb k r, rb (k+1) (phi (VarD k)), rb (k+1) (psi (VarD k)),
                    rb (k+1) (w (VarD k)), rb (k+1) (il (VarD k)) , rb (k+2) (ir (VarD (k+1)) (VarD k)), rb k p)
                                
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
  | GammaT (x, f, s, t, r, phi, psi) ->
     GammaD (eval x rho, eval f rho, eval s rho, eval t rho, eval r rho,
             (fun p -> eval phi (WithVar ("", p, rho))),
             (fun p -> eval psi (WithVar ("", p, rho))))
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
  | GammaInlT (x, f, s, t, r, phi, psi, p) ->
     GammaInlD (eval x rho, eval f rho, eval s rho, eval t rho, eval r rho,
                   (fun p -> eval phi (WithVar ("", p, rho))),
                   (fun p -> eval psi (WithVar ("", p, rho))),
                   eval p rho)
  | GammaInrT (x, f, s, t, r, phi, psi, p, q) ->
     GammaInrD (eval x rho, eval f rho, eval s rho, eval t rho, eval r rho,
                   (fun p -> eval phi (WithVar ("", p, rho))),
                   (fun p -> eval psi (WithVar ("", p, rho))),
                   eval p rho, eval q rho)
                       
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
  | GammaPosElimT (x, f, s, t, r, phi, psi, w, il, ir, p) ->
     (* CHECK ME: are the variable indices for "ir" in the correct order? *)
     GammaPosElimD (eval x rho, eval f rho, eval s rho, eval t rho, eval r rho,
                 (fun p -> eval phi (WithVar ("", p, rho))),
                 (fun p -> eval psi (WithVar ("", p, rho))),
                 (fun p -> eval w (WithVar ("", p, rho))),
                 (fun p -> eval il (WithVar ("", p, rho))),
                 (fun p q -> eval ir (WithVar ("", q, WithVar ("", p, rho)))),
                 eval p rho)
    
  | PiT (a , p) -> PiD (eval a rho , fun x -> eval p (WithVar ("" , x , rho)))
  | LamT a -> LamD (fun x -> eval a (WithVar ("" , x , rho)))
  | AppT (a , b) -> appD (eval a rho) (eval b rho)
  | SigT (a , p) -> SigD (eval a rho , fun x -> eval p (WithVar ("" , x , rho)))
  | PairT (a , b) -> PairD (eval a rho, eval b rho)
  | FstT a -> fstD (eval a rho)
  | SndT a -> sndD (eval a rho)
  | BVarT k -> getEnvIdx k rho
  | FVarT id -> match getEnv id rho with
                | WasVar d -> d
                | WasDef (tm' , _ , rho') -> eval tm' rho'
                | NoResult ->
                   raise (Empty_environment
                            (Printf.sprintf "Environment lookup failed for %s" id))
   
