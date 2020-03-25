(** 
  * typecheck.ml - typechecking routines
  * 
  **)

open Syntax
open Eval   

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

let tcEval tm =
  let%bind rho = tcEnv in
  return (eval tm rho)
                 
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

let tcReadback d t =
  let%bind k = tcDepth in
  return (rb k (down d t))
  
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
  | (EOType , TypeD) -> return OTypeT

  (* Basic Opetopic Structure *)
  | (EFrm x, TypeD) ->
     let%bind xt = check x OTypeD in
     return (FrmT xt)
  | (ECell (x, f), TypeD) ->
     let%bind (xt, xd) = checkAndEval x OTypeD in 
     let%bind ft = check f (FrmD xd) in
     return (CellT (xt, ft))
  | (ETree (x, f), TypeD) ->
     let%bind (xt, xd) = checkAndEval x OTypeD in 
     let%bind ft = check f (FrmD xd) in
     return (TreeT (xt, ft))
  | (EPos (x, f, s), TypeD) ->
     let%bind (xt, xd) = checkAndEval x OTypeD in
     let%bind (ft, fd) = checkAndEval f (FrmD xd) in
     let%bind st = check s (TreeD (xd, fd)) in
     return (PosT (xt, ft, st))
    
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

  (* Basic Opetopic Structure *)
  | ETyp (x, f, s, p) ->
     let%bind (xt, xd) = checkAndEval x OTypeD in 
     let%bind (ft, fd) = checkAndEval f (FrmD xd) in
     let%bind (st, sd) = checkAndEval s (TreeD (xd, fd)) in
     let%bind pt = check p (PosD (xd, fd, sd)) in
     return (TypT (xt, ft, st, pt), FrmD xd)
  | EInh (x, f, s, p) -> 
     let%bind (xt, xd) = checkAndEval x OTypeD in
     let%bind (ft, fd) = checkAndEval f (FrmD xd) in
     let%bind (st, sd) = checkAndEval s (TreeD (xd, fd)) in
     let%bind pt = check p (PosD (xd, fd, sd)) in
     return (InhT (xt, ft, st, pt), CellD (xd, fd))
     
  (* Type inference failure *)
  | _ -> tcFail (Printf.sprintf "Failed to infer type for expression %s" (printExpr e))

and checkAndEval e d =
  let%bind tm = check e d in
  let%bind dm = tcEval tm in
  return (tm, dm)
       
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

  
