(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Syntax
open Suite
open Expr

open Opetopes.Complex
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  | RigidV of lvl * spine
  | ExpV of lvl * spine 
  | TopV of name * spine * value

  (* Pi Types *)
  | LamV of name * (value -> value) 
  | PiV of name * value * (value -> value)

  (* Sigma Types *) 
  | PairV of value * value
  | SigV of name * value * (value -> value)

  (* The Universe *)
  | TypV

and spine =
  | EmpSp
  | AppSp of spine * value
  | FstSp of spine
  | SndSp of spine
  | ReflSp of spine * string cmplx 

let varV k = RigidV (k,EmpSp)
let expV k = ExpV (k,EmpSp) 

(* Take the non-dependent product of a list of type values *)
let rec prod tys =
  match tys with
  | [] -> failwith "empty product"
  | ty :: [] -> ty
  | ty :: tys' -> 
    SigV ("",ty,fun _ -> prod tys')


(*****************************************************************************)
(*                      A Monad for Constructing Values                      *)
(*****************************************************************************)

type 'a valm = ('a -> value) -> value 
  
module ValBasic =
struct

  type 'a t = 'a valm 

  let return a k = k a
  let bind m ~f:f k =
    m (fun a -> f a k) 

  let map m ~f:f k =
    m (fun a -> k (f a))

  let map = `Custom map 
  
end

module ValMonad = Base.Monad.Make(ValBasic) 

module ValSyntax =
struct
  let (let*) m f = ValMonad.bind m ~f 
  let ret = ValMonad.return
end 
  
let lam (nm : name) : value valm =
  fun k -> LamV (nm,k) 

let pi (nm : name) (av : value) : value valm =
  fun k -> PiV (nm,av,k) 
  
let sigma (nm : name) (av : value) : value valm =
  fun k -> SigV (nm,av,k) 
    
let val_of (m : value valm) : value =
  m (fun v -> v) 
    

(*****************************************************************************)
(*                              Pretty Printing                              *)
(*****************************************************************************)

let rec pp_value ppf v =
  match v with
  
  | RigidV (i,sp) ->
    pp_spine Fmt.int i ppf sp 
  | ExpV (i,sp) ->
    let ppe ppf = pf ppf "exp%d" in 
    pp_spine ppe i ppf sp 
  | TopV (nm,sp,_) ->
    let pp_nm ppf' n = pf ppf' "%s" n in 
    pf ppf "%a" (pp_spine pp_nm nm) sp
      
  | LamV (nm,_) ->
    pf ppf "\\%s.<closure>" nm 
  | PiV (nm,a,_) ->
    pf ppf "(%s : %a) -> <closure>" nm
      pp_value a
      
  | PairV (u,v) ->
    pf ppf "%a , %a" pp_value u pp_value v
  | SigV (nm,a,_) ->
    pf ppf "(%s : %a) \u{d7} <closure>" nm
      pp_value a

  | TypV -> pf ppf "U"
    
and pp_spine : 'a. 'a Fmt.t -> 'a -> spine Fmt.t =
  fun pp_a a ppf sp -> 
  match sp with
  | EmpSp ->
    pf ppf "%a" pp_a a
  | AppSp (sp',v) ->
    pf ppf "%a %a" (pp_spine pp_a a) sp' pp_value v
  | FstSp sp' ->
    pf ppf "fst @[%a@]" (pp_spine pp_a a) sp' 
  | SndSp sp' ->
    pf ppf "snd @[%a@]" (pp_spine pp_a a) sp'
  | ReflSp (sp',pi) ->
    let open Opetopes.Idt.IdtConv in
    pf ppf "[ @[%a@] @[<v>%@ %a@] ]"
      (pp_spine pp_a a) sp' (pp_suite ~sep:(any "@;| ")
       (Fmt.box (pp_tr_expr Fmt.string))) (of_cmplx pi)
