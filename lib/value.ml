(*****************************************************************************)
(*                                                                           *)
(*                                   Values                                  *)
(*                                                                           *)
(*****************************************************************************)

open Fmt
open Syntax
open Suite
open Expr

open Opetopes.Idt
open Opetopes.Complex
       
(*****************************************************************************)
(*                              Type Definitions                             *)
(*****************************************************************************)

type value =

  | RigidV of lvl * spine
  | ExpV of lvl * spine 
  | TopV of qname * spine * value

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
  | ReflSp of spine * name* name cmplx 

let varV k = RigidV (k,EmpSp)
let expV k = ExpV (k,EmpSp) 

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
    pf ppf "%a" (pp_spine pp_qname nm) sp
      
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
  | ReflSp (sp',_,pi) ->
    let open Opetopes.Idt.IdtConv in
    pf ppf "[ @[%a@] @[<v>%@ %a@] ]"
      (pp_spine pp_a a) sp' (pp_suite ~sep:(any "@;| ")
       (Fmt.box (pp_tr_expr Fmt.string))) (of_cmplx pi)


(*****************************************************************************)
(*                                Eliminators                                *)
(*****************************************************************************)

let rec app_val t u =
  match t with
  | RigidV (l,sp) -> RigidV (l,AppSp(sp,u))
  | ExpV (l,sp) -> ExpV (l,AppSp(sp,u))
  | TopV (nm,sp,tv) -> TopV (nm,AppSp(sp,u), app_val tv u)
  | LamV (_,cl) -> cl u
  | _ -> raise (Internal_error (Fmt.str "malformed application: %a" pp_value t))

let (<@) = app_val 

let rec fst_val t =
  match t with
  | RigidV (l,sp) -> RigidV (l, FstSp sp)
  | ExpV (l,sp) -> ExpV (l, FstSp sp) 
  | TopV (nm,sp,tv) -> TopV (nm, FstSp sp, fst_val tv)
  | PairV (u,_) -> u
  | _ -> raise (Internal_error (Fmt.str "malformed first proj: %a" pp_value t))

let rec snd_val t =
  match t with
  | RigidV (l,sp) -> RigidV (l, SndSp sp)
  | ExpV (l,sp) -> ExpV (l, SndSp sp) 
  | TopV (nm,sp,tv) -> TopV (nm, SndSp sp, snd_val tv)
  | PairV (_,v) -> v
  | _ -> raise (Internal_error (Fmt.str "malformed second proj: %a" pp_value t))


(* Application to lambdas and pi's *)
           
let rec app_args f args =
  match args with
  | [] -> f
  | v::vs -> app_args (app_val f v) vs 

let app_pi t u =
  match t with
  | PiV (_,_,b) -> b u
  | _ -> raise (Internal_error (Fmt.str "malformed pi app: %a" pp_value u))

let rec app_pi_args t us =
  match us with
  | [] -> t
  | u::us' ->
    app_pi_args (app_pi t u) us' 

(*****************************************************************************)
(*                           Opetopic Utilities                              *)
(*****************************************************************************)

type 'a cmplx_opt =
  | Obj of 'a
  | Arr of 'a * 'a * 'a
  | Cell of 'a cmplx * 'a nst * 'a

let get_cmplx_opt pi =
  match pi with
  | Base (Lf a) -> Obj a
  | Adjoin (Base (Nd (t, Nd (Lf s, Lf ()))), Lf a) ->
    Arr (s,t,a)
  | Adjoin (Adjoin (t,n), Lf a) ->
    Cell (t,n,a) 
  | _ -> failwith "complex match error"


(* convert a complex of cells in the universe to a complex of fibrations by projecting
   out the fibration in appropriate dimensions *)
let ucells_to_fib ucs =
  let dim = dim_cmplx ucs in 
  map_cmplx_with_addr ucs
    ~f:(fun v (cd,_) ->
        if (cd = dim) then v
        else fst_val v)

let appc v vc = app_args v (labels vc)

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

let pair a b =
  ValMonad.return (PairV (a,b))
    
let val_of (m : value valm) : value =
  m (fun v -> v) 

let prod (u : value) (v : value) =
  SigV ("",u,fun _ -> v)

(* Take the non-dependent product of a list of type values *)
let rec list_prod tys =
  match tys with
  | [] -> failwith "empty product"
  | ty :: [] -> ty
  | ty :: tys' -> 
    SigV ("",ty,fun _ -> list_prod tys')

(*****************************************************************************)
(*                            Opetopic Combinators                           *)
(*****************************************************************************)

(* Abstract over all the positions in a given complex and pass
   the abstracted values in complex form to the function b. *)
let rec lam_cmplx (nm : name) (a : name cmplx) (b : value cmplx -> value) : value =

  let rec do_lams nl cm =
    match nl with
    | [] -> b cm
    | (cnm,addr)::addrs ->
      LamV (nm ^ cnm, fun v -> 
          do_lams addrs (replace_at cm (0,addr) v))

  in match a with
  | Base n ->
    let n' = map_nst_with_addr n
        ~f:(fun cnm addr -> (cnm,addr)) in
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    do_lams (nodes_nst n') (Base nv)
  | Adjoin (t,n) ->
    let n' = map_nst_with_addr n
        ~f:(fun cnm addr -> (cnm, addr)) in 
    let nv = map_nst n ~f:(fun _ -> TypV) in 
    lam_cmplx nm t (fun vc -> do_lams (nodes_nst n') (Adjoin (vc,nv)))


(* Abstract a list of types, putting the abstracted 
   value at the appropriate address in the provided complex *)
let rec do_pis nl cm b =
  match nl with
  | [] -> b cm
  | (nm,addr,typ)::ns ->
    PiV (nm, typ, fun v ->
        do_pis ns (replace_at cm (0,addr) v) b)

(* Given a "complex dependent type", extract the space 
   of sections of it with respect to the complex indexed 
   fibration b *)
let rec pi_cmplx (nm : name) (cnms : name cmplx)
    (a : value cmplx) (b : value cmplx -> value) : value =
  
  match (a,cnms) with
  | (Base n , Base nms) ->

    let n' = match_nst_with_addr n nms
        ~f:(fun typ cnm addr -> (nm ^ cnm,addr,typ)) in 
    do_pis (nodes_nst n') a b

  | (Adjoin (t,n), Adjoin (tnms,nnms)) ->

    pi_cmplx nm tnms t (fun vc ->

        let n' = match_nst_with_addr n nnms
            ~f:(fun fib cnm addr ->
                let f = face_at (Adjoin (vc,n)) (0,addr) in
                let f_tl = tail_of f in
                let typ = app_args fib (labels f_tl) in 
                (nm ^ cnm,addr,typ)) in

        do_pis (nodes_nst n') (Adjoin (vc,n)) b

      )

  | _ -> raise (Internal_error "length mismatch in pi_cmplx")

(* b takes just the frame, leaving out the top cell ... *)
let pi_kan (nm : name) (cnms : name cmplx) 
    (addr : addr) (a : value cmplx) (b : value cmplx -> value) : value =
  
  match (a,cnms) with
  | (Base _ , _) -> failwith "Base in Kan abstraction"
  | (Adjoin (Base n , _) , Adjoin (Base nms , _)) ->

    let n' = match_nst_with_addr n nms
        ~f:(fun typ cnm addr -> (nm ^ cnm,addr,typ)) in 
    do_pis (nodes_nst_except n' addr) (Base n) b

  | (Adjoin (Adjoin (t,n),_) , Adjoin (Adjoin (tnms,nnms),_)) ->

    pi_cmplx nm tnms t (fun vc ->

        let n' = match_nst_with_addr n nnms
            ~f:(fun fib cnm addr ->
                let f = face_at (Adjoin (vc,n)) (0,addr) in
                let f_tl = tail_of f in
                let typ = app_args fib (labels f_tl) in 
                (nm ^ cnm,addr,typ)) in

        do_pis (nodes_nst_except n' addr) (Adjoin (vc,n)) b

      )

  | _ -> failwith "uneven complex in pi_kan"


let pi_pd (nm : name)
    (atnms : name cmplx) (at : value cmplx)
    (ahnms : name nst) (ah : value nst)
    (b : value cmplx * value nst -> value) : value = 
  let open ValSyntax in val_of (

    (* let frm = Adjoin (at,ah) in  *)
    let* vc = pi_cmplx nm atnms at in

    let ah' = match_nst_with_addr ah ahnms
        ~f:(fun fib cnm addr ->
            let f = face_at (Adjoin (vc,ah)) (0,addr) in
            let typ = appc fib (tail_of f) in
            (nm ^ cnm, addr, typ)
          ) in 
    
    ret (do_pis (nodes_nst_except ah' []) (Adjoin (vc,ah))
           (fun vc' -> b (tail_of vc',head_of vc')))

  )

(* value monad smart constructors *)
let lamc (nm : name) (a : name cmplx) : value cmplx valm =
  lam_cmplx nm a 

let pic (nm : name) (cnms : name cmplx) (a : value cmplx) : value cmplx valm =
  pi_cmplx nm cnms a 

let pic_kan (nm : name) (cnms : name cmplx)
    (addr : addr) (a : value cmplx) : value cmplx valm =
  pi_kan nm cnms addr a 
