type kind =
  | Type
  | KProd of string * family * kind
   and
     family =
     | SFc of family * family
     | SProd of string * family * family
     | SLambda of string * family * family
     | SApp of family * delta
     | SAnd of family * family
     | SOr of family * family
     | SAtom of string
     | SOmega
     | SAnything
   and
     delta =
     | DVar of string
     | DStar
     | DLambda of string * family * delta
     | DApp of delta * delta
     | DAnd of delta * delta
     | DProjL of delta
     | DProjR of delta
     | DOr of string * family * delta * string * family * delta * delta
     | DInjL of delta
     | DInjR of delta

type bkind =
  | BType
  | BKProd of string * bfamily * bkind
   and
     bfamily =
     | BSFc of bfamily * bfamily
     | BSProd of string * bfamily * bfamily
     | BSLambda of string * bfamily * bfamily
     | BSApp of bfamily * bdelta
     | BSAnd of bfamily * bfamily
     | BSOr of bfamily * bfamily
     | BSAtom of string
     | BSOmega
     | BSAnything
   and
     bdelta =
     | BDVar of (string * bool * int) (* id * is_bound? * bruijn index *)
     | BDStar
     | BDLambda of string * bfamily * bdelta
     | BDApp of bdelta * bdelta
     | BDAnd of bdelta * bdelta
     | BDProjL of bdelta
     | BDProjR of bdelta
     | BDOr of string * bfamily * bdelta * string * bfamily * bdelta * bdelta
     | BDInjL of bdelta
     | BDInjR of bdelta

type sentence =
  | Quit
  | Load of string
  | Proof of string * family
  | Typecst of string * kind
  | Cst of string * family
  | Typecheck of string * delta * family
  | Typeinfer of string * delta
  | Print of string
  | Print_all
  | Compute of string
  | Help
  | Error

type proofrule =
  | PError
  | PQuit
  | PAbort
  | PBacktrack
  | PExact of delta (* ; __ ; *)
  | PAbst1 (* dependent case *)
  | PAbst2 of string (* non-dependent case (the user has to input a variable name *)
  | PSConj
  | PSDisj of string * bfamily * bfamily
  | PProjL of bfamily
  | PProjR of bfamily
  | PInjL
  | PInjR

type path = Left | Middle | Right

      (*
type proofrule =
  (* syntax directed *)
  | POmega
  | PVar of string
  | PIntro of string
  | PDependentIntro
  | PAnd
  | PInjL
  | PInjR
  (* non syntax directed *)
  | PElim of bfamily
  | PDependentElim of bfamily * bdelta
  | PProjL of bfamily
  | PProjR of bfamily
  | POr of string * bfamily * bfamily
  (* essence *)
  (* | PPop : too complicated *)
  | PBreak
  (* control flow *)
  | PBacktrack
  | PAbort
  | PSwitch
       *)

(*
type proofnode =
    PN of (int * int list * ((string * bfamily) list) * bfamily * proofrule option * int)
(* parent ptr, children ptr list, gamma, rule, essence ptr *)

type essencerule = EApp | EAbstr | EVar of int
type essencenode =
    EN of (int list * essencerule option * int list)
(* children ptr list, rule, proof ptr list *)

type proofgraph = PG of ((int * proofnode) list * (int * essencenode) list * int * int list)
(* derivation tree, essence tree, goal, remaining goals *)
       *)

type signature =
    Sig of ((string * bkind) list) * ((string * bfamily) list) * ((string * (bdelta * bfamily)) list) (* type constants, constants, definitions *)

type lambda_bruijn =
  | BVar of string * bool * int (* name * is it bound? * bruijn index *)
  | BLambda of lambda_bruijn
  | BApp of lambda_bruijn * lambda_bruijn

(* to_string functions *)

let rec kind_to_string k =
  match k with
  | Type -> "Type"
  | KProd (id, f, k) -> "!" ^ id ^ " : " ^ (family_to_string f) ^ ". " ^ (kind_to_string k)
and family_to_string f =
  let aux f =
    match f with
    | SAtom x -> x
    | SOmega -> "$"
    | _ -> "(" ^ (family_to_string f) ^ ")"
  in
  let aux2 delta =
    match delta with
    | DVar i -> i
    | DStar -> "*"
    | DAnd (_, _) -> delta_to_string delta
    | DOr (_, _, _, _, _, _, _) -> delta_to_string delta
    | _ -> "(" ^ (delta_to_string delta) ^ ")"
  in
  match f with
  | SFc (f1, f2) -> (aux f1) ^ " -> " ^ (aux f2)
  | SProd (id, f1, f2) -> "!" ^ id ^ " : " ^ (family_to_string f1) ^ ". " ^ (aux f2)
  | SLambda (id, f1, f2) -> "\\" ^ id ^ " : " ^ (family_to_string f1) ^ ". " ^ (aux f2)
  | SApp (f1, d) -> (aux f1) ^ " " ^ (aux2 d)
  | SAnd (f1, f2) -> (aux f1) ^ " & " ^ (aux f2)
  | SOr (f1, f2) -> (aux f1) ^ " | " ^ (aux f2)
  | SAtom id -> id
  | SOmega -> "$"
  | SAnything -> "?"
and delta_to_string d =
  let aux delta =
    match delta with
    | DVar i -> i
    | DStar -> "*"
    | DAnd (_, _) -> delta_to_string delta
    | DOr (_, _, _, _, _, _, _) -> delta_to_string delta
    | _ -> "(" ^ (delta_to_string delta) ^ ")"
  in
  match d with
  | DVar i -> i
  | DStar -> "*"
  | DLambda (i, s, d) ->
     let t = aux d in
     "\\" ^ i ^ " : " ^ (family_to_string s) ^ ". " ^ t
  | DApp (d1, d2) ->
     let t1 = aux d1
     in let t2 = aux d2 in
	t1 ^ " " ^ t2
  | DAnd (d1, d2) ->
     let t1 = aux d1
     in let t2 = aux d2 in
	"< " ^ t1 ^ " & " ^ t2 ^ " >"
  | DProjL d ->
     let t = aux d in
     "proj_l " ^ t
  | DProjR d ->
     let t = aux d in
     "proj_r " ^ t
  | DOr (x1, f1, d1, x2, f2, d2, d3) ->
     let t1 = delta_to_string (DLambda (x1,f1,d1))
     in let t2 = delta_to_string (DLambda (x2,f2,d2))
	in let t3 = delta_to_string d3 in
	   "< " ^ t1 ^  " | " ^ t2 ^ " # " ^ t3 ^ " >"
  | DInjL d ->
     let t = aux d in
     "inj_l " ^ t
  | DInjR d ->
     let t = aux d in
     "inj_r " ^ t

(* conversion functions bruijn <-> normal *)

let (family_to_bruijn, delta_to_bruijn, delta_gamma) =
  let rec find_env x l =
    match l with
    | [] -> false
    | y :: l' -> if x = y then true else find_env x l'
  in
  let rec get_env x l n =
    match l with
    | [] -> failwith "use find_env"
    | y :: l' -> if x = y then n else get_env x l' (n+1)
  in
  let rec family_to_bruijn' f env =
    match f with
    | SFc (f1, f2) -> BSFc (family_to_bruijn' f1 env, family_to_bruijn' f2 ("" :: env))
    | SProd (id, f1, f2) -> BSProd (id, family_to_bruijn' f1 env, family_to_bruijn' f2 (id::env))
    | SLambda (id, f1, f2) -> BSLambda (id, family_to_bruijn' f1 env, family_to_bruijn' f2 (id::env))
    | SApp (f1, d2) -> BSApp (family_to_bruijn' f1 env, delta_to_bruijn' d2 env)
    | SAnd (f1, f2) -> BSAnd (family_to_bruijn' f1 env, family_to_bruijn' f2 env)
    | SOr (f1, f2) -> BSOr (family_to_bruijn' f1 env, family_to_bruijn' f2 env)
    | SAtom id -> BSAtom id
    | SOmega -> BSOmega
    | SAnything -> BSAnything
    and
      delta_to_bruijn' d env =
      match d with
      | DVar id -> if find_env id env then BDVar (id, true, get_env id env 0) (* local variables shadow global ones *)
		   else BDVar(id, false, 0)
      | DStar -> BDStar
      | DLambda (id, f1, d') -> BDLambda (id, family_to_bruijn' f1 env, delta_to_bruijn' d' (id::env))
      | DApp (d1, d2) -> BDApp (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DAnd (d1, d2) -> BDAnd (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DProjL d' -> BDProjL (delta_to_bruijn' d' env)
      | DProjR d' -> BDProjR (delta_to_bruijn' d' env)
      | DOr (id', f', d', id'', f'', d'', d''') -> BDOr (id', family_to_bruijn' f' env, delta_to_bruijn' d' (id'::env), id'', family_to_bruijn' f'' env, delta_to_bruijn' d'' (id''::env), delta_to_bruijn' d''' env)
      | DInjL d' -> BDInjL (delta_to_bruijn' d' env)
      | DInjR d' -> BDInjR (delta_to_bruijn' d' env)
  in ((fun f -> family_to_bruijn' f []), (fun d -> delta_to_bruijn' d []), (fun d -> fun g -> delta_to_bruijn' d g))

let rec kind_to_bruijn k =
  match k with
  | Type -> BType
  | KProd (id, f, k') -> BKProd (id, family_to_bruijn f, kind_to_bruijn k')

let rec alpha_conv id b n check replace =
  match n with
  | None -> if check id b 0 then (id, b) else alpha_conv id b (Some 0) check replace
  | Some n' ->
     let id' = id ^ (string_of_int n') in
     if check id' b 0 then (id', replace b id' 0) else alpha_conv id b (Some (n'+1)) check replace

let rec f_check id f n =
  match f with
  | BSFc (f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSProd (id', f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSLambda (id', f1, f2) -> (f_check id f1 n) && (f_check id f2 (n+1))
  | BSApp (f1, d2) -> (f_check id f1 n) && (d_check id d2 n)
  | BSAnd (f1, f2) -> (f_check id f1 n) && (f_check id f2 n)
  | BSOr (f1, f2) -> (f_check id f1 n) && (f_check id f2 n)
  | BSAtom id' -> true
  | BSOmega -> true
  | BSAnything -> true
  and
    d_check id d n =
    match d with
    | BDVar (id', false, n') -> not (id = id')
    | BDVar (id', true, n') -> if (id = id') then (n >= n') else true (* no free variable should be called id *)
    | BDStar -> true
    | BDLambda (id', f1, d') -> (f_check id f1 n) && (d_check id d' (n+1))
    | BDApp (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDAnd (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDProjL d' -> d_check id d' n
    | BDProjR d' -> d_check id d' n
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       (f_check id f' n) &&
	 (d_check id d' (n+1)) &&
	   (f_check id f'' n) &&
	     (d_check id d'' (n+1)) &&
	       (d_check id d''' n)
    | BDInjL d' -> d_check id d' n
    | BDInjR d' -> d_check id d' n

let rec f_replace f id n =
  match f with
  | BSFc (f1, f2) -> BSFc (f_replace f1 id n, f_replace f2 id (n+1))
  | BSProd (id', f1, f2) -> BSProd (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSLambda (id', f1, f2) -> BSLambda (id', f_replace f1 id n, f_replace f2 id (n+1))
  | BSApp (f1, d2) -> BSApp (f_replace f1 id n, d_replace d2 id n)
  | BSAnd (f1, f2) -> BSAnd (f_replace f1 id n, f_replace f2 id n)
  | BSOr (f1, f2) -> BSOr (f_replace f1 id n, f_replace f2 id n)
  | BSAtom id' -> f
  | BSOmega -> f
  | BSAnything -> f
  and
    d_replace d id n =
    match d with
    | BDVar (id', false, n') -> d
    | BDVar (id', true, n') -> if (n = n') then BDVar (id, true, n') else d
    | BDStar -> d
    | BDLambda (id', f1, d') -> BDLambda (id', f_replace f1 id n, d_replace d' id (n+1))
    | BDApp (d1, d2) -> BDApp (d_replace d1 id n, d_replace d2 id n)
    | BDAnd (d1, d2) -> BDAnd (d_replace d1 id n, d_replace d2 id n)
    | BDProjL d' -> BDProjL (d_replace d' id n)
    | BDProjR d' -> BDProjR (d_replace d' id n)
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       BDOr (id',
	     f_replace f' id n,
	     d_replace d' id (n+1),
	     id'',
	     f_replace f'' id n,
	     d_replace d'' id (n+1),
	     d_replace d''' id n)
    | BDInjL d' -> BDInjL (d_replace d' id n)
    | BDInjR d' -> BDInjR (d_replace d' id n)

let rec bruijn_to_family f =
  match f with
  | BSFc (f1, f2) -> SFc (bruijn_to_family f1, bruijn_to_family f2)
  | BSProd (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SProd (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSLambda (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SLambda (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSApp (f1, d2) -> SApp (bruijn_to_family f1, bruijn_to_delta d2)
  | BSAnd (f1, f2) -> SAnd (bruijn_to_family f1, bruijn_to_family f2)
  | BSOr (f1, f2) -> SOr (bruijn_to_family f1, bruijn_to_family f2)
  | BSAtom id -> SAtom id
  | BSOmega -> SOmega
  | BSAnything -> SAnything
  and
    bruijn_to_delta d =
    match d with
    | BDVar (id, b, n) -> DVar id
    | BDStar -> DStar
    | BDLambda (id, f1, d') -> let (id', d'') = alpha_conv id d' None d_check d_replace in DLambda (id', bruijn_to_family f1, bruijn_to_delta d'')
    | BDApp (d1, d2) -> DApp (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDAnd (d1, d2) -> DAnd (bruijn_to_delta d1, bruijn_to_delta d2)
    | BDProjL d' -> DProjL (bruijn_to_delta d')
    | BDProjR d' -> DProjR (bruijn_to_delta d')
    | BDOr (id', f', d', id'', f'', d'', d''') ->
       let (id'1, d'1) = alpha_conv id' d' None d_check d_replace in
       let (id''1, d''1) = alpha_conv id'' d'' None d_check d_replace in
       DOr (id'1, bruijn_to_family f', bruijn_to_delta d'1, id''1, bruijn_to_family f'', bruijn_to_delta d''1, bruijn_to_delta d''')
    | BDInjL d' -> DInjL (bruijn_to_delta d')
    | BDInjR d' -> DInjR (bruijn_to_delta d')

let rec bruijn_to_kind k =
  let rec k_check id k n =
    match k with
    | BType -> true
    | BKProd (id', f, k') -> (f_check id f n) && (k_check id k' (n+1))
  in
  let rec k_replace k id n =
    match k with
    | BType -> k
    | BKProd (id', f, k') -> BKProd (id', f_replace f id n, k_replace k' id (n+1))
  in
  match k with
  | BType -> Type
  | BKProd (id, f, k') -> let (id', k'') = alpha_conv id k' None k_check k_replace in KProd (id', bruijn_to_family f, bruijn_to_kind k'')

(* auxiliary functions for using signature *)

let rec find id l =
  match l with
  | [] -> false
  | (x, y) :: l' -> if x = id then true else find id l'

let rec get id l =
  match l with
  | [] -> failwith "the programmer should ensure this does not happen (use the find function)"
  | (x, y) :: l' -> if x = id then y else get id l'

let find_type id ctx = let Sig (a,b,c) = ctx in find id a
let get_type id ctx = let Sig (a,b,c) = ctx in get id a
let find_cst id ctx = let Sig (a,b,c) = ctx in find id b
let get_cst id ctx = let Sig (a,b,c) = ctx in get id b (* we suppose id has already been found *)
let find_def id ctx = let Sig (a,b,c) = ctx in find id c
let get_def id ctx = let Sig (a,b,c) = ctx in get id c (* we suppose id has already been found *)
let find_all id ctx = find_type id ctx || find_cst id ctx || find_def id ctx

let typecst_to_string id t = id ^ " : " ^ (kind_to_string (bruijn_to_kind t)) ^ "\n"
let cst_to_string id t = "Constant " ^ id ^ " : " ^ (family_to_string (bruijn_to_family t)) ^ "\n"
let def_to_string id t = let (a,b) = t in
			 id ^ " = " ^ (delta_to_string (bruijn_to_delta a)) ^ " : " ^ (family_to_string (bruijn_to_family b)) ^ "\n"

																  (* todo : inference, proof *)
