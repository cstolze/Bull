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
  | PVar
  | PAbort
  | PIntro
  | PElim of family
  | PSconj
  | PProjL of family
  | PProjR of family
  | PInjL
  | PInjR
  | PSdisj of family * family
  | PBacktrack
  | PChangerule
  | PError

type signature =
    Sig of ((string * kind) list) * ((string * family) list) * ((string * (delta * family)) list) (* type constants, constants, definitions *)

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
  match f with
  | SFc (f1, f2) -> (aux f1) ^ " -> " ^ (aux f2)
  | SProd (id, f1, f2) -> "!" ^ id ^ " : " ^ (family_to_string f1) ^ ". " ^ (aux f2)
  | SLambda (id, f1, f2) -> "\\" ^ id ^ " : " ^ (family_to_string f1) ^ ". " ^ (aux f2)
  | SApp (f1, d) -> (aux f1) ^ " " ^ (delta_to_string d)
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

let (family_to_bruijn, delta_to_bruijn) =
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
    | SFc (f1, f2) -> BSFc (family_to_bruijn f1 env, family_to_bruijn f2 env)
    | SProd (id, f1, f2) -> BSProd (id, family_to_bruijn f1 env, family_to_bruijn f2 (id::env))
    | SLambda (id, f1, f2) -> BSLambda (id, family_to_bruijn f1 env, family_to_bruijn f2 (id::env))
    | SApp (f1, f2) -> BSApp (family_to_bruijn f1 env, family_to_bruijn f2 env)
    | SAnd (f1, f2) -> BSAnd (family_to_bruijn f1 env, family_to_bruijn f2 env)
    | SOr (f1, f2) -> BSOr (family_to_bruijn f1 env, family_to_bruijn f2 env)
    | SAtom id -> BSAtom id
    | SOmega -> BSOmega
    | SAnything -> BSAnything
    and
      delta_to_bruijn' d env =
      | DVar id -> if find_env x env then BDVar (x, true, get_env x env 0) (* local variables shadow global ones *)
		   else BDVar(x, false, 0)
      | DStar -> BStar
      | DLambda (id, f1, d') -> BDLambda (x, family_to_bruijn' f1, delta_to_bruijn' d' (id::env))
      | DApp (d1, d2) -> BDApp (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DAnd (d1, d2) -> BDAnd (delta_to_bruijn' d1 env, delta_to_bruijn' d2 env)
      | DProjL d' -> BDProjL (delta_to_bruijn' d' env)
      | DProjR d' -> BDProjR (delta_to_bruijn' d' env)
      | DOr (id', f', d', id'', f'', d'', d''') -> BDOr (id', family_to_bruijn' f' env, delta_to_bruijn' d' (id'::env), id'', family_to_bruijn' f'' env, delta_to_bruijn' d'' (id''::env), delta_to_bruijn' d''' env)
      | DInjL d' -> BDInjL (delta_to_bruijn' d' env)
      | DInjR d' -> BDInjR (delta_to_bruijn' d' env)
  in (fun f -> family_to_bruijn' f [], fun d -> delta_to_bruijn' d [])

let rec kind_to_bruijn k =
  match k with
  | Type -> BType
  | KProd (id, f, k') -> BKProd (id, family_to_bruijn f, kind_to_bruijn k')

let rec alpha_conv id b n check replace =
  match n with
  | None -> if check id b 0 then (id, b) else alpha_conv id b (Some 0) check replace
  | Some n' ->
     let id' = id ^ (string_of_int n') in
     if check id' b 0 then (id', replace b id id' 0) else alpha_conv id b (Some (n'+1)) check replace

let rec f_check id f n =
  | BSFc (f1, f2) -> BSFc (fcheck id f1 n, fcheck id f2 n)
  | BSProd (id, f1, f2) -> 
  | BSLambda (id, f1, f2) -> 
  | BSApp (f1, d2) -> BSApp (fcheck id f1 n, dcheck id d2 n)
  | BSAnd (f1, f2) -> BSAnd (fcheck id f1 n, fcheck id f2 n)
  | BSOr (f1, f2) -> BSOr (fcheck id f1 n, fcheck id f2 n)
  | BSAtom id -> true
  | BSOmega -> true
  | BSAnything -> true
  and
    d_check id d n =
    | BDVar (id', false, n') -> not (id = id')
    | BDVar (id', true, n') -> if (id = id') then (n >= n') else true
    | BDStar -> true
    | BDLambda (id', f1, d') -> 
    | BDApp (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDAnd (d1, d2) -> (d_check id d1 n) && (d_check id d2 n)
    | BDProjL d' -> d_check id d' n
    | BDProjR d' -> d_check id d' n
    | BDOr (id', f', d', id'', f'', d'', d''') -> 
    | BDInjL d' -> d_check id d' n
    | BDInjR d' -> d_check id d' n

let rec bruijn_to_family f =
  match f with
  | BSFc (f1, f2) -> SFc (bruijn_to_family f1, bruijn_to_family f2)
  | BSProd (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SProd (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSLambda (id, f1, f2) -> let (id', f2') = alpha_conv id f2 None f_check f_replace in SLambda (id', bruijn_to_family f1, bruijn_to_family f2')
  | BSApp (f1, f2) -> SApp (bruijn_to_family f1, bruijn_to_family f2)
  | BSAnd (f1, f2) -> SAnd (bruijn_to_family f1, bruijn_to_family f2)
  | BSOr (f1, f2) -> SOr (bruijn_to_family f1, bruijn_to_family f2)
  | BSAtom id -> SAtom
  | BSOmega -> SOmega
  | BSAnything -> SAnything
  and
    bruijn_to_delta d =
  | BDVar (id, b, n) -> DVar id
  | BDStar -> DStar
  | BDLambda (id, f1, d') -> let (id', d'') = alpha_conv id d' None d_check d_replace in SLambda (id', bruijn_to_family f1, bruijn_to_delta d'')
  | BDApp (d1, d2) -> DApp (bruijn_to_delta d1, bruijn_to_delta d2)
  | BDAnd (d1, d2) -> DAnd (bruijn_to_delta d1, bruijn_to_delta d2)
  | BDProjL d' -> DProjL (bruijn_to_delta d')
  | BDProjR d' -> DProjR (bruijn_to_delta d')
  | BDOr (id', f', d', id'', f'', d'', d''') -> 
  | BDInjL d' -> DInjL (bruijn_to_delta d')
  | BDInjR d' -> DInjR (bruijn_to_delta d')

let rec bruijn_to_kind k =
  match k with
  | BType -> Type
  | BKProd (id, f, k') -> let (id', k') = alpha_conv id k None k_check k_replace

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


let typecst_to_string id t = id ^ " : " ^ (kind_to_string t) ^ "\n"
let cst_to_string id t = "Constant " ^ id ^ " : " ^ (family_to_string t) ^ "\n"
let def_to_string id t = let (a,b) = t in
			 id ^ " = " ^ delta_to_string a ^ " : " ^ family_to_string b ^ "\n"

let rec is_family_sound f ctx = (* to use when the user declares a constant *)
  match f with
  | SFc (f', f'') -> (is_family_sound f' ctx) ^ (is_family_sound f'' ctx)
  | SAnd (f', f'') -> (is_family_sound f' ctx) ^ (is_family_sound f'' ctx)
  | SOr (f', f'') -> (is_family_sound f' ctx) ^ (is_family_sound f'' ctx)
  | SAtom x -> if find_type x ctx then "" else "Error: the type " ^ x ^ " has not been declared yet.\n"
  | SAnything -> "should not happen"
  | SOmega -> ""

											 (* todo : proof *)
