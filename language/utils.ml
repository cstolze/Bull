type kind =
  | Type

type family =
  | SFc of family * family
  | SAnd of family * family
  | SOr of family * family
  | SAtom of string
  | SAnything

type delta =
  | DVar of string
  | DLambda of string * family * delta
  | DApp of delta * delta
  | DAnd of delta * delta
  | DProjL of delta
  | DProjR of delta
  | DOr of string * family * delta * string * family * delta * delta
  | DInjL of delta
  | DInjR of delta

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

let rec family_to_string f =
  let aux f =
    match f with
    | SAtom x -> x
    | _ -> "(" ^ (family_to_string f) ^ ")"
  in
  match f with
  | SFc (f1, f2) -> (aux f1) ^ " -> " ^ (aux f2)
  | SAnd (f1, f2) -> (aux f1) ^ " & " ^ (aux f2)
  | SOr (f1, f2) -> (aux f1) ^ " | " ^ (aux f2)
  | SAtom id -> id
  | SAnything -> "?"

let rec delta_to_string d =
  let aux delta =
    match delta with
    | DVar i -> i
    | DAnd (_, _) -> delta_to_string delta
    | DOr (_, _, _, _, _, _, _) -> delta_to_string delta
    | _ -> "(" ^ (delta_to_string delta) ^ ")"
  in
  match d with
  | DVar i -> i
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
  | SAnything -> "Error: type unknown.\n" (* should not happen *)

											 (* todo : proof *)
