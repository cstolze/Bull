(* TO FIX *)
(* Change the syntax of terms so it's more Coq-like *)
(* Possible extension: do pretty-printing stuff whose types are Format.formatter -> t -> unit, so we can mess with the toplevel ocaml pretty-printer *)

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

let typecst_to_string id t = id ^ " : " ^ (kind_to_string (bruijn_to_kind t)) ^ "\n"
let cst_to_string id t = "Constant " ^ id ^ " : " ^ (family_to_string (bruijn_to_family t)) ^ "\n"
let def_to_string id t = let (a,b) = t in
			 id ^ " = " ^ (delta_to_string (bruijn_to_delta a)) ^ " : " ^ (family_to_string (bruijn_to_family b)) ^ "\n"
