open Utils
open Reduction

(* Note: for now, these functions suppose that there is no type meta-variables in the terms *)
(* TODO: design an unification algorithm for types modulo subtyping *)

(* rewriting function simplifying the use of omega *)
let rec omega_simpl a =
  match a with
  | Prod(id, a1, a2) ->
     (match (omega_simpl a1, omega_simpl a2) with
     | (a, Omega) -> Omega
     | (a,b) -> Prod(id,a,b))
  | Subset(id, a1, a2) -> Subset(id,omega_simpl a1, omega_simpl a2)
  | Inter(a1, a2) ->
     (match (omega_simpl a1, omega_simpl a2) with
     | (a, Omega) | (Omega, a) -> a
     | (a,b) -> Inter(a,b))
  | Union(a1, a2) ->
     (match (omega_simpl a1, omega_simpl a2) with
     | (a, Omega) | (Omega, a) -> Omega
     | (a,b) -> Union(a,b))
  | _ -> a

(* rewriting functions for disjunctive and conjunctive normal forms *)
let rec anf a =
  let rec distr f a b =
    match (a,b) with
    | (Union(a1,a2),_) -> Inter(distr f a1 b, distr f a2 b)
    | (_, Inter(b1,b2)) -> Inter(distr f a b1, distr f a b2)
    | _ -> f a b
  in
  match a with
  | Prod(id,a,b) -> distr (fun a b -> Prod(id,a,b)) (danf a) (canf b)
  | Subset(id,a,b) -> distr (fun a b -> Subset(id,a,b)) (danf a) (canf b)
  | _ -> a
and canf a =
  let rec distr a b =
    match (a,b) with
    | (Inter(a1,a2),_) -> Inter(distr a1 b, distr a2 b)
    | (_,Inter(b1,b2)) -> Inter(distr a b1, distr a b2)
    | _ -> Union(a,b)
  in
  match a with
  | Inter(a,b) -> Inter(canf a, canf b)
  | Union(a,b) -> distr (canf a) (canf b)
  | _ -> anf a
and danf a =
  let rec distr a b =
    match (a,b) with
    | (Union(a1,a2),_) -> Union(distr a1 b, distr a2 b)
    | (_,Union(b1,b2)) -> Union(distr a b1, distr a b2)
    | _ -> Inter(a,b)
  in
  match a with
  | Inter(a,b) -> distr (danf a) (danf b)
  | Union(a,b) -> Union(danf a, danf b)
  | _ -> anf a

(* tell whether a <= b *)
let is_subtype gamma a b =
  let a = danf @@ omega_simpl @@ strongly_normalize gamma a in
  let b = canf @@ omega_simpl @@ strongly_normalize gamma b in
  let rec foo gamma a b =
  match (a, b) with
  | (_,Omega) -> true
  | (Union(a1,a2),_) -> foo gamma a1 b && foo gamma a2 b
  | (_,Inter(b1,b2)) -> foo gamma a b1 && foo gamma a b2
  | (Inter(a1,a2),_) -> foo gamma a1 b || foo gamma a2 b
  | (_,Union(b1,b2)) -> foo gamma a b1 || foo gamma a b2
  | (Prod(_,a1,a2),Prod(_,b1,b2)) | (Subset(_,a1,a2),Prod(_,b1,b2))
  | (Subset(_,a1,a2),Subset(_,b1,b2)) -> foo gamma b1 a1 && foo (DefAxiom(Nothing,Nothing)::gamma) a2 b2
  | _ -> is_equal gamma a b
  in foo gamma a b
