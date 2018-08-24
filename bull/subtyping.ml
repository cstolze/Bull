open Utils
open Reduction

(* Note: for now, these functions suppose that there is no type meta-variables in the terms *)
(* TODO: design an unification algorithm for types modulo subtyping *)

(* rewriting functions for disjunctive and conjunctive normal forms *)
let rec anf a =
  let rec distr f a b =
    match (a,b) with
    | (Union(l,a1,a2),_) -> Inter(l, distr f a1 b, distr f a2 b)
    | (_, Inter(l,b1,b2)) -> Inter(l, distr f a b1, distr f a b2)
    | _ -> f a b
  in
  match a with
  | Prod(l,id,a,b) -> distr (fun a b -> Prod(l,id,a,b)) (danf a) (canf b)
  | _ -> a
and canf a =
  let rec distr a b =
    match (a,b) with
    | (Inter(l,a1,a2),_) -> Inter(l, distr a1 b, distr a2 b)
    | (_,Inter(l,b1,b2)) -> Inter(l, distr a b1, distr a b2)
    | _ -> Union(dummy_loc,a,b)
  in
  match a with
  | Inter(l,a,b) -> Inter(l, canf a, canf b)
  | Union(l,a,b) -> distr (canf a) (canf b)
  | _ -> anf a
and danf a =
  let rec distr a b =
    match (a,b) with
    | (Union(l,a1,a2),_) -> Union(l, distr a1 b, distr a2 b)
    | (_,Union(l,b1,b2)) -> Union(l, distr a b1, distr a b2)
    | _ -> Inter(dummy_loc, a,b)
  in
  match a with
  | Inter(l,a,b) -> distr (danf a) (danf b)
  | Union(l,a,b) -> Union(l, danf a, danf b)
  | _ -> anf a

(* tell whether a <= b *)
let is_subtype gamma a b =
  let a = danf @@ strongly_normalize gamma a in
  let b = canf @@ strongly_normalize gamma b in
  let rec foo gamma a b =
  match (a, b) with
  | (Union(_,a1,a2),_) -> foo gamma a1 b && foo gamma a2 b
  | (_,Inter(_,b1,b2)) -> foo gamma a b1 && foo gamma a b2
  | (Inter(_,a1,a2),_) -> foo gamma a1 b || foo gamma a2 b
  | (_,Union(_,b1,b2)) -> foo gamma a b1 || foo gamma a b2
  | (Prod(_,_,a1,a2),Prod(_,_,b1,b2))
    -> foo gamma b1 a1 && foo (DefAxiom("",dummy_term)::gamma) a2 b2
  | _ -> true (* is_equal gamma a b *) (* TODO: FIXME *)
  in foo gamma a b
