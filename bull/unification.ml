open Utils
open Bruijn
open Reduction
open Subtyping
open Printer

exception Error of string



(* TODO : 2 functions:
- unification_delta
- unification_essence

functions takes one term as input (not a fullterm)
 *)


let unification meta env ctx t1 t2 =
  let norm t =
    let t = {delta=apply_all_substitution meta t.delta;
             essence=apply_all_substition meta t.essence} in
    {delta=strongly_normalize env t.delta;
     essence=strongly_normalize env t.essence}
  in
  let t1 = norm t1 in
  let t2 = norm t2 in
  let rec unify_delta env t1 t2 =
    match (t1,t2) with
    | Sort(l,t1), Sort(_,t2) -> if t1 = t2 then meta
                                else Error "Sort"
    | Prod(l,id,t1,t2), Prod(_,_,t1',t2') ->
       let meta = foo env t1 t1' in
       let t2 = foo ({delta=t1;essence=nothing} :: env) t2 t2' in
       meta
    | Abs(l,id,t1,t2), Abs(_,_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo ({delta=t1;essence=nothing} :: env) t2 t2' in
       meta
    | Inter(l,t1,t2), Inter(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | Union(l,t1,t2), Union(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | SPair(l,t1,t2), SPair(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | SPrLeft(l,t1), SPrLeft(_,t1') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | SPrRight(l,t1), SPrRight(_,t1') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | SInLeft(l,t1,t2), SInLeft(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | SInRight(l,t1,t2), SInRight(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
    | Coercion(l,t1,t2), Coercion(_,t1',t2') ->
       let meta = foo env t1 t1' in
       let meta = foo env t2 t2' in
       meta
  | Var(l,x), Var(_,y) -> if x = y then meta else Error "Var"
  | Const (_,_), _ | _, Const (_,_)
    | Underscore _, _ | _, Underscore _
    | Let (_,_,_,_,_), _ | _, Let (_,_,_,_,_) -> assert false
  | Meta of location * int * (term list) (* index and substitution *)
  | App of location * term * term (* t1 t2 *)
  | SMatch of location * term * term * string * term * term * string * term * term (* match t1 return t2 with s1 : t3 => t4 , s2 : t5 => t6 end *)
