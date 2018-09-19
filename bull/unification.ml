open Utils
open Bruijn
open Reduction
open Subtyping
open Printer

let meta_add_sort (n,meta) = (n, (n+1, IsSort n :: meta))

let meta_add (n,meta) ctx t = (n, (n+1, DefMeta (ctx, n, t) :: meta))

let get_meta (_,meta) n =
  let rec foo = function
    | [] -> assert false
    | IsSort m :: l ->
       if m = n then IsSort n else foo l
    | DefMeta (l1, m, t) :: l -> if m = n then DefMeta (l1, m, t) else
                                   foo l
    | SubstSort (m,s) :: l -> if m = n then SubstSort (m,s) else foo l
    | Subst (l1,m,t1,t2) :: l -> if m = n then Subst (l1, m, t1, t2)
                                 else foo l
    | SubstEssence (l1, m, t1, t2) :: l
      -> if m = n then SubstEssence (l1, m, t1, t2) else foo l
  in
  foo meta

let is_instanced meta n =
  match get_meta meta n with
  | SubstSort _ | Subst _ -> true
  | _ -> false

let instantiate meta env n l =
  

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
  let rec unify_delta meta env t1 t2 =
    match (t1,t2) with
    | Sort(l,t1), Sort(_,t2) -> if t1 = t2 then meta
                                else Error "Sort"
    | Prod(l,id,t1,t2), Prod(_,_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let t2 = foo meta ({delta=t1;essence=nothing} :: env) t2 t2' in
       meta
    | Abs(l,id,t1,t2), Abs(_,_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta ({delta=t1;essence=nothing} :: env) t2 t2' in
       meta
    | Inter(l,t1,t2), Inter(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | Union(l,t1,t2), Union(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SPair(l,t1,t2), SPair(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SPrLeft(l,t1), SPrLeft(_,t1') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SPrRight(l,t1), SPrRight(_,t1') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SInLeft(l,t1,t2), SInLeft(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | SInRight(l,t1,t2), SInRight(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
    | Coercion(l,t1,t2), Coercion(_,t1',t2') ->
       let meta = foo meta env t1 t1' in
       let meta = foo meta env t2 t2' in
       meta
  | Var(l,x), Var(_,y) -> if x = y then meta else Error "Var"
  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6),
    SMatch (_, t1', t2', _, t3', t4', _, t5', t6') ->
     let meta = foo meta env t1 t1' in
     let meta = foo meta env t2 t2' in
     let meta = foo meta env t3 t3' in
     let meta = foo meta env t4 t4' in
     let meta = foo meta env t5 t5' in
     let meta = foo meta env t6 t6' in
     meta
  | Const (_,_), _ | _, Const (_,_)
    | Underscore _, _ | _, Underscore _
    | Let (_,_,_,_,_), _ | _, Let (_,_,_,_,_) -> assert false
  | App(l,t1,l2), App(_,t1',l2') ->
     if List.length l2 = List.length l2' then
       try
         let meta = foo env t1 t1' in
         let rec bar meta l l' =
           match l, l' with
           | x :: l, y :: l' -> let meta = foo meta env x y
                                in bar meta l l'
           | [], [] -> meta
           | _ -> assert false
         in bar meta l2 l2'
       with
  | Meta (l, n), t | t, Meta (l,n) ->
     begin
       (* TODO: find if meta has already been instantiated
        if yes, unify instantiate(meta) and t. Other case: pattern *)
     end
