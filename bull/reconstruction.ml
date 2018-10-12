open Utils
open Bruijn
open Reduction
open Subtyping
open Printer
open Unification

(* returns the essence and the type of a term *)

let get_from_meta meta env l n subst =
  match get_meta meta n with
  | IsSort n -> raise (Err "should not happen? 1")
  | SubstSort (n,Type) -> (meta, {delta=Sort(l,Type); essence=Sort(l,Type)}
                           , {delta=Sort(l,Kind); essence=Sort(l,Kind)})
  | SubstSort (n,Kind) -> raise (Err "should not happen? 2")
  | DefMeta (l1,n,t2) | Subst (l1,n,_,t2) | SubstEssence (l1,n,_,t2)
    -> (meta, {delta = Meta(l,n,subst); essence = Meta(l,n,subst)},
        {delta=apply_substitution t2.delta subst;
         essence=apply_substitution t2.essence subst})

let type_of_sort s =
  match s with
  | Type -> Some ({delta=Sort(dummy_loc, Kind); essence=Sort(dummy_loc, Kind)})
  | Kind -> None

(* returns the sort of Pi x : A. B, where A:s1 and b:s2 *)
(* pre-condition: s1 and s2 have to be sorts (or sort meta-vars) *)
let principal_type_system meta env ctx s1 s2 =
  match (s1, s2) with
  | (Sort (_,Type), t) -> (meta, {delta=t;essence=t})
  | (t1, t2) -> let meta = unification meta env t1
                                       {delta=Sort(dummy_loc,Type);
                                        essence=Sort(dummy_loc,Type)}
                in (meta, {delta=t2;essence=t2})

(* same as principal type system, but for A | B and A & B *)
let principal_set_system meta env ctx s1 s2 =
  match (s1, s2) with
  | (Sort (_,Type), Sort(l,Type)) -> (meta, {delta=Sort(l,Type); essence=Sort(l,Type)})
  | (t1, t2) -> let meta = unification meta env t1
                                       {delta=Sort(dummy_loc,Type);
                                        essence=Sort(dummy_loc,Type)}
                in
                let meta = unification meta env t2
                                       {delta=Sort(dummy_loc,Type);
                                        essence=Sort(dummy_loc,Type)}
                in (meta, {delta=Sort(dummy_loc,Type); essence=Sort(dummy_loc,Type)})


(*
4 algorithms:
reconstruct

reconstruct_with_essence

reconstruct_with_type

reconstruct_with_all

These function takes as input:
- a meta-environment
- a local environment
- a full environment
- a term
- eventually an essence and/or a type

These functions return:
- a new meta-environment
- a new fullterm
- a new fulltype

These functions can throw an exception

 *)


(*
  force-type takes is like reconstruct, except that
it forces the returned type to be either Type, Kind, or a meta-variable with
the property is_sort
 *)
(*
  cast takes as input
  - a meta-variable environment
  - a fullterm t
  - a fulltype t1
  - a fulltype t2

and returns
  - a new meta-var env
  - a new fullterm
  - a new fulltype
 *)

(*
  unification function takes as input:
  - a meta-variable environment
  - a fullterm t
  - a fullterm t'

and returns
  - a new meta-var env
 *)

(*
  a meta-variable environment is a list of either
  - a context, a meta-variable identifier, and a type
  - a context, and the constraint is-a-sort(meta-variable identifier)

The meta-variable environment comes with an integer being the maximum meta-var id in the list
(in case we have to add a new id)
 *)
(*
  a substitution is a list of:
  - context, meta-var id, term, type ( \Gamma \vdash id := term : type )
 *)

let rec reconstruct meta env ctx t =
  match t with

  | Sort (l, s) ->
     begin
       match type_of_sort s with
       | Some x -> (meta, {delta=t; essence=t}, x)
       | None -> raise (Err error_kind)
     end

  | Let (l, id, t1, t2, t3) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct_with_type
                              meta env ctx t2 t1.delta in
     let decl = DefLet(id, t2, t2') in
     reconstruct meta (decl :: env) (decl :: ctx) t3

  | Prod (l, id, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') =
       let decl = DefAxiom(id, t1) in
       force_type meta (decl :: env) (decl :: ctx) t2 in
     let (meta, tt) = principal_type_system meta env ctx t1'.delta t2'.delta in
     (meta, {delta=Prod(l,id,t1.delta,t2.delta); essence=Prod(l,id,t1.essence,t2.essence)},
      tt)

  | Abs (l, id, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') =
       let decl = DefAxiom(id, t1) in
       reconstruct meta (decl :: env) (decl :: ctx) t2 in
     let (meta,typ,_) = force_type meta env ctx (Prod (l, id, t1.delta, t2'.delta)) in
     (meta, {delta=Abs(l, id, t1.delta, t2.delta); essence=Abs(l, id, nothing, t2.essence)},
      typ)

  | App (l, t1, l2) ->
     begin
       match l2 with
       | [] -> reconstruct meta env ctx t1
       | t2 :: l2 ->
          let (meta, t1, t1') = reconstruct meta env ctx (App (l,t1,l2)) in
          let t1, l2, et1, el2 =
            match t1.delta, t1.essence with
            | App(_,t1,l2), App(_,et1,el2) -> t1,l2,et1,el2
            | _ -> t1.delta, [], t1.essence, []
          in
          let t1' = strongly_normalize_full env @@ apply_all_substitution_full meta t1' in
          begin
            match t1'.delta, t1'.essence with
            | Prod (l, id, u1, u2), Prod(_, _, eu1, eu2) -> (* case 1: we know the type of t1 *)
               let (meta, t2, t2') =
                 reconstruct_with_type meta env ctx t2 u1 in
               (meta, {delta = App(l, t1, t2.delta :: l2);
                       essence = App(l, et1, t2.essence :: el2)},
                {delta = beta_redex u2 t2.delta;
                 essence = beta_redex eu2 t2.essence})
            | _ -> (* case 2: we do not know the type of t1 *)
               let (meta, t2, t2') = reconstruct meta env ctx t2 in
               let (meta, s) = meta_add_sort meta dummy_loc in
               let (meta, k) = meta_add meta ctx s dummy_loc in
               let meta = unification
                            meta env t1' (Prod(l, "x", t2'.delta,
                                               k.delta)) in
               (meta, {delta = App(l, t1, t2.delta :: l2);
                       essence = App(l, et1, t2.essence :: el2)},
                {delta=beta_redex k.delta t2.delta; essence=beta_redex k.essence t2.essence})
          end
     end

  | Inter (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = force_type meta env ctx t2 in
     let (meta, tt) = principal_set_system meta env ctx t1'.delta t2'.delta in
     (meta, {delta=Inter(l,t1.delta,t2.delta);essence=Inter(l,t1.essence,t2.essence)},
      tt)

  | Union (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = force_type meta env ctx t2 in
     let (meta, tt) = principal_set_system meta env ctx t1'.delta t2'.delta in
     (meta, {delta=Union(l,t1.delta,t2.delta);essence=Union(l,t1.essence,t2.essence)},
      tt)

  | SPair (l, t1, t2) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let (meta, t2, t2') = reconstruct_with_essence meta env ctx t2 t1.essence in
     let (meta, t', _) = force_type meta env ctx (Inter (l, t1'.delta, t2'.delta)) in
     (meta, {delta=SPair(l,t1.delta,t2.delta); essence=t1.essence},
      t')
  | SPrLeft (l, t1) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let t1' = strongly_normalize_full env @@ apply_all_substitution_full meta t1 in
     begin
       match t1'.delta, t1'.essence with
       | Inter(l,t',_), Inter(_,et',_) ->
          (meta, {delta=SPrLeft(l,t1.delta); essence=t1.essence},
           {delta=t'; essence=et'})
       | _ ->
          let (meta, s) = meta_add_sort meta dummy_loc in
          let (meta, a) = meta_add meta ctx s dummy_loc in
          let (meta, b) = meta_add meta ctx s dummy_loc in
          let meta = unification meta env t1' (Inter(l,a.essence,
                                                     b.essence)) in
          (meta, {delta=SPrLeft(l,t1.delta); essence=t1.essence}, a)
     end
  | SPrRight (l, t1) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let t1' = strongly_normalize_full env @@ apply_all_substitution_full meta t1 in
     begin
       match t1'.delta, t1'.essence with
       | Inter(l,_,t'), Inter(_,_,et') ->
          (meta, {delta=SPrRight(l,t1.delta); essence=t1.essence},
           {delta=t'; essence=et'})
       | _ ->
          let (meta, s) = meta_add_sort meta dummy_loc in
          let (meta, a) = meta_add meta ctx s dummy_loc in
          let (meta, b) = meta_add meta ctx s dummy_loc in
          let meta = unification meta env t1' (Inter(l,a.essence,
                                                     b.essence)) in
          (meta, {delta=SPrRight(l,t1.delta); essence=t1.essence}, b)
     end

  | SMatch (l, t1, t2, id1, t3, t4, id2, t5, t6) ->
     let (meta, t1, t1') = reconstruct meta env ctx t1 in
     let (meta, t2, t2') =
       reconstruct_with_type meta env ctx t2 (Prod(dummy_loc, id1, t1'.delta, Sort(l,Type))) in
     let (meta, t3, t3') = reconstruct_with_type meta env ctx t3 (Sort(dummy_loc, Type)) in
     let (meta, t5, t5') = reconstruct_with_type meta env ctx t5 (Sort(dummy_loc, Type)) in
     let meta = unification meta env t1' (Union(dummy_loc, t3.delta, t5.delta)) in
     let (meta, t4, t4') =
       reconstruct_with_type meta env (DefEssence("x", t1.essence, t3)
                                       :: ctx)
                             t4 (App(dummy_loc, t2.delta,
                                     SInLeft(dummy_loc, t5.delta,
                                             t3.delta) :: [])) in (* TO FIX: case where there is a spine in a spine *)
     let (meta, t6, t6') =
       reconstruct_with_all meta env (DefEssence("x", t1.essence, t5)
                                      :: ctx) t6
                            t4.essence (App(dummy_loc, t2.delta,
                                            SInRight(dummy_loc,
                                                     t3.delta,
                                                     t5.delta) :: []))
                            (* TO FIX *)
     in
     (meta,
      {delta=SMatch (l, t1.delta, t2.delta, id1, t3.delta, t4.delta, id2, t5.delta, t6.delta);
       essence=SMatch (l, t1.essence, t2.essence, id1, t3.essence, t4.essence, id2, t5.essence, t6.essence)},
      {delta=App(dummy_loc,t2.delta,t1.delta :: []);
       essence=App(dummy_loc,t2.essence,t1.essence :: [])}) (* to fix *)

  | SInLeft (l, t1, t2) ->
     let (meta, t1, _) = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, tt, _) = force_type meta env ctx (Union(l,t1.delta,t2'.delta)) in
     (meta, {delta=SInLeft(l,t1.delta,t2.delta); essence=SInLeft(l,t1.essence,t2.essence)},
     tt)

  | SInRight (l, t1, t2) ->
     let (meta, t1, _) = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, tt, _) = force_type meta env ctx (Union(l,t2'.delta,t1.delta)) in
     (meta, {delta=SInRight(l,t1.delta,t2.delta); essence=SInRight(l,t1.essence,t2.essence)},
     tt)

  | Coercion (l, t1, t2) ->
     let (meta, t1, t1') = force_type meta env ctx t1 in
     let (meta, t2, t2') = reconstruct meta env ctx t2 in
     let (meta, t2', _) = reconstruct_with_type meta env ctx t2'.delta t1'.delta in (* force both type to be on the same level *)
     if is_subtype env t1.essence t2'.essence then
       (meta, {delta = Coercion(l,t1.delta,t2.delta); essence=t2.essence},
        t1)
     else raise (Err "coercion")

  | Var (l, n) -> let (t1,t1') = get_from_context env n in
                  (meta, t1, t1')

  | Const (l, id) -> raise (Err "const")

  | Underscore l ->
     let (meta, s) = meta_add_sort meta l in
     let (meta, v) = meta_add meta ctx s l in
     let (meta, u) = meta_add meta ctx v l in
     (meta, u, v)

  | Meta (l, n, subst) ->
     get_from_meta meta ctx l n subst
and force_type meta env ctx t =
  let (meta, t, t') = reconstruct meta env ctx t in
  let x =
    try
      Some (unification meta env t' (Sort(dummy_loc, Type)))
    with
    | _ -> None
  in
  let y =
    try
      Some (unification meta env t' (Sort(dummy_loc, Kind)))
    with
    | _ -> None
  in
  match x, y with
  | Some _, Some _ -> (meta, t, t')
  | Some meta, None -> (meta, t, t')
  | None, Some meta -> (meta, t, t')
  | None, None -> raise (Err "force_type")
and reconstruct_with_type meta env ctx t1 t2 = (* dummy *)
  let (meta, t1, t1') = reconstruct meta env ctx t1 in
  (unification meta env t1' t2, t1, t1')
and reconstruct_with_essence meta env ctx t1 e = (* dummy *)
  reconstruct meta env ctx t1
and reconstruct_with_all meta env ctx t1 e1 t2 = (* dummy *)
  let (meta, t1, t1') = reconstruct meta env ctx t1 in
  (unification meta env t1' t2, t1, t1')

let check_axiom str id_list gamma l t =
  let (meta, t1, t2) = reconstruct (0,[]) gamma [] t in
  match t2.delta with
  | Sort (_,s) -> t2
  | _ -> raise (Err "check_axiom")
