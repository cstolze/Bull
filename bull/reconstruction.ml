open Utils
open Bruijn
open Reduction
open Subtyping
open Printer

(* returns the essence and the type of a term *)

exception Err of string

(* dummy *)
let unification meta env t1 t2 = meta

let meta_add_sort (n,meta) l = ((n+1, IsSort n :: meta), {delta=Meta(l,n,[]);essence=Meta(l,n,[])})

let meta_add (n,meta) ctx t l =
  let s = List.map (fun _ -> Var(dummy_loc,0)) ctx in
  ((n+1, DefMeta (ctx, n, t) :: meta), {delta=Meta(l,n,s);essence=Meta(l,n,s)})

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
               let meta = unification meta env t1' {delta=Prod(l, "x", t2'.delta, k.delta); essence=Prod(l,"x",t2'.essence, k.essence)} in
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
          let meta = unification meta env t1' {delta=Inter(l,a.essence,b.essence); essence=Inter(l,a.essence,b.essence)} in
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
          let meta = unification meta env t1' {delta=Inter(l,a.essence,b.essence); essence=Inter(l,a.essence,b.essence)} in
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
  reconstruct meta env ctx t (* dummy *)
and reconstruct_with_type meta env ctx t1 t2 =
  reconstruct meta env ctx t1 (* dummy *)
and reconstruct_with_essence meta env ctx t1 e =
  reconstruct meta env ctx t1 (* dummy *)
and reconstruct_with_all meta env ctx t1 e1 t2 =
  reconstruct meta env ctx t1 (* dummy *)


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





(* **************************************************************************************************** *)
(* ******************************************** TO REMOVE ********************************************* *)
(* **************************************************************************************************** *)
(*
let rec reconstruction str id_list gamma l t =
  let r0 = reconstruction str in
  let getloc = (* get location *)
    let Locnode (a,b,_) = l in (a,b)
  in
  let get n = (* get loc for the nth child *)
    let Locnode (_,_,l') = l in
    try List.nth l' n
    with _ -> l (* in case we're dealing with a let-variable (it is a hack, we should be able to recurse while staying on the same locnode level)*)
  in
  let r nl1 t1 = (* recursive call *)
    Result.bind (r0 id_list gamma (get nl1) t1)
  in
  let r2 t1 t2 f = (* recursively type the two children *)
    r 0 t1 (fun x -> r 1 t2 (f x))
  in
  let check_abs x nl1 t1 nl2 t2 f = (* check that x:t1 can be put in gamma, then type gamma,x:t1 |- t2 *)
    r nl1 t1 (fun (s1,e1,_) ->
	      match s1 with
	      | Sort s -> Result.bind (r0 (x::id_list) (DefAxiom(t1,e1)::gamma) (get nl2) t2) (f s e1) (* note the signature of f *)
	      | _ -> Result.Error (error_abs id_list (get 0) str s1) )
  in
  let type_prod x s1 t2 = (* s1 is the sort of A in 'forall x:A, t2' *)
    match t2 with
    | Sort s2 ->
       (match principal_type_system s1 s2 with
	| Some s -> Result.Ok s
	| None -> Result.Error (error_pts getloc str))
    | _ -> Result.Error (error_type_prod (x::id_list) getloc str t2)
  in
  let type_app t (t1,e1,et1) (t2,e2,et2) =
    match (t1,et1) with
    | (Prod(_,_,t3), Prod (_,et2',et3)) -> if is_equal gamma et2 et2' then Result.Ok (beta_redex t3 t, App(e1,e2), beta_redex et3 e2)
					      else
					     Result.Error (error_match id_list getloc str et2' et2)
    | (Subset(_,_,t3), Subset(_,et2',et3)) -> if is_equal gamma et2 et2' then Result.Ok (beta_redex t3 t, e2, beta_redex et3 e2) else Result.Error (error_match id_list getloc str et2' et2)
    | _ -> Result.Error (error_no_prod id_list (get 0) str t1)
  in
  let type_sproj b t1 = (* b = true -> proj_left *)
     r 0 t1
       (fun (t1,e1,et1) ->
	match (t1,et1) with
	| (Inter(l,r),Inter(el,er)) -> Result.Ok((if b then l else r),e1,if b then el else er)
	| _ -> Result.Error (error_sproj id_list (get 0) str t1))
  in
  let type_set s1 s2 e = (* look if s1 = s2 and if we are dealing with sets *)
    if s1 = s2 then
      match s1 with
      | Sort s -> if is_set s then Result.Ok (Sort s,e,Sort s) else Result.Error (error_set getloc str)
      | _ -> Result.Error (error_set getloc str)
    else Result.Error (error_set getloc str)
  in
  let type_union_inter b t1 t2 = (* b = true -> inter *)
    r2 t1 t2 (fun (s1,e1,_) (s2,e2,_) ->
	      type_set s1 s2 (if b then Inter(e1,e2) else Union(e1,e2)))
  in
  let type_inj b t1 t2 = (* b = true -> inj_left *)
    let l' = let l = get 0 in let Locnode (a,b,_) = l in Locnode(a,b,[l;l]) (* fix the location for the recursive call *)
    in
    r 1 t2 (fun (t,e,_) ->
	    let res = if b then Union (t,t1) else Union (t1,t)
	    in
	    Result.bind (r0 id_list gamma l' res) (fun (_,et,_) -> Result.Ok (res,e,et)))
  in
  match t with
  | Sort s -> type_of_sort s
  | Let (id,t1,t2) ->
     r 0 t1
       (fun (t1',e1',et1')
	-> r0 (id::id_list) (DefLet(t1,t1',e1',et1') :: gamma) (get 1) t2)
  | Prod (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,_)
					       ->
					       Result.bind (type_prod id s1 t2) (fun s -> Result.Ok (Sort s,Prod(id,e1,e2),Sort s)))
  | Abs (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,et2) ->
 					      (* hack to see if Prod(id,t1,t2) is well-defined *)
						 Result.bind (r0 id_list gamma l (Prod(id,t1,t2)))
							     (fun (_,et,_) -> Result.Ok (Prod(id,t1,t2), Abs(id,Nothing,e2),Prod(id,e1,et2))))
  | Subset (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,_) -> type_set (Sort s1) t2 (Subset(id,e1,e2)))
  | Subabs (id,t1,t2) -> check_abs id 0 t1 1 t2 (fun s1 e1 (t2,e2,et2) ->
						 if is_equal (DefAxiom(Nothing,Nothing)::gamma) e2 (Var 0) then
						   (* hack to see if Subset(id,t1,t2) is well-defined *)
						   Result.bind (r0 id_list gamma l (Subset(id,t1,t2)))
							       (fun (_,et,_) -> Result.Ok (Subset(id,t1,t2), Abs(id,Nothing,(*e2*)Var 0),Subset(id,e1,et2)))
						 else Result.Error (error_essence getloc str))
  | App (t1, t2) -> r2 t1 t2 (type_app t2)
  | Inter (t1, t2) -> type_union_inter true t1 t2
  | Union (t1, t2) -> type_union_inter false t1 t2
  | SPair (t1, t2) -> r2 t1 t2
			 (fun (t1,e1,et1) (t2,e2,et2) ->
			  if is_equal gamma e1 e2 then
			    r2 t1 t2 (fun (s1,_,_) (s2,_,_) ->
				      match (s1,s2) with
				      | (Sort s1, Sort s2) -> if (s1 == s2) then if is_set s1 then Result.Ok (Inter (t1, t2), e1, Inter(et1,et2)) else Result.Error (error_set getloc str) else Result.Error (error_set getloc str)
				      | _ -> assert false)
			  else Result.Error (error_essence getloc str))
  | SPrLeft t1 -> type_sproj true t1
  | SPrRight t1 -> type_sproj false t1
  | SMatch (t1, t2) -> r2 t1 t2 (fun (t1',e1',et1') (t2',e2',et2') ->
				 match (e1',et2') with
				 | (Prod(_,Union(a,b),f),
				    Inter(Prod(_,a',fa),Prod(_,b',fb)))->
				    if is_equal (DefAxiom(Nothing,Nothing)::gamma) fa fb then
				      if is_equal (DefAxiom(Nothing,Nothing)::gamma) f fa && is_equal gamma a a' && is_equal gamma b b' then
					Result.Ok (t1, e2', e1')
				      else Result.Error (error_return (get 0) str)
				    else Result.Error (error_with (get 1) str)
				 | _ -> Result.Error (error_smatch getloc str))
  | SInLeft (t1, t2) -> type_inj true t1 t2
  | SInRight (t1, t2) -> type_inj false t1 t2
  | Coercion (t1, t2) -> r2 t1 t2 (fun (t1',e1',_) (t2',e2',et2') ->
    match t1' with
    | Sort s1 ->
       Result.bind (r0 id_list gamma l t2')
         (fun (t,_,_) -> match t with
                         | Sort s2 -> if s1 == s2 then
                                        if is_subtype gamma et2' e1' then Result.Ok(t1,e2',e1')
                                        else
                                          Result.Error(error_subtype
                                                         l str id_list
                                                         t1 t2')
                                      else
                                        Result.Error (error_set getloc str)
                         | _ -> Result.Error(error_coe2 (get 1) str))
    | _ -> Result.Error(error_coe1 (get 0) str id_list t1'))
  | Var n -> let (_,t,e,et) = get_from_context gamma n in Result.Ok(t,e,et)
  | Const id -> Result.Error(error_const getloc str id)
  | Omega -> Result.Ok(Sort Type, Omega, Sort Type)
  | Nothing -> assert false
  | Meta n -> Result.Error("No meta variables for now.\n")

let check_axiom str id_list gamma l t =
  Result.bind (reconstruction str id_list gamma l t)
	      (fun (s,et,_) -> match s with
			       | Sort s -> Result.Ok (et)
			       | _ -> Result.Error error_axiom)
  *)

let check_axiom str id_list gamma l t =
  let (meta, t1, t2) = reconstruct (0,[]) gamma [] t in
  match t2.delta with
  | Sort (_,s) -> t2
  | _ -> raise (Err "check_axiom")
