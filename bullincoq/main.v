Require Import Bool.
Require Import List.

(* functions that manage identifiers (ie strings). Not implemented *)
Parameter Id : Set.
Parameter (equal : forall x y : Id, {x = y} + {x <> y}).
Parameter (new : forall l : list Id, { x : Id | ~ List.In x l }).

(* type declarations *)

Inductive Kind (var : Set) : Set :=
| type : Kind var (* Type *)
| kprod : (var -> Kind var) -> Sigma var -> Kind var (* \Pi x : A. K *) (* ??? *)
with
Sigma (var : Set) : Set :=
(* | func : Sigma -> Sigma -> Sigma (* A -> B *) *)
| prod : (var -> Sigma var) -> Sigma var -> Sigma var (* \Pi x : A. B *)
| lamb : (var -> Sigma var) -> Sigma var -> Sigma var (* \Lambda x : A. B *)
| sapp : Sigma var -> Delta var -> Sigma var (* A M *)
| sand : Sigma var -> Sigma var -> Sigma var (* A \cap B *)
| sor : Sigma var -> Sigma var -> Sigma var (* A \cup B *)
| svar : Id -> Sigma var (* a *) (* ??? *)
| om : Sigma var (* \omega *)
| wildcard : Sigma var (* ? (for type inference purposes) *)
with
Delta (var : Set) : Set :=
| vari : var -> Delta var (* x *)
| star : Delta var (* * *)
| abst : (var -> Delta var) -> Sigma var -> Delta var (* \lambda x : A. M *) (* ??? *)
| appl : Delta var -> Delta var -> Delta var (* M N *)
| and : Delta var -> Delta var -> Delta var (* <M, N> *)
| pr1 : Delta var -> Delta var (* pr1 M *)
| pr2 : Delta var -> Delta var (* pr2 M *)
| or : (var -> Delta var) -> Sigma var -> (var -> Delta var) -> Sigma var -> Delta var -> Delta var (* [\lambda x : A. M, \lambda y : B. N] M' *)
| in1 : Delta var -> Delta var (* in1 M *)
| in2 : Delta var -> Delta var (* in2 M *)
.

Fixpoint squashs (var : Set) (s : Sigma (Delta var)) : Sigma var :=
  match s with
      | prod _ f s' => prod _ (fun x : var => squashs _ (f (vari _ x))) (squashs _ s')
      | lamb _ f s' => lamb _ (fun x : var => squashs _ (f (vari _ x))) (squashs _ s')
      | sapp _ s' d'' => sapp _ (squashs _ s') (squashd _ d'')
      | sand _ s' s'' => sand _ (squashs _ s') (squashs _ s'')
      | sor _ s' s'' => sor _ (squashs _ s') (squashs _ s'')
      | svar _ x => svar var x
      | om _ => om var
      | wildcard _ => wildcard var
  end
with
squashd (var : Set) (d : Delta (Delta var)) : Delta var :=
  match d with
    | vari _ d' => d'
    | star _ => star var
    | abst _ f s => abst _ (fun x : var => squashd _ (f (vari _ x))) (squashs _ s)
    | appl _ d' d'' => appl _ (squashd _ d') (squashd _ d'')
    | and _ d' d'' => and _ (squashd _ d') (squashd _ d'')
    | pr1 _ d' => pr1 _ (squashd _ d')
    | pr2 _ d' => pr2 _ (squashd _ d')
    | or _ f s f' s' d' => or _ (fun x : var => squashd _ (f (vari _ x))) (squashs _ s) (fun x : var => squashd _ (f' (vari _ x))) (squashs _ s') (squashd _ d')
    | in1 _ d' => in1 _ (squashd _ d')
    | in2 _ d' => in2 _ (squashd _ d')
  end.

Definition substi (var : Set) (d : Delta var -> Delta (Delta var)) (d' : Delta var) : Delta var :=
  squashd var (d d').

Definition Kind' := forall var : Set, Kind var.
Definition Sigma' := forall var : Set, Sigma var.
Definition Delta' := forall var : Set, Delta var.
Definition app' := forall var : Set, var -> Delta var.

Definition substi' (d : app') (d' : Delta') : Delta' :=
  fun var : Set =>
    squashd var (d (Delta var) (d' var)).

(* DOES NOT COMPILE UNDER THIS LINE *)

Inductive Equiv : Delta' -> Delta' -> Prop :=
| erefl : forall d : Delta', Equiv d d
| esym : forall d d' : Delta', Equiv d' d -> Equiv d d'
| etrans : forall d d' d'' : Delta',  Equiv d d' -> Equiv d' d'' -> Equiv d d''
| eeta :  forall (d : Delta') (s : Sigma'), Equiv d (fun var => abst _ (fun x : var => (appl _ (d var) (vari _ x))) (s var))
| ebeta : forall (d : app') (d' : Delta') (s : Sigma'), Equiv (fun var => appl _ (abst _ (d var) (s var)) (d' var)) (substi' d d')
| eapp : forall d d' d1 d1' : Delta', Equiv d d1 -> Equiv d' d1' -> Equiv (fun var => appl var (d var) (d' var)) (fun var => appl var (d1 var) (d1' var))
| elam : forall (d d' : app'), (forall (var : Set) (x : var), Equiv (d var x) (d' x)) -> Equiv (fun var => abst var d) (fun var => abst var d')
| eand : forall d d' d1 d1' : Delta var, Equiv var d d1 -> Equiv var d' d1' -> Equiv var (and _ d d') (and _ d1 d1')
| epr1 : forall d d' : Delta var, Equiv var d d' -> Equiv var (pr1 _ d) (pr1 _ d')
| epr2 : forall d d' : Delta var, Equiv var d d' -> Equiv var (pr2 _ d) (pr2 _ d')
| eor : forall (d d' d1 d1' : var -> Delta var) (d'' d1'' : Delta var), (forall x : var, Equiv var (d x) (d1 x)) -> (forall x : var, Equiv var (d' x) (d1' x)) -> Equiv var d'' d1'' -> Equiv var (or var d d' d'') (or var d1 d1' d1'')
| ein1 : forall d d' : Delta var, Equiv var d d' -> Equiv var (in1 _ d) (in1 _ d')
| ein2 : forall d d' : Delta var, Equiv var d d' -> Equiv var (in2 _ d) (in2 _ d')
.

Inductive Signature : Set :=
| emptysig : Signature (* <> *)
| ctype : Id -> Kind -> Signature -> Signature (* \Sigma, a : K *)
| cvar : Id -> Sigma -> Signature -> Signature (* \Sigma, c : A *)
.

Inductive Context : Set :=
| emptyctx : Context (* <> *)
| ccons : Id -> Sigma -> Context -> Context (* \Gamma, x : A *)
.

(* membership predicates for contexts and signatures *)
Fixpoint in_sig (x : Id) (s : Signature) : Prop :=
  match s with
    | emptysig => False
    | ctype y _ s' => x = y \/ in_sig x s'
    | cvar y _ s' => x = y \/ in_sig x s'
  end.

Fixpoint in_ctx (x : Id) (c : Context) : Prop :=
  match c with
    | emptyctx => False
    | ccons y _ c' => x = y \/ in_ctx x c'
  end.

Fixpoint const_in_sig (x : Id) (f : Sigma) (s : Signature) : Prop :=
  match s with
    | emptysig => False
    | ctype _ _ s' => const_in_sig x f s'
    | cvar y f' s' => (x = y /\ f = f') \/ const_in_sig x f s'
  end.

Fixpoint type_in_sig (x : Id) (k : Kind) (s : Signature) : Prop :=
  match s with
    | emptysig => False
    | ctype y k' s' => (x = y /\ k = k') \/ type_in_sig x k s'
    | cvar _ _ s' => type_in_sig x k s'
  end.

Fixpoint var_in_ctx (x : Id) (f : Sigma) (c : Context) : Prop :=
  match c with
    | emptyctx => False
    | ccons y f' c' => (x = y /\ f = f') \/ var_in_ctx x f c'
  end.


(* checking predicates *)
Inductive ValidSig : Signature -> Prop :=
| es : ValidSig emptysig
| ks : forall (a : Id) (k : Kind) (s : Signature), ValidSig s -> ValidKind emptyctx s k -> ~ in_sig a s -> ValidSig (ctype a k s)
| ss : forall (a : Id) (f : Sigma) (s : Signature), ValidSig s -> ValidSigma emptyctx s f type -> ~ in_sig a s -> ValidSig (ccons a f s)
with
ValidCtx : Sigma -> Context -> Prop :=
| ec : forall s : Signature, ValidSig s -> ValidCtx s Type
| sc : forall (a : Id) (f : Sigma) (c : Context) (s : Sigma), ValidCtx s c -> ValidSigma c s f type -> ~ in_ctx a c -> ValidCtx s (ccons a f c)
with
ValidKind : Context -> Signature -> Kind -> Prop :=
| t : forall (s : Signature) (c : Context), ValidCtx s c -> ValidKind c s type
| pk : forall (c : Context) (a : Id) (f : Sigma) (s : Signature) (k : Kind), ValidKind (ccons a f c) s k -> ValidKind c s (kprod a f k)
with
ValidSigma : Context -> Signature -> Sigma -> Kind -> Prop :=
| cs : forall (c : Context) (s : Signature) (a : Id) (k : Kind), ValidCtx s c -> const_in_sig a f s -> ValidSigma c s (svar a) k
| ps : forall 

with
ValidDelta : Context -> Signature -> Delta -> Sigma -> Prop :=