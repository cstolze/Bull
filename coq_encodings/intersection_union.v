(* Encodings made thanks to the help of Furio Honsell and Ivan Scagnetto *)

(* Define our types *)
Axiom o : Set.
(* Axiom omegatype : o. *)
Axioms (arrow relev inter union : o -> o -> o).

(* Transform our types into LF types *)
Axiom OK : o -> Set.

(* Define the essence equality as an equivalence relation *)
Axiom Eq : forall (s t : o), OK s -> OK t -> Prop.
Axiom Eqrefl : forall (s : o) (M : OK s), Eq s s M M.
Axiom Eqsymm : forall (s t : o) (M : OK s) (N : OK t), Eq s t M N -> Eq t s N M.
Axiom Eqtrans : forall (s t u : o) (M : OK s) (N : OK t) (O : OK u), Eq s t M N -> Eq t u N O -> Eq s u M O.

(* constructors for arrow (->I and ->E) *)
Axiom Abst : forall (s t : o), ((OK s) -> (OK t)) -> OK (arrow s t).
Axiom Sabst : forall (s t : o) (M : OK s -> OK t) (N : OK s), (Eq s t N (M N)) -> OK (relev s t).
Axiom App : forall (s t : o), OK (arrow s t) -> OK s -> OK t.
Axiom Sapp : forall (s t : o), OK (relev s t) -> OK s -> OK t.

(* constructors for intersection *)
Axiom Proj_l : forall (s t : o), OK (inter s t) -> OK s.
Axiom Proj_r : forall (s t : o), OK (inter s t) -> OK t.
Axiom Pair : forall (s t : o) (M : OK s) (N : OK t), Eq s t M N -> OK (inter s t).

(* constructors for union *)
Axiom Inj_l : forall (s t : o), OK s -> OK (union s t).
Axiom Inj_r : forall (s t : o), OK t -> OK (union s t).
Axiom Copair : forall (s t u : o) (X : OK (arrow s u)) (Y : OK (arrow t u)), OK (union s t) -> Eq (arrow s u) (arrow t u) X Y -> OK u.

(* omega *)
(* Axiom star : OK omegatype. *)

(* define equality wrt arrow constructors *)
Axiom Eqabst : forall (s t s' t' : o) (M : OK s -> OK t) (N : OK s' -> OK t'), (forall (x : OK s) (y : OK s'), Eq s s' x y -> Eq t t' (M x) (N y)) -> Eq (arrow s t) (arrow s' t') (Abst s t M) (Abst s' t' N).
Axiom Eqapp : forall (s t s' t' : o) (M : OK (arrow s t)) (N : OK s) (M' : OK (arrow s' t')) (N' : OK s'), Eq (arrow s t) (arrow s' t') M M' -> Eq s s' N N' -> Eq t t' (App s t M N) (App s' t' M' N').
Axiom Eqsabst : forall (s t s' t' : o) (M : OK (relev s t)) (N : OK (relev s' t')), Eq (relev s t) (relev s' t') M N.
Axiom Eqsapp : forall (s t : o) (M : OK (relev s t)) (x : OK s), Eq s t x (Sapp s t M x).

(* define equality wrt intersection constructors *)
Axiom Eqpair : forall (s t u : o) (M : OK s) (N : OK t) (O : OK u) (pf : Eq s t M N), (Eq s u M O) -> Eq (inter s t) u (Pair s t M N pf) O.
Axiom Eqproj_l : forall (s t u : o) (M : OK (inter s t)) (N : OK u), Eq (inter s t) u M N -> Eq s u (Proj_l s t M) N.
Axiom Eqproj_r : forall (s t u : o) (M : OK (inter s t)) (N : OK u), Eq (inter s t) u M N -> Eq t u (Proj_r s t M) N.

(* define equality wrt union *)
Axiom Eqinj_l : forall (s t u : o) (M : OK s) (N : OK u), Eq s u M N -> Eq (union s t) u (Inj_l s t M) N.
Axiom Eqinj_r : forall (s t u : o) (M : OK t) (N : OK u), Eq t u M N -> Eq (union s t) u (Inj_r s t M) N.
Axiom Eqcopair : forall (s t u v : o) (A : OK (arrow s u)) (B : OK (arrow t u)) (C : OK (union s t)) (Z : Eq (arrow s u) (arrow t u) A B) (N : OK v), (forall (x : OK s), Eq s (union s t) x C -> Eq u v (App s u A x) N) -> Eq u v (Copair s t u A B C Z) N. (* If you look closely at the Eqapp rule (knowing that Eq is an equivalence), you can infer that the hypothesis (forall (y : OK t), Eq t (union s t) y C -> Eq u v (App t u B y) N) is useless *)

(* define equality wrt omega *)
(* Axiom Eqstar : forall (s : o) (M : OK s), Eq omegatype s star M. (* OH GOD IT BREAKS THE TRANSITIVITY *) *)

(****************************************************************************************************)
(********************************************* EXAMPLES *********************************************)
(****************************************************************************************************)

Section Examples.
  Hypotheses s t : o.

  (* lambda x. x x : (sigma inter (sigma -> tau)) -> tau *)
  Definition autoapp : OK (arrow (inter s (arrow s t)) t) :=
    Abst (inter s (arrow s t)) t (fun x : OK (inter s (arrow s t)) => App s t (Proj_r s (arrow s t) x) (Proj_l s (arrow s t) x)).

  (* lambda x. x : (sigma -> sigma) inter (tau -> tau) *)
  Definition id1 : OK (inter (arrow s s) (arrow t t)) :=
    Pair (arrow s s) (arrow t t) (Abst s s (fun x : OK s => x)) (Abst t t (fun x : OK t => x)) (Eqabst s s t t (fun x : OK s => x) (fun x : OK t => x) (fun (x : OK s) (y : OK t) (Z : Eq s t x y) => Z)).

  (* lambda x. x : (sigma union tau) -> (tau union sigma) *)
  Definition id2 : OK (arrow (union s t) (union t s)) :=
    Abst (union s t) (union t s) (fun x : OK (union s t) => Copair s t (union t s) (Abst s (union t s) (fun y : OK s => Inj_r t s y)) (Abst t (union t s) (fun y : OK t => Inj_l t s y)) x (Eqabst s (union t s) t (union t s) (fun y : OK s => Inj_r t s y) (fun y : OK t => Inj_l t s y) (fun (x : OK s) (y : OK t) (Z : Eq s t x y) => Eqtrans (union t s) s (union t s) (Inj_r t s x) x (Inj_l t s y) (Eqinj_r t s s x x (Eqrefl s x)) (Eqtrans s t (union t s) x y (Inj_l t s y) Z (Eqsymm (union t s) t (Inj_l t s y) y (Eqinj_l t s t y y (Eqrefl t y))))))).

  Definition id' : OK (arrow (union s t) (union t s)).
  Proof.
    apply (Abst (union s t) (union t s)).
    intro x.
    apply (Copair s t (union t s) (Abst s (union t s) (fun y : OK s => Inj_r t s y)) (Abst t (union t s) (fun y : OK t => Inj_l t s y)) x).
    apply Eqabst.
    intros.
    assert (Eq s (union t s) x0 (Inj_r t s x0)).
    {
      apply Eqsymm.
      apply Eqinj_r.
      apply Eqrefl.
    }
    assert (Eq t (union t s) y (Inj_l t s y)).
    {
      apply Eqsymm.
      apply Eqinj_l.
      apply Eqrefl.
    }
    eapply Eqtrans.
    apply (Eqsymm _ _ x0); trivial.
    eapply Eqtrans.
    apply H.
    apply H1.
  Defined.

End Examples.

Extraction id2.
(* let id2 s t =
  abst (union s t) (union t s) (fun x ->
    copair s t (union t s) (abst s (union t s) (fun y -> inj_r t s y))
      (abst t (union t s) (fun y -> inj_l t s y)) x) *)

Extraction id'.
(* let id' s t =
  abst (union s t) (union t s) (fun x ->
    copair s t (union t s) (abst s (union t s) (fun y -> inj_r t s y))
      (abst t (union t s) (fun y -> inj_l t s y)) x) *)
