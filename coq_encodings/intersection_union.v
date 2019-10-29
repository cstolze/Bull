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
Axiom App : forall (s t : o), OK (arrow s t) -> OK s -> OK t.

(* constructors for strong arrows *)
Axiom Sabst : forall (s t : o) (M : OK s -> OK t), (forall (N : OK s), (Eq s t N (M N))) -> OK (relev s t).
Axiom Sapp : forall (s t : o), OK (relev s t) -> OK s -> OK t.

(* constructors for intersection *)
Axiom Proj_l : forall (s t : o), OK (inter s t) -> OK s.
Axiom Proj_r : forall (s t : o), OK (inter s t) -> OK t.
Axiom Pair : forall (s t : o) (M : OK s) (N : OK t), Eq s t M N -> OK (inter s t).

(* constructors for union *)
Axiom Inj_l : forall (s t : o), OK s -> OK (union s t).
Axiom Inj_r : forall (s t : o), OK t -> OK (union s t).
Axiom Copair : forall (s t u : o) (X : OK (arrow s u)) (Y : OK (arrow t u)), OK (union s t) -> Eq (arrow s u) (arrow t u) X Y -> OK u.

(* define equality wrt arrow constructors *)
Axiom Eqabst : forall (s t s' t' : o) (M : OK s -> OK t) (N : OK s' -> OK t'), (forall (x : OK s) (y : OK s'), Eq s s' x y -> Eq t t' (M x) (N y)) -> Eq (arrow s t) (arrow s' t') (Abst s t M) (Abst s' t' N).
Axiom Eqapp : forall (s t s' t' : o) (M : OK (arrow s t)) (N : OK s) (M' : OK (arrow s' t')) (N' : OK s'), Eq (arrow s t) (arrow s' t') M M' -> Eq s s' N N' -> Eq t t' (App s t M N) (App s' t' M' N').

(* define equality wrt strong arrow constructors *)
Axiom Eqsabst : forall (s t s' t' : o) (M : OK (relev s t)) (N : OK (relev s' t')), Eq (relev s t) (relev s' t') M N.
Axiom Eqsapp : forall (s t : o) (M : OK (relev s t)) (x : OK s), Eq s t x (Sapp s t M x).

(* define equality wrt intersection constructors *)
Axiom Eqpair : forall (s t : o) (M : OK s) (N : OK t) (pf : Eq s t M N), Eq (inter s t) s (Pair s t M N pf) M.
Axiom Eqproj_l : forall (s t : o) (M : OK (inter s t)), Eq (inter s t) s M (Proj_l s t M).
Axiom Eqproj_r : forall (s t : o) (M : OK (inter s t)), Eq (inter s t) t M (Proj_r s t M).

(* define equality wrt union *)
Axiom Eqinj_l : forall (s t : o) (M : OK s), Eq (union s t) s (Inj_l s t M) M.
Axiom Eqinj_r : forall (s t : o) (M : OK t), Eq (union s t) t (Inj_r s t M) M.
Axiom Eqcopair : forall (s t u : o) (M : OK (arrow s u)) (N : OK (arrow t u)) (O : OK (union s t)) (pf: Eq (arrow s u) (arrow t u) M N) (x : OK s), Eq s (union s t) x O -> Eq u u (App s u M x) (Copair s t u M N O pf).

(****************************************************************************************************)
(********************************************* EXAMPLES *********************************************)
(****************************************************************************************************)

Section Examples.
  Hypotheses s t : o.

  (* lambda x. x x : (sigma inter (sigma -> tau)) -> tau *)
  Definition autoapp : OK (arrow (inter s (arrow s t)) t) :=
    Abst (inter s (arrow s t)) t (fun x : OK (inter s (arrow s t)) => App s t (Proj_r s (arrow s t) x) (Proj_l s (arrow s t) x)).

  (* lambda x. x : (sigma -> sigma) inter (tau -> tau) *)
  Definition polyid : OK (inter (arrow s s) (arrow t t)) :=
    Pair (arrow s s) (arrow t t) (Abst s s (fun x : OK s => x)) (Abst t t (fun x : OK t => x)) (Eqabst s s t t (fun x : OK s => x) (fun x : OK t => x) (fun (x : OK s) (y : OK t) (Z : Eq s t x y) => Z)).

  (* lambda x. x : (sigma union tau) -> (tau union sigma) *)
  Definition commutunion : OK (arrow (union s t) (union t s)) :=
    Abst (union s t) (union t s)
         (fun x : OK (union s t) =>
            Copair s t (union t s) (Abst s (union t s) (fun y : OK s => Inj_r t s y))
                   (Abst t (union t s) (fun y : OK t => Inj_l t s y)) x
                   (Eqabst s (union t s) t (union t s) (fun y : OK s => Inj_r t s y)
                           (fun y : OK t => Inj_l t s y)
                           (fun (x0 : OK s) (y : OK t) (pf : Eq s t x0 y) =>
                              Eqtrans (union t s) s (union t s) (Inj_r t s x0) x0
                                      (Inj_l t s y)
                                      (Eqinj_r t s x0)
                                      (Eqtrans s t (union t s) x0 y (Inj_l t s y) pf
                                               (Eqsymm (union t s) t (Inj_l t s y) y
                                                       (Eqinj_l t s y)))))).

  Definition commutunion' : OK (arrow (union s t) (union t s)).
  Proof.
    apply (Abst (union s t) (union t s)).
    intro x.
    apply (Copair _ _ _ (Abst _ _ (fun y : _ => Inj_r _ _ y))
                  (Abst _ _ (fun y : _ => Inj_l _ _ y)) x).
    apply Eqabst.
    intros x0 y pf.
    assert (Eq _ _ (Inj_r t _ x0) x0) by apply Eqinj_r.
    assert (Eq _ _ y (Inj_l _ s y)). {
      apply Eqsymm.
      apply Eqinj_l.
    }
    eapply Eqtrans.
    now apply H.
    eapply Eqtrans.
    now apply pf.
    trivial.
  Defined.

End Examples.

Print commutunion.
(* let commutunion s t =
  abst (union s t) (union t s) (fun x ->
    copair s t (union t s) (abst s (union t s) (fun y -> inj_r t s y))
      (abst t (union t s) (fun y -> inj_l t s y)) x) *)

Eval compute in commutunion'.
(* let commutunion' s t =
  abst (union s t) (union t s) (fun x ->
    copair s t (union t s) (abst s (union t s) (fun y -> inj_r t s y))
      (abst t (union t s) (fun y -> inj_l t s y)) x) *)

Section Test.
  Hypotheses (Pos Zero Neg T F : o).
  Hypotheses (Test : OK (union Pos Neg))
             (is_0 : OK (inter (arrow Neg F) (inter (arrow Zero T) (arrow Pos F)))).

  (* is_0 Test *)
  Definition is0test : OK F.
    apply (Copair _ _ _ (Abst _ _ (fun x : _ => App _ _ (Proj_r _ _ (Proj_r _ _ is_0)) x))
                  (Abst _ _ (fun x : _ => App _ _ (Proj_l _ _ is_0) x))).
    now apply Test.
    apply Eqabst.
    intros x y pf.
    apply Eqapp.
    - assert (H : Eq _ _ is_0 (Proj_r (arrow Neg F) (inter (arrow Zero T)
                                                           (arrow Pos F)) is_0))
        by apply Eqproj_r.
      assert (H0 : Eq _ _ (Proj_r (arrow Neg F) (inter (arrow Zero T)
                                                       (arrow Pos F)) is_0)
                      (Proj_r (arrow Zero T) (arrow Pos F)
                              (Proj_r (arrow Neg F) (inter (arrow Zero T)
                                                           (arrow Pos F)) is_0)))
        by apply Eqproj_r.
      assert (H1 : Eq _ _ is_0 (Proj_l (arrow Neg F) (inter (arrow Zero T)
                                                            (arrow Pos F)) is_0))
        by apply Eqproj_l.
      apply Eqsymm in H.
      apply Eqsymm in H0.
      eapply Eqtrans.
      apply H0.
      eapply Eqtrans.
      apply H.
      apply H1.
    - trivial.
  Defined.

  Print is0test.
  Eval compute in is0test.
End Test.