Section Test.
Hypotheses(PosZeroNegTF: o).
Hypotheses (Test : OK ( union Pos Neg)) ( is_0 : OK ( inter ( arrow Neg F) ( inter ( arrow Zero T) ( arrow Pos F)))).
(* is_0 Test *)
Definition is0test : OK F.
apply(Copair__ _ (Abst_ _ (funx : _ ⇒App__(Proj_r__ (Proj_r__ is_0)) x)) (Abst_ _ (funx : _ ⇒App__(Proj_l__ is_0) x))); [now apply Test|]; apply Eqabst; intros x y pf; apply Eqapp; trivial;
assert (H : Eq _ _ is_0 (Proj_r (arrow Neg F) (inter (arrow Zero T) (arrow Pos F)) is_0)) by apply Eqproj_r;
assert (H0 : Eq _ _ (Proj_r (arrow Neg F) (inter (arrow Zero T) (arrow Pos F)) is_0)
(Proj_r (arrow Zero T) (arrow Pos F) (Proj_r (arrow Neg F) (inter (arrow Zero T) (arrow Pos F)) is_0)))
by apply Eqproj_r; assert (H1 : Eq _ _ is_0 (Proj_l (arrow Neg F) (inter (arrow Zero T) (arrow Pos F)) is_0)) by apply Eqproj_l;
apply Eqsymm in H; apply Eqsymm in H0; eapply Eqtrans; [now apply H0|]; eapply Eqtrans; [apply H| apply H1].
Defined.
End Test.
