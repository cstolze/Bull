Inductive lambda : Set :=
| Var : nat -> lambda
| Abs : lambda -> lambda
| App : lambda -> lambda -> lambda.

(* Update the de Bruijn indices, starting from level, by adding offset to them *)
Fixpoint lift level offset t :=
  match t with
  | Var n => if Nat.leb level n then Var (offset + n) else Var n
  | Abs t => Abs (lift (S level) offset t)
  | App t1 t2 => App (lift level offset t1) (lift level offset t2)
  end.

(* Substitute 'Var level' with t2 (with fixed de Bruijn indices) *)
Fixpoint subs level t1 t2 :=
  match t1 with
  | Var n => if Nat.eqb level n then lift 0 level t2 else Var n
  | Abs t => Abs (subs (S level) t t2)
  | App t t' => App (subs level t t2) (subs level t' t2)
  end.

Inductive single_step_beta : lambda -> lambda -> Prop :=
| Beta : forall t1 t2, single_step_beta (App (Abs t1) t2) (subs 0 t1 t2)
| App_closure_left : forall t1 t2 t1', single_step_beta t1 t1' -> single_step_beta (App t1 t2) (App t1' t2)
| App_closure_right : forall t1 t2 t2', single_step_beta t2 t2' -> single_step_beta (App t1 t2) (App t1 t2')
| Lam_closure : forall t1 t2, single_step_beta t1 t2 -> single_step_beta (Abs t1) (Abs t2).

Definition nf M := forall N, single_step_beta M N -> False.

Inductive vNF : lambda -> Prop :=
| NFvar: forall n, vNF (Var n)
| NFapp: forall M N, vNF M -> NF N -> vNF (App M N)
with
NF : lambda -> Prop :=
| NFval : forall M, vNF M -> NF M
| NFabs : forall M, NF M -> NF (Abs M).

Fixpoint vNF_to_nf M : vNF M -> nf M
with NF_to_nf M : NF M -> nf M.
Proof.
  {
    intro H; induction H.
    - intros N H.
      inversion H.
    - intros N1 H1.
      inversion H1.
      + rewrite <- H3 in H.
        inversion H.
      + apply (vNF_to_nf M H t1'); trivial.
      + apply (NF_to_nf N H0 t2'); trivial.
  }
  {
    intro H; induction H.
    - apply vNF_to_nf; trivial.
    - intros N1 H1.
      inversion H1.
      apply (NF_to_nf M H t2); trivial.
  }
Qed.

Inductive strongly_normalize t1 : Prop :=
| Stuck : NF M -> strongly_normalize t1
| Trans : (forall t2, single_step_beta t1 t2 -> strongly_normalize t2) -> strongly_normalize t1.



Lemma sn_app : forall M N, strongly_normalize (App M N) -> strongly_normalize M /\ strongly_normalize N.
Proof.
  induction M.
  
Qed.

Inductive simple_type : Set :=
| tp : simple_type
| arr : simple_type -> simple_type -> simple_type.

Fixpoint find {A : Type} m (l : list A) :=
  match l with
  | nil => None
  | cons x l' =>
    match m with
    | 0 => Some x
    | S m' => find m' l'
    end
  end.

Inductive simply_typed (env : list simple_type) : lambda -> simple_type -> Prop :=
| Var_rule : forall n t, find n env = Some t -> simply_typed env (Var n) t
| Abs_rule : forall t T1 T2, simply_typed (cons T1 env) t T2 -> simply_typed env (Abs t) (arr T1 T2)
| App_rule : forall t1 t2 T1 T2, simply_typed env t1 (arr T1 T2) -> simply_typed env t2 T1 -> simply_typed env (App t1 t2) T2.

Fixpoint C (A : simple_type) (M : lambda) : Prop :=
   simply_typed nil M A /\
   match A with
   | tp => strongly_normalize M
   | arr A B => forall N, C A N -> C B (App M N)
   end.

Lemma C_sn : forall A M, C A M -> strongly_normalize M.
Proof.
  induction A; intros M (H1, H2).
  assumption.
  
Qed.