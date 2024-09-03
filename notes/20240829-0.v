Definition Fals := forall P: Prop, P.

Lemma exfalso (P: Prop) : Fals -> P.
Proof.
  intros.
  unfold Fals in H.
  apply H.
Qed.

Lemma False_correct : Fals <-> False.
Proof.
  unfold "<->".
  split.
  - intros H.
    apply exfalso.
    apply H.
  - intros H.
    destruct H.
Qed.

Definition Tru := Fals -> Fals.
Definition Tru' := forall P, P -> P.

Lemma Tru_correct : Tru <-> True.
Proof.
  split.
  - intros H.
    constructor.
  - intros H.
    unfold Tru.
    intros H'.
    apply H'.
Qed.

Definition and (P Q : Prop) :=
  forall R : Prop, (P -> Q -> R) -> R.

Lemma and_left P Q : and P Q -> P.
Proof.
  unfold and.
  intros H.
  apply H.
  intros H1 H2.
  apply H1.
Qed.

Lemma and_right P Q : and P Q -> Q.
Proof.
  unfold and.
  intros H.
  apply H.
  intros H1 H2.
  apply H2.
Qed.

Lemma and_intro (P Q : Prop) : P -> Q -> and P Q.
Proof.
  intros HP HQ.
  unfold and.
  intros R Himp.
  apply Himp.
  - apply HP.
  - apply HQ.
Qed.

Lemma and_correct (P Q : Prop) :
  and P Q <-> P /\ Q.
Proof.
  split.
  - intros H.
    split.
    (* + apply (and_left P Q). *)
    (* + apply (and_left _ Q). *)
    + eapply and_left.
      apply H.
    + eapply and_right.
      apply H.
  - intros H.
    destruct H as [H1 H2].
    apply and_intro.
    + apply H1.
    + apply H2.
Qed.
Print and_correct.

