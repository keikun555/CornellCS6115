(* Propositional reasoning *)
Lemma False_example (P: Prop): False -> P.
Proof.
  intros HFalse.
  destruct HFalse.
Qed.

Lemma True_example (P: Prop): P -> P /\  True.
Proof.
  intros.
  split.
  - apply H.
  - constructor.
Qed.

Lemma And_example: forall (P Q : Prop), P /\ Q -> Q /\ P.
Proof.
  intros.
  destruct H as [HP HQ].
  split.
  - apply HQ.
  - apply HP.
Qed.

Lemma Or_example: forall (P Q R : Prop), P \/ Q -> (P -> R) /\ (Q -> R) -> R.
Proof.
  intros P Q R HOr HAnd.
  destruct HAnd as [HPR HQR].
  destruct HOr.
  - apply HPR.
    apply H.
  - apply HQR.
    apply H.
Qed.

Lemma Not_example (P Q: Prop) : ~(P\/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  - unfold not.
    intros HP.
    unfold not in H.
    apply H.
    left.
    apply HP.
  - unfold not.
    intros HQ.
    unfold not in H.
    apply H.
    right.
    apply HQ.
Qed.

(* Does not work because it needs excluded middle, needs to be constructive and this is not *)
Lemma Not_non_example (P Q: Prop) : ~(P/\Q) -> ~P\/~Q.
Proof.
  intros.
  left.
  intros HP.
  apply H.
Abort.

