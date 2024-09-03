Definition or (P Q : Prop) : Prop := forall R : Prop, (P -> R) -> (Q -> R) -> R.
(* Definition and (P Q : Prop) := *)
(*   forall R : Prop, (P -> Q -> R) -> R. *)

Lemma or_intro_left P Q : P -> or P Q.
Proof.
  intros HP.
  unfold or.
  intros R H1 H2.
  apply H1.
  apply HP.
Qed.


Lemma or_intro_right P Q : Q -> or P Q.
Proof.
  intros HP.
  unfold or.
  intros R H1 H2.
  apply H2.
  apply HP.
Qed.

Lemma or_elim P Q (R : Prop) : or P Q -> (P -> R) -> (Q -> R) -> R.
Admitted.

Lemma or_correct P Q : P \/ Q <-> or P Q.
Proof.
  split.
  - intros H. destruct H.
    + eapply or_intro_left. apply H.
    + eapply or_intro_right. apply H.
  - intros H.
    unfold or in H.
    apply H.
    + intros HP. left. apply HP.
    + intros HQ. right. apply HQ.
Qed.

