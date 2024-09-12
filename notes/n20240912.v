Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Lia.
Require Import Arith.

Fixpoint is_even (n: nat) : Prop :=
  match n with
  | 0 => True
  | S n' => 
      match n' with
      | 0 => False
      | S n'' => is_even n''
      end
  end.

(* constructor simplifies *)
Lemma four_even : is_even 4.
Proof.
  constructor.
Qed.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Check even.

Lemma four_is_even : even 4.
Proof.
  apply even_SS.
  apply even_SS.
  apply even_0.
Qed.

Lemma even_plus_4 : forall n, even n -> even (4 + n).
Proof.
  intros.
  simpl.
  apply even_SS.
  apply even_SS.
  apply H.
Qed.

Lemma even_minus_two : forall n, even (S (S n)) -> even n.
Proof.
  intros.
  inversion H.
  subst.
  apply H1.
Qed.

Lemma even_minus_two' : forall n m, m = S (S n) -> even m -> even n.
Proof.
  intros.
  destruct H0.
  - inversion H.
  - inversion H.
    subst.
    apply H0.
Qed.

Lemma one_is_not_even : ~ even 1.
Proof.
  intros H.
  inversion H.
Qed.

Lemma three_is_not_even : ~ even 3.
Proof.
  intros H.
  inversion H.
  apply one_is_not_even.
  apply H1.
Qed.

Lemma double_even : forall n, even (2 * n).
Proof.
  intros.
  induction n.
  - simpl.
    apply even_0.
  - replace (2 * S n) with (2 + 2 * n) by lia.
    apply even_SS.
    apply IHn.
Qed.

Lemma even_double n: even n -> exists k, n = 2 * k.
Proof.
  intros H.
  induction n.
  - exists 0.
    reflexivity.
  - Admitted.

Lemma even_double_take2 n: even n -> exists k, n = 2 * k.
Proof.
  intros H.
  induction n using lt_wf_ind.
  destruct n.
  - exists 0.
    reflexivity.
  - destruct n.
    + inversion H.
    + inversion H.
      subst.
      clear H.
      destruct (H0 n) as [k' H'].
      * lia.
      * apply H2.
      * subst.
        exists (S k').
        lia.
Qed.

Lemma even_double_better n : even n -> exists k, n = 2 * k.
Proof.
  intros H.
  induction H.
  - exists 0.
    reflexivity.
  - destruct IHeven.
    + exists (S x).
      subst.
      lia.
Qed.

