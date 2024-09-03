Inductive Nat :=
  | O : Nat
  | S : Nat -> Nat.

Definition zero := O.
Definition one := S O.
Definition two := S (S O).
Definition three := S (S (S O)).

Check two.
Print two.

(* Recursive functions use Fixpoint *)
Fixpoint add n m :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Check add.
Compute (add two three).
Compute (fun x => add two x).
Check O.
Check S.
Check Nat.

Lemma add_0_n n : add O n = n.
Proof.
  (* simpl. *)
  reflexivity.
  (* destruct n. *)
  (* - simpl. *)
  (*   reflexivity. *)
  (* - simpl. *)
  (*   reflexivity. *)
Qed.

Lemma add_Sr_m n m : add (S n) m = S (add n m).
Proof.
  simpl.
  reflexivity.
Qed.

Lemma add_assoc a b c : add (add a b) c = add a (add b c).
Proof.
  (* destruct a. *)
  (* - simpl. *)
  (*   reflexivity. *)
  (* - simpl. *)
  induction a.
  - reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.

Lemma add_n_0 n : add n O = n.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma add_n_Sm n m : add n (S m) = S (add n m).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Lemma add_comm n m : add n m = add m n.
Proof.
  induction n.
  - simpl.
    rewrite add_n_0.
    reflexivity.
  - simpl.
    rewrite add_n_Sm.
    (* rewrite -> add_n_Sm. *)
    (* rewrite <- add_n_Sm. *)
    rewrite IHn.
    reflexivity.
Qed.

Infix "+" := add.
Notation "0" := O.
Notation "1" := (S 0).
Notation "2" := (S 1).
Notation "3" := (S 2).

Compute 1 + 2.

Definition nat_eq n m :=
  match n with
  | 0 => m = 0
  | S n' => match m with
            | 0 => False
            | S m' => n' = m'
            end
  end.

Lemma nat_eq_eq n m : nat_eq n m -> n = m.
Proof.
  intros H.
  destruct n.
  - simpl in H. rewrite H. reflexivity.
  - simpl in H.
    destruct m.
    + destruct H.
    + rewrite H. reflexivity.
Qed.

Lemma S_not_0 n : S n = 0 -> False.
Proof.
  intros H.
  assert (nat_eq (S n) 0).
  - rewrite H. simpl. reflexivity.
  - simpl in H0. apply H0.
Qed.

Lemma add_0_inv n m :
  n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros H.
  destruct n.
  - simpl in H. rewrite H.
    split.
    + reflexivity.
    + reflexivity.
  - simpl in H.
    (* apply S_not_0 in H. *)
    (* destruct H. *)

    (* discriminate H. *)
    discriminate.
Qed.

Lemma S_inj n m : S n = S m -> n = m.
Proof.
  intros H.
  (* assert (nat_eq (S n) (S m)). *)
  (* - rewrite H. simpl. reflexivity. *)
  (* - simpl in H0. apply H0. *)
  injection H as H.
  apply H.
Qed.

Lemma foo n m : n = m -> S n = S m.
Proof.
  intros H.
  f_equal.
  apply H.
Qed.

Lemma bar n m : n = m -> n + 0 = m + 0.
Proof.
  intros H.
  f_equal.
  apply H.
Qed.

Fixpoint le n m :=
  match n with 
  | 0 => True
  | S n' =>
      match m with
      | 0 => False
      | S m' => le n' m'
      end
  end.

Compute le 0 1.
Compute le 1 0.

Lemma le_refl n : le n n.
Proof.
  induction n.
  - simpl. constructor.
  - simpl. apply IHn.
Qed.

Lemma le_trans n m k :
  le n m -> le m k -> le n k.
Proof.
  revert k m.
  induction n;
  intros k m H1 H2.
  - simpl in *. constructor.
  - simpl in *.
    destruct m.
    { destruct H1. }
    simpl in *.
    destruct k.
    { apply H2. }
    apply (IHn k m).
    + apply H1.
    + apply H2.
Qed.

Definition lt n m := le (S n) m.

Lemma strong_induction (P : Nat -> Prop) : 
  (forall n, (forall m, lt m n -> P m) -> P n) -> forall n, P n.
Proof.
  intros H n.
  apply H.
  induction n.
  - intros m H1. unfold lt in H1. simpl in H1. destruct H1.
  - intros m H1. unfold lt in H1. simpl in H1.
    apply H.
    intros m0 H2.
    apply IHn.
    unfold lt in H2.
    unfold lt.
    apply (le_trans (S m0) m n).
    + apply H2.
    + apply H1.
Qed.
