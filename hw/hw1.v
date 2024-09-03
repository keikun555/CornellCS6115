(** *Homework 1: Logic and Tactics* *)

(* For EX2 through EX6, give an explicit proof terms for the given
 * proposition, following EX1 as an example. Specifically, you should
 * replace the ". Admitted" with ":= <exp>" where "<exp>" is an
 * expression of appropriate type. You should *not* use tactics in
 * your solutions.
 *)

Definition EX1 : forall (A B C : Prop),
  ~(A \/ B) -> B -> C :=
  fun (A B C:Prop) (H : ~ (A \/ B)) (HB : B) =>
    match H (or_intror HB) with
    end.

Definition EX2 : forall (A B C : Prop),
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C) := 
  fun (A B C:Prop) (H : A /\ (B \/ C)) =>
    match H with
    | conj HA (or_introl HB) => or_introl (conj HA HB)
    | conj HA (or_intror HC) => or_intror (conj HA HC)
    end.


Definition EX3 : forall (A B C D : Prop),
  (B /\ (B -> C /\ D)) -> D :=
  fun (A B C D : Prop) (H: B /\ (B -> C /\ D)) => 
    match H with
    | conj HB H' => match H' HB with
                    | conj HC HD => HD
                    end
    end.

Definition EX4 : forall (A : Prop),
  A <-> A := 
  fun (A : Prop) => conj (fun A => A) (fun A => A).

Definition EX5 : forall (A B:Prop),
  (A <-> B) <-> (B <-> A) :=
  fun (A B : Prop) => conj 
    (fun (H : A <-> B) => match H with
                          | conj HAB HBA => conj HBA HAB 
                          end)
    (fun (H : B <-> A) => match H with
                          | conj HBA HAB => conj HAB HBA
                          end).

Definition EX6 : forall (A B C:Prop),
  (A <-> B) -> (B <-> C) -> (A <-> C) :=
  fun (A B C : Prop) (HAiffB : A <-> B) => fun (HBiffC : B <-> C) => conj
  (fun A => match HAiffB with
            | conj HAB HBA => match HBiffC with
                              | conj HBC HCB => HBC (HAB A) end
            end)
  (fun C => match HAiffB with
            | conj HAB HBA => match HBiffC with
                              | conj HBC HCB => HBA (HCB C) end
            end).

(* Karma problem: the law of the excluded middle is not provable in
  Coq, without adding another axiom.  Try to prove it and see where you
  get stuck. Describe your attempts... *)
Definition LOEM : forall (A : Prop),
  (A \/ ~ A). Admitted. (* TODO *)

(* Now, for each EX1T through EX6T, give a proof using tactics. Do not
 * use tactics like [firstorder] and [tauto] that automatically solve
 * first-order propsitions. Instead, stick to the basic tactics used in
 * lecture: [intros, apply, destruct, unfold, split, left, right, etc.]
 *)

Lemma Not_example (P Q : Prop) : ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  split.
  - unfold not.
    intros HP.
    apply H.
    left.
    apply HP.
  - unfold not.
    intros HQ.
    apply H.
    right.
    apply HQ.
Qed.
Print Not_example.

Definition EX1T { A B C : Prop } :
  ~(A \/ B) -> B -> C.
Proof.
  intros.
  destruct H.
  right.
  apply H0.
Qed.

Definition EX2T { A B C : Prop } :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  intros.
  destruct H.
  destruct H0.
  - left.
    constructor.
    apply H.
    apply H0.
  - right.
    constructor.
    apply H.
    apply H0.
Qed.

Definition EX3T { A B C D : Prop } :
  (B /\ (B -> C /\ D)) -> D.
Proof.
  intros.
  destruct H.
  apply H0 in H.
  destruct H.
  apply H1.
Qed.

(* For this next exercise, you'll need to figure out what [<->] 
 * means and how to work with it. *)

Definition EX4T { A : Prop } :
  A <-> A.
Proof.
  split.
  - intros.
    apply H.
  - intros.
    apply H.
Qed.

Definition EX5T {A B:Prop} :
  (A <-> B) <-> (B <-> A).
Proof.
  split.
  - intros.
    split.
    + destruct H.
      apply H0.
    + destruct H.
      apply H.
  - intros.
    split.
    + destruct H.
      apply H0.
    + destruct H.
      apply H.
Qed.

Definition EX6T {A B C:Prop} :
  (A <-> B) -> (B <-> C) -> (A <-> C).
Proof.
  intros.
  destruct H.
  destruct H0.
  split.
  - intros.
    apply H in H3.
    apply H0 in H3.
    apply H3.
  - intros.
    apply H2 in H3.
    apply H1 in H3.
    apply H3.
Qed.
