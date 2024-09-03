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
Definition EX2 { A B C : Prop } :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C). Admitted.

Definition EX3 { A B C D : Prop } :
  (B /\ (B -> C /\ D)) -> D. Admitted.

Definition EX4 { A : Prop } :
  A <-> A. Admitted.

Definition EX5 {A B:Prop} :
  (A <-> B) <-> (B <-> A). Admitted.

Definition EX6 {A B C:Prop} :
  (A <-> B) -> (B <-> C) -> (A <-> C). Admitted.

(* Karma problem: the law of the excluded middle is not provable in
  Coq, without adding another axiom.  Try to prove it and see where you
  get stuck. Describe your attempts... *)

(* Now, for each EX1T through EX6T, give a proof using tactics. Do not
 * use tactics like [firstorder] and [tauto] that automatically solve
 * first-order propsitions. Instead, stick to the basic tactics used in
 * lecture: [intros, apply, destruct, unfold, split, left, right, etc.]
 *)

Definition EX1T { A B C : Prop } :
  ~(A \/ B) -> B -> C. Admitted.

Definition EX2T { A B C : Prop } :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C). Admitted.

Definition EX3T { A B C D : Prop } :
  (B /\ (B -> C /\ D)) -> D. Admitted.

(* For this next exercise, you'll need to figure out what [<->] 
 * means and how to work with it. *)

Definition EX4T { A : Prop } :
  A <-> A. Admitted.

Definition EX5T {A B:Prop} :
  (A <-> B) <-> (B <-> A). Admitted.

Definition EX6T {A B C:Prop} :
  (A <-> B) -> (B <-> C) -> (A <-> C). Admitted.
