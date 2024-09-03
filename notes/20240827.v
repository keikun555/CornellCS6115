Inductive Bool := Type :=
  | true
  | false.

Check true.
Print true.
Check Bool.
Print Bool.

Definition negb (b:Bool) : Bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : Bool) : Bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2 : Bool) : Bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true false) = true.
Proof.
  reflexivity.
Qed.

Compute (negb true).

Theorem T1 : \forall (A:Prop), A -> A.
Proof.
  intros A Asm.
  apply Asm.
Qed.
Proof.
  intros.
  assumption.
Qed.

Check true = true.

Definition bogus : Prop := true = false.

Theorem bogus_proof_attempt : bogus.
Proof.
  unfold bogus.
Abort.
