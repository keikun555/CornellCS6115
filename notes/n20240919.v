(*|
===============================
Lecture 8: Small-step semantics
===============================
|*)

(* Import necessary libraries *)
Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Arith.
Require Import Lia.

(* Helper function for string equality *)
Definition string_eq (x y : string) : {x = y} + {x <> y}.
Proof.
  destruct (String.eqb_spec x y); auto.
Defined.

(* Useful tactics for simplifying equalities *)
Ltac simpeq := repeat match goal with
  | _ => congruence || (progress subst) (* progress stops repeat forever *)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  end.

Ltac inv H := inversion H; clear H; simpeq.

(*|
Recap: arithmetic expressions
-----------------------------
|*)

(* Axiom for function extensionality *)
Axiom funext : forall {X Y: Type} (f g: X -> Y),
    (forall x, f x = g x) -> f = g.

(* Type abbreviation for environments *)
Definition env := string -> nat.

(* Definition of arithmetic expressions *)
Inductive expr : Type :=
  | Const : nat -> expr
  | Var : string -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr.

(* Evaluation function for expressions *)
Fixpoint eval (env : env) (e : expr) : nat :=
  match e with
  | Const n => n
  | Var x => env x
  | Plus e1 e2 => eval env e1 + eval env e2
  | Mult e1 e2 => eval env e1 * eval env e2
  | Minus e1 e2 => eval env e1 - eval env e2
  end.

(*|
Statements
----------
|*)

(* Definition of statements *)
Inductive stmt :=
  | Assign : string -> expr -> stmt
  | Seq : stmt -> stmt -> stmt
  | If : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt
  | Skip : stmt. (* For small-step semantics, we need Skip *)

(*|
Small-step semantics
--------------------
|*)

(* Small-step semantics for statements *)
Inductive small_step : env -> stmt -> env -> stmt -> Prop :=
  | small_Assign env x e :
    small_step env (Assign x e)
      (fun var =>
         if string_eq x var then
           eval env e
         else
           env var)
      Skip
  | small_Seq1 env s1 s1' s2 env' :
      small_step env s1 env' s1' ->
      small_step env (Seq s1 s2) env' (Seq s1' s2)
  | small_SeqSkip env s2 :
      small_step env (Seq Skip s2) env s2
  | small_IfTrue env e s1 s2 :
      eval env e <> 0 ->
      small_step env (If e s1 s2) env s1
  | small_IfFalse env e s1 s2 :
      eval env e = 0 ->
      small_step env (If e s1 s2) env s2
  | small_WhileTrue env e s :
      eval env e <> 0 -> (* <> means not equal *)
      small_step env (While e s) env (Seq s (While e s))
  | small_WhileFalse env e s :
      eval env e = 0 ->
      small_step env (While e s) env Skip.

(*|
Determinism
-----------
|*)

(* Proof of determinism for small-step semantics *)
Lemma small_step_deterministic env env1 env2 s s1 s2 :
  small_step env s env1 s1 ->
  small_step env s env2 s2 ->
  env1 = env2 /\ s1 = s2.
Proof.
  intros H1.
  (* revert takes a hypothesis and makes it into a goal with forall or something *)
  revert env2 s2.
  induction H1.
  - intros env2 s2 H2.
    inv H2.
    auto.
  - intros env2 s2' H2.
    inv H2.
    + edestruct IHsmall_step.
      * eauto.
      * simpeq. auto.
    + inv H1.
  - intros env2 s2' H2. inv H2. inv H5. auto.
  - intros env2 s2' H2. inv H2. auto.
  - intros env2 s2' H2. inv H2. auto.
  - intros env2 s2' H2. inv H2. auto.
  - intros env2 s2' H2. inv H2. auto.
Qed.

(* Tactic to invert small step hypotheses *)
Ltac inv_small_step :=
  match goal with
  | [ H : small_step _ _ _ _ |- _ ] => inv H
      (* (inv H; [|]) || (inv H; []) || (inv H; fail) *) 
      (* list matches number of subgoals *)
      (* inv only when there are <= 2 subgoals *)
  end.

Lemma small_step_deterministic' env env1 env2 s s1 s2 :
  small_step env s env1 s1 ->
  small_step env s env2 s2 ->
  env1 = env2 /\ s1 = s2.
Proof.
  intros H1. revert env2 s2.
  induction H1; intros; inv_small_step; eauto.
  - edestruct IHsmall_step.
    + eauto.
    + simpeq. auto.
  - inv_small_step.
  - inv_small_step.
Qed.

(*|
Progress
--------
|*)

(* Definition of progress *)
Definition progress (env : string -> nat) (s : stmt) : Prop :=
  exists env' s', small_step env s env' s'.

(* Tactic for destructing hypotheses *)
Ltac destr :=
  match goal with
  | [ H : ?P \/ ?Q |- _ ] => destruct H
  | [ H : exists _, _ |- _ ] => destruct H
  end.

(* Proof that all states either progress or are Skip *)
Lemma all_states_progress env s :
  progress env s \/ s = Skip.
Proof.
  induction s.
  - left.
    unfold progress.
    eauto using small_step.
  - left.
    (* unfold in both hypothesis and goals *)
    unfold progress in *.
    destruct IHs1.
    + destruct H as [ env' [ s' ] ].
      eauto using small_step.
    + simpeq.
      eauto using small_step.
  - left.
    destruct (Nat.eq_dec (eval env e) 0).
    unfold progress in *.
    eauto using small_step.
    unfold progress in *.
    eauto using small_step.
  - left.
    destruct (Nat.eq_dec (eval env e) 0).
    unfold progress in *.
    eauto using small_step.
    unfold progress in *.
    eauto using small_step.
  - right. reflexivity.
Qed.
  (* induction s; eauto; left; unfold progress in *; *) 
  (* do 9 try destr; simpeq; eauto using small_step; *)
  (* destruct (Nat.eq_dec (eval env e) 0); eauto using small_step. *)

(*|
Transitive closure
------------------
|*)

(* Definition of multi-step small-step semantics *)
(* Transitive closure relation *)
Inductive small_steps : env -> stmt -> env -> stmt -> Prop :=
  | small_steps_refl env s :
      small_steps env s env s
  | small_steps_step env env' env'' s s' s'' :
      small_step env s env' s' ->
      small_steps env' s' env'' s'' ->
      small_steps env s env'' s''.

(* Proof of transitivity for small_steps *)
Lemma small_steps_trans env s env' s' env'' s'' :
  small_steps env s env' s' ->
  small_steps env' s' env'' s'' ->
  small_steps env s env'' s''.
Proof.
  intros H1. induction H1; eauto using small_steps, small_step.
Qed.

Require Import Coq.Program.Equality.

(* Lemma: Skip doesn't change the environment *)
Lemma skip_id env env' s :
  small_steps env Skip env' s -> env' = env /\ s = Skip.
Proof.
  intros H. dependent induction H; auto.
  inv_small_step.
Qed.

(*| Multi-step determinism |*)
Lemma small_steps_deterministic env env1 env2 s :
  small_steps env s env1 Skip ->
  small_steps env s env2 Skip ->
  env1 = env2.
Proof.
  intros H. revert env2.
  dependent induction H; intros.
  - eapply skip_id in H as []. auto.
  - inv H1.
    + inv_small_step.
    + eapply small_step_deterministic in H as []; eauto. simpeq. eauto.
Qed.

(*|
Equivalence with big-step
-------------------------
|*)

(* Definition of big-step semantics *)
Inductive big_step : env -> stmt -> env -> Prop :=
  | big_Skip env :
      big_step env Skip env
  | big_Assign env x e :
    big_step env (Assign x e)
      (fun var =>
         if string_eq x var then
           eval env e
         else
           env var)
  | big_Seq env env' env'' s1 s2 :
      big_step env s1 env' ->
      big_step env' s2 env'' ->
      big_step env (Seq s1 s2) env''
  | big_IfTrue env env' e s1 s2 :
      eval env e <> 0 ->
      big_step env s1 env' ->
      big_step env (If e s1 s2) env'
  | big_IfFalse env env' e s1 s2 :
      eval env e = 0 ->
      big_step env s2 env' ->
      big_step env (If e s1 s2) env'
  | big_WhileTrue env env' env'' e s :
      eval env e <> 0 ->
      big_step env s env' ->
      big_step env' (While e s) env'' ->
      big_step env (While e s) env''
  | big_WhileFalse env e s :
      eval env e = 0 ->
      big_step env (While e s) env.

(* Lemma: small_steps for sequences *)
Lemma small_steps_Seq env s1 s2 env' s1' :
  small_steps env s1 env' s1' ->
  small_steps env (Seq s1 s2) env' (Seq s1' s2).
Proof.
  intros H. induction H; eauto using small_steps, small_step.
Qed.

(* Proof that big-step implies small-steps *)
Lemma big_step_small_step env s env' :
  big_step env s env' ->
  small_steps env s env' Skip.
Proof.
  intros H. induction H; 
  eauto 10 using small_steps, small_step, 
     small_steps_trans, small_steps_Seq.
Qed.

(* Lemma: single small-step preserves big-step *)
Lemma small_step_big_step env s env' s' env'' :
  small_step env s env' s' ->
  big_step env' s' env'' ->
  big_step env s env''.
Proof.
  intros H1 H2. revert env s H1. 
  induction H2; intros; inv H1; eauto using big_step.
Qed.

(* Proof that small-steps implies big-step *)
Lemma small_steps_big_step env s env' :
  small_steps env s env' Skip ->
  big_step env s env'.
Proof.
  intros H. dependent induction H; 
  eauto using big_step, small_step_big_step.
Qed.

(*|
Concurrency
-----------
|*)

(* Definition of concurrent statements *)
Inductive cstmt :=
  | CSkip : cstmt
  | CAssign : string -> expr -> cstmt
  | CSeq : cstmt -> cstmt -> cstmt
  | CIf : expr -> cstmt -> cstmt -> cstmt
  | CWhile : expr -> cstmt -> cstmt
  | CPar : cstmt -> cstmt -> cstmt.

(* Small-step semantics for concurrent statements *)
Inductive csmall_step : env -> cstmt -> env -> cstmt -> Prop :=
  | csmall_Assign env x e :
    csmall_step env (CAssign x e)
      (fun var =>
         if string_eq x var then
           eval env e
         else
           env var)
      CSkip
  | csmall_Seq1 env s1 s1' s2 env' :
      csmall_step env s1 env' s1' ->
      csmall_step env (CSeq s1 s2) env' (CSeq s1' s2)
  | csmall_SeqSkip env s2 :
      csmall_step env (CSeq CSkip s2) env s2
  | csmall_IfTrue env e s1 s2 :
      eval env e <> 0 ->
      csmall_step env (CIf e s1 s2) env s1
  | csmall_IfFalse env e s1 s2 :
      eval env e = 0 ->
      csmall_step env (CIf e s1 s2) env s2
  | csmall_WhileTrue env e s :
      eval env e <> 0 ->
      csmall_step env (CWhile e s) env (CSeq s (CWhile e s))
  | csmall_WhileFalse env e s :
      eval env e = 0 ->
      csmall_step env (CWhile e s) env CSkip
  | csmall_Par1 env s1 s1' s2 env' :
      csmall_step env s1 env' s1' ->
      csmall_step env (CPar s1 s2) env' (CPar s1' s2)
  | csmall_Par2 env s2 s2' s1 env' :
      csmall_step env s2 env' s2' ->
      csmall_step env (CPar s1 s2) env' (CPar s1 s2')
  | csmall_ParSkip1 env s2 :
      csmall_step env (CPar CSkip s2) env s2
  | csmall_ParSkip2 env s1 :
      csmall_step env (CPar s1 CSkip) env s1.

(*|
Evaluation contexts
-------------------
|*)

(* Definition of evaluation contexts *)
Inductive ctx : (cstmt -> cstmt) -> Type :=
  | CSeq1 s2 : ctx (fun x => CSeq x s2)
  | CPar1 s2 : ctx (fun x => CPar x s2)
  | CPar2 s1 : ctx (fun x => CPar s1 x).

(* Small-step semantics with contexts *)
Inductive ccsmall_step : env -> cstmt -> env -> cstmt -> Prop :=
  | ccsmall_Assign env x e :
    ccsmall_step env (CAssign x e)
      (fun var =>
         if string_eq x var then
           eval env e
         else
           env var)
      CSkip
  | ccsmall_SeqSkip env s2 :
      ccsmall_step env (CSeq CSkip s2) env s2
  | ccsmall_IfTrue env e s1 s2 :
      eval env e <> 0 ->
      ccsmall_step env (CIf e s1 s2) env s1
  | ccsmall_IfFalse env e s1 s2 :
      eval env e = 0 ->
      ccsmall_step env (CIf e s1 s2) env s2
  | ccsmall_WhileTrue env e s :
      eval env e <> 0 ->
      ccsmall_step env (CWhile e s) env (CSeq s (CWhile e s))
  | ccsmall_WhileFalse env e s :
      eval env e = 0 ->
      ccsmall_step env (CWhile e s) env CSkip
  | ccsmall_ParSkip1 env s2 :
      ccsmall_step env (CPar CSkip s2) env s2
  | ccsmall_ParSkip2 env s1 :
      ccsmall_step env (CPar s1 CSkip) env s1
  | ccsmall_Ctx K s1 s2 s1' s2' env env' :
      (* This is to make eauto work better *)
      ctx K -> s1' = K s1 -> s2' = K s2 -> 
      ccsmall_step env s1 env' s2 ->
      ccsmall_step env s1' env' s2'.

(*| Equivalence with previous small-step semantics |*)
Lemma csmall_step_ccsmall_step env1 s1 env2 s2 :
  csmall_step env1 s1 env2 s2 <->
  ccsmall_step env1 s1 env2 s2.
Proof.
  split; intros H.
  - induction H; eauto using ccsmall_step, ctx.
  - induction H; eauto using csmall_step. subst.
    inv H; eauto using csmall_step.
Qed.
