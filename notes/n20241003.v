(*|
=======================
Lecture 11: Termination
=======================

In this lecture, we will prove that the simply typed lambda calculus is terminating.
We also add natural numbers to the language.
|*)

(*| 
  Here, we demonstrate the use of the Rec operator in Coq.
  Our language will also have such a Rec operator.
  The Rec operator is powerful enough to define addition, multiplication, and exponentiation.
|*)

Fixpoint rec {A} (n : nat) (x : A) (f : A -> A) : A :=
  match n with
  | 0 => x
  | S n => f (rec n x f)
  end.

Definition double n := rec n 0 (fun x => S (S x)).

Compute (double 3).

Definition add n m := rec n m (fun x => S x).

Compute (add 3 4).

Definition mul n m := rec n 0 (fun x => add m x).

Compute (mul 3 4).

Definition pow n m := rec m 1 (fun x => mul n x).

Compute (pow 2 3).

(*|
  When using rec with A := nat, we can only do primitive recursion.
  By using the rec operator at type A := nat -> nat, we can go beyond, 
  and define the Ackermann function.
|*)

Definition ack m := rec m S (fun f => fun n => rec (S n) 1 f).

Compute (ack 3 3).




(* Useful tactics for simplifying equalities *)
Ltac simpeq := repeat match goal with
  | _ => congruence || (progress subst)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  end.

Ltac inv H := inversion H; clear H; simpeq.


(* Utilities on environments/contexts *)
Require Import String.

Definition empty {T} : string -> option T := fun _ => None.

Definition insert {T} (x : string) (t : T) (f : string -> option T) : string -> option T :=
  fun x' => if string_dec x x' then Some t else f x'.

Definition delete {T} (x : string) (f : string -> option T) : string -> option T :=
  fun x' => if string_dec x x' then None else f x'.

(* fun_eq lets us avoid the function extensionality axiom *)

Definition fun_eq {A B} (f g : A -> B) :=
  forall x, f x = g x.

Notation "f == g" := (fun_eq f g) (at level 70).

Ltac simpfun := 
  (unfold fun_eq, delete, insert in *);
  (repeat (solve [eauto] || destruct string_dec || simpeq || intro)).

(* 
We can prove all the following lemmas using simpfun.
Now that we have simpfun, we don't even need the lemmas, we can just do simpfun.
*)

Lemma fun_eq_refl {A B} (f : A -> B) :
  f == f.
Proof.
  simpfun.
Defined.

Lemma fun_eq_sym {A B} (f g : A -> B) :
  f == g -> g == f.
Proof.
  simpfun.
Defined.

Lemma delete_insert {T} x v (env : string -> option T) :
  delete x (insert x v env) == delete x env.
Proof.
  simpfun.
Defined.

Lemma insert_delete {T} x v (env : string -> option T) :
  insert x v (delete x env) == insert x v env.
Proof.
  simpfun.
Defined.

Lemma delete_delete {T} x (env : string -> option T) :
  delete x (delete x env) == delete x env.
Proof.
  simpfun.
Defined.

Lemma delete_delete_comm {T} x y (env : string -> option T) :
  x <> y ->
  delete x (delete y env) == delete y (delete x env).
Proof.
  simpfun.
Defined.

Lemma delete_insert_comm {T} x y v (env : string -> option T) :
  x <> y ->
  delete x (insert y v env) == insert y v (delete x env).
Proof.
  simpfun.
Defined.




(*|
Syntax
------
|*)


Inductive expr :=
  | Var (x : string)
  | Lam (x : string) (e : expr)
  | App (e1 e2 : expr)
  | Zero : expr
  | Succ (e : expr)
  | Rec (e1 e2 e3 : expr).


(*|
Typing
------
|*)

Inductive ty :=
  | Nat : ty
  | Fun (t1 t2 : ty).

Definition ctx := string -> option ty.

Inductive typed : ctx -> expr -> ty -> Prop :=
  | Typed_Var (x : string) (t : ty) (Gamma : ctx) :
    Gamma x = Some t ->
    typed Gamma (Var x) t
  | Typed_Lam (x : string) (e : expr) (t1 t2 : ty) (Gamma : ctx) :
    typed (insert x t1 Gamma) e t2 ->
    typed Gamma (Lam x e) (Fun t1 t2)
  | Typed_App (e1 e2 : expr) (t1 t2 : ty) (Gamma : ctx) :
    typed Gamma e1 (Fun t1 t2) ->
    typed Gamma e2 t1 ->
    typed Gamma (App e1 e2) t2
  | Typed_Zero (Gamma : ctx) :
    typed Gamma Zero Nat
  | Typed_Succ (e : expr) (Gamma : ctx) :
    typed Gamma e Nat ->
    typed Gamma (Succ e) Nat
  | Typed_Rec (e1 e2 e3 : expr) (Gamma : ctx) (t : ty) :
    typed Gamma e1 Nat ->
    typed Gamma e2 t ->
    typed Gamma e3 (Fun t t) ->
    typed Gamma (Rec e1 e2 e3) t.

(*|
Semantics
---------
|*)

(*| Substitution |*)

Fixpoint subst (x : string) (v : expr) (e : expr) : expr :=
  match e with
  | Var y => if string_dec x y then v else e
  | Lam y e => Lam y (if string_dec x y then e else subst x v e)
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | Zero => Zero
  | Succ e => Succ (subst x v e)
  | Rec e1 e2 e3 => Rec (subst x v e1) (subst x v e2) (subst x v e3)
  end.

(*| Values |*)

Inductive value : expr -> Prop :=
  | Val_Lam (x : string) (e : expr) :
    value (Lam x e)
  | Val_Zero :
    value Zero
  | Val_Succ (e : expr) :
    value e ->
    value (Succ e).

(*| Small-step Semantics |*)

Inductive step : expr -> expr -> Prop :=
  | Step_App1 (e1 e1' e2 : expr) :
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
  | Step_App2 (e1 e2 e2' : expr) :
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
  | Step_AppLam (x : string) (v e : expr) :
    value v ->
    step (App (Lam x e) v) (subst x v e)
  | Step_Succ1 (e e' : expr) :
    step e e' ->
    step (Succ e) (Succ e')
  | Step_Rec1 (e1 e1' e2 e3 : expr) :
    step e1 e1' ->
    step (Rec e1 e2 e3) (Rec e1' e2 e3)
  | Step_Rec2 (e1 e2 e2' e3 : expr) :
    step e2 e2' ->
    step (Rec e1 e2 e3) (Rec e1 e2' e3)
  | Step_Rec3 (e1 e2 e3 e3' : expr) :
    step e3 e3' ->
    step (Rec e1 e2 e3) (Rec e1 e2 e3')
  | Step_RecZero (e2 e3 : expr) :
    value e2 -> value e3 ->
    step (Rec Zero e2 e3) e2
  | Step_RecSucc (e1 e2 e3 : expr) :
    value e1 -> value e2 -> value e3 ->
    step (Rec (Succ e1) e2 e3) (Rec e1 (App e3 e2) e3).

(*|
Termination
-----------
|*)

Inductive rtc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | rtc_refl (x : A) : rtc R x x
  | rtc_once (x y z : A) : R x y -> rtc R y z -> rtc R x z.

Definition terminates (e : expr) :=
  exists e', rtc step e e' /\ value e'.


(* Lemma terimination e t: *)
(*   typed empty e t -> terminates e. *)
(* Proof. *)
(*   intros H. remember empty as Gamma. *)
(*   induction H. *)
(*   - subst. unfold empty in *. simpeq. *)
(*   - exists (Lam x e). split. *)
(*     + eapply rtc_refl. *)
(*     + constructor. *)
(*   - admit. *)
(*   - exists Zero. split. *)
(*     + eapply rtc_refl. *)
(*     + constructor. *)
(*   - unfold terminates in *. *)
(*     destruct (IHtyped HeqGamma) as [e' [Hstep Hval]]. *)
(*     assert (typed Gamma e' Nat) by admit. *)
(*     exists (Succ e'). *)
(*     split. *)
(*     + admit. *)
(*     + constructor. auto. *)


(*|
Termination proof
-----------------
|*)

(* Main proof: semantic typing of values and expressions *)

Fixpoint nat_to_expr (n : nat) : expr :=
  match n with
  | 0 => Zero
  | S n => Succ (nat_to_expr n)
  end.

Definition closed e := forall x v, subst x v e = e.

Fixpoint value_ok (e : expr) (t : ty) :=
  match t with
  | Nat => exists n, e = nat_to_expr n
  | Fun t1 t2 =>
      closed e /\
      exists x ebody, e = Lam x ebody /\
        forall v, value_ok v t1 ->
          exists e', rtc step (subst x v ebody) e' /\ value_ok e' t2
  end.

Definition expr_ok (e : expr) (t : ty) :=
  exists e', rtc step e e' /\ value_ok e' t.


(* Helper lemmas about steps, value_ok, and expr_ok *)

Lemma rtc_trans {A} (R : A -> A -> Prop) x y z :
  rtc R x y ->
  rtc R y z ->
  rtc R x z.
Proof.
  induction 1; eauto using rtc_once.
Defined.

Lemma rtc_step_Succ e e' :
  rtc step e e' ->
  rtc step (Succ e) (Succ e').
Proof.
  induction 1; eauto using rtc_refl, rtc_once, Step_Succ1.
Defined.

Lemma rtc_step_Rec e1 e1' e2 e2' e3 e3' :
  rtc step e1 e1' ->
  rtc step e2 e2' ->
  rtc step e3 e3' ->
  rtc step (Rec e1 e2 e3) (Rec e1' e2' e3').
Proof.
  induction 1; eauto using rtc_once, Step_Rec1.
  induction 1; eauto using rtc_once, Step_Rec2.
  induction 1; eauto using rtc_once, Step_Rec3.
  eapply rtc_refl.
Defined.

Lemma rtc_step_App e1 e1' e2 e2' :
  rtc step e1 e1' ->
  rtc step e2 e2' ->
  rtc step (App e1 e2) (App e1' e2').
Proof.
  induction 1; eauto using rtc_once, Step_App1.
  induction 1; eauto using rtc_once, Step_App2.
  eapply rtc_refl.
Defined.

Lemma expr_ok_step e e' t :
  rtc step e e' ->
  expr_ok e' t ->
  expr_ok e t.
Proof.
  intros Hstep [e'' [Hrtc Hval]].
  exists e''. split; eauto using rtc_trans.
Defined.

Lemma value_ok_value v t :
  value_ok v t -> value v.
Proof.
  destruct t; simpl; intros H.
  - destruct H as [n ->].
    induction n; simpl; constructor; auto.
  - destruct H as [Hcloseded [x [ebody [-> H]]]].
    constructor.
Defined.

Lemma value_ok_expr_ok v t :
  value_ok v t ->
  expr_ok v t.
Proof.
  intros H. exists v. split; auto.
  eapply rtc_refl.
Defined.

Lemma nat_to_expr_value n :
  value (nat_to_expr n).
Proof.
  induction n; simpl; constructor; auto.
Defined.

Lemma value_ok_App v1 v2 t1 t2 :
  value_ok v1 (Fun t1 t2) ->
  value_ok v2 t1 ->
  expr_ok (App v1 v2) t2.
Proof.
  intros Hv1 Hv2.
  simpl in *.
  destruct Hv1 as [Hcloseded [x [ebody [-> H]]]].
  eapply expr_ok_step.
  { eapply rtc_once; [apply Step_AppLam | apply rtc_refl]; eauto using value_ok_value. }
  eapply H. auto.
Defined.

(* Lemma termination Gamma e t : *)
(*   typed Gamma e t -> expr_ok e t. *)
(* Proof. *)
(*   intros H. *)
(*   induction H. *)
(*   - admit. *)
(*   - unfold expr_ok. *)
(*     exists (Lam x e). *)
(*     split. { eapply rtc_refl. } *)
(*     simpl. *)
(*     split. admit. *)
(*     eexists. eexists. split. eauto. *)
(*     unfold expr_ok in IHtyped. *)
(*   - unfold expr_ok in IHtyped1, IHtyped2. *)
(*     destruct IHtyped1 as [e1' [Hstep1 Hval1]]. *)
(*     destruct IHtyped2 as [e2' [Hstep2 Hval2]]. *)
(*     eapply value_ok_App; eauto. *)

Lemma expr_ok_rec n v1 v2 t :
  value_ok v1 t ->
  value_ok v2 (Fun t t) ->
  expr_ok (Rec (nat_to_expr n) v1 v2) t.
Proof.
  intros Hv1 Hv2.
  revert v1 Hv1.
  induction n; intros; simpl.
  - eapply expr_ok_step.
    { eapply rtc_once; [apply Step_RecZero | apply rtc_refl]; eauto using value_ok_value. }
    eapply value_ok_expr_ok. eauto.
  - eapply expr_ok_step.
    { eapply rtc_once; [apply Step_RecSucc | apply rtc_refl]; eauto using nat_to_expr_value, value_ok_value. }
    assert (expr_ok (App v2 v1) t).
    { eapply value_ok_App; eauto. }
    destruct H as [e' [Hstep Hval]].
    eapply expr_ok_step.
    { eapply rtc_step_Rec; eauto; eauto using rtc_refl. }
    eauto.
Defined.

Lemma value_ok_closed v t :
  value_ok v t ->
  closed v.
Proof.
  intros H.
  destruct t; simpl in *.
  - destruct H as [n ->].
    intros ??. induction n; simpl; auto. rewrite IHn. auto.
  - destruct H. auto.
Defined.

(* Environments and multi-substitutions *)

Definition env := string -> option expr.

Fixpoint subst_map (env : env) (e : expr) : expr :=
  match e with
  | Var x =>
      match env x with
      | Some v => v
      | None => e
      end
  | Lam x e => Lam x (subst_map (delete x env) e)
  | App e1 e2 => App (subst_map env e1) (subst_map env e2)
  | Zero => Zero
  | Succ e => Succ (subst_map env e)
  | Rec e1 e2 e3 => Rec (subst_map env e1) (subst_map env e2) (subst_map env e3)
  end.

Lemma subst_map_eq env1 env2 e :
  env1 == env2 ->
  subst_map env1 e = subst_map env2 e.
Proof.
  revert env1 env2. induction e; intros; simpl; try f_equal; eauto.
  - rewrite ?H. auto.
  - eapply IHe. simpfun.
Defined.

Lemma subst_map_empty e :
  subst_map empty e = e.
Proof.
  induction e; simpl; rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  f_equal. assert (delete x empty == (empty : env)) by simpfun.
  erewrite subst_map_eq; eauto.
Defined.

Lemma subst_subst_map_1 Gamma env e x v t :
  typed Gamma e t ->
  (forall x v, env x = Some v -> closed v) ->
  Gamma x = None \/ env x <> None ->
  subst x v (subst_map env e) = subst_map env e.
Proof.
  intros H. revert env. induction H; intros; simpl;
  try solve [rewrite ?IHtyped, ?IHtyped1, ?IHtyped2, ?IHtyped3; auto].
  - destruct (env0 x0) eqn:E.
    + eapply H0. eauto.
    + simpl. destruct string_dec; simpeq.
      destruct H1; simpeq.
  - destruct string_dec; simpeq. f_equal.
    eapply IHtyped; simpfun.
Defined.

Lemma subst_subst_map_2 Gamma env e x v t :
  typed Gamma e t ->
  (forall x v, env x = Some v -> closed v) ->
  env x = None ->
  subst x v (subst_map env e) = subst_map (insert x v env) e.
Proof.
  intros H. revert env. induction H; intros; simpl;
  try solve [rewrite ?IHtyped, ?IHtyped1, ?IHtyped2, ?IHtyped3; auto].
  - unfold insert. destruct string_dec; simpeq.
    + rewrite H1. simpl. destruct string_dec; simpeq.
    + destruct (env0 x0) eqn:E; simpl; simpfun.
      eapply H0. eauto.
  - f_equal. simpfun.
    + apply subst_map_eq. simpfun.
    + rewrite IHtyped; eauto.
      * apply subst_map_eq. simpfun.
      * simpfun.
      * simpfun.
Defined.

(* Lemmas about environments *)

Definition env_ok (env : env) (Gamma : ctx) :=
  forall x, 
  match Gamma x, env x with
  | Some t, Some v => value_ok v t
  | None, None => True
  | _, _ => False
  end.

Lemma env_ok_insert x v t env Gamma :
  env_ok env Gamma ->
  value_ok v t ->
  env_ok (insert x v env) (insert x t Gamma).
Proof.
  intros Henv Hval x'.
  unfold insert. destruct string_dec; simpeq. apply Henv.
Defined.

Lemma env_ok_eq Gamma env1 env2 :
  env2 == env1 ->
  env_ok env1 Gamma ->
  env_ok env2 Gamma.
Proof.
  intros H12 H1 x. unfold fun_eq, env_ok in *. 
  specialize (H1 x). rewrite <- H12 in H1. eauto.
Defined.

Lemma env_ok_closed Gamma env e t :
  typed Gamma e t ->
  env_ok env Gamma ->
  closed (subst_map env e).
Proof.
  (* Introduce four things with coq naming *)
  (* Intros unfold intros unfold intros unfold intros unfold *)
  intros ????.
  eapply subst_subst_map_1; eauto.
  - intros. unfold env_ok in H0. specialize (H0 x0).
    rewrite H1 in H0. destruct Gamma; eauto using value_ok_closed. destruct H0.
  - unfold env_ok in H0. 
    destruct Gamma eqn:E; eauto.
    destruct env eqn:E'. { right. intro. simpeq. }
    specialize (H0 x).
    rewrite E in H0. rewrite E' in H0.
    destruct H0.
Defined.

(* Generalized termination proof *)

Theorem termination_general (Gamma : ctx) (env : env) (e : expr) (t : ty) :
  typed Gamma e t ->
  env_ok env Gamma ->
  expr_ok (subst_map env e) t.
Proof.
  intros Htyped.
  revert env.
  induction Htyped; intros env Henv.
  - unfold env_ok in Henv. simpl.
    specialize (Henv x). rewrite H in Henv.
    destruct env.
    + eapply value_ok_expr_ok. auto.
    + destruct Henv.
  - eapply value_ok_expr_ok.
    split. { eapply env_ok_closed; eauto using typed. }
    eexists _,_. simpl. split; [auto|].
    intros v Hv. erewrite subst_subst_map_2; eauto.
    + eapply IHHtyped.
      assert (Hinsert : insert x v (delete x env) == insert x v env) by simpfun.
      eapply env_ok_eq; eauto.
      apply env_ok_insert; auto.
    + intros. unfold env_ok in Henv.
      unfold delete in H. destruct string_dec; simpeq.
      specialize (Henv x0). rewrite H in Henv. destruct Gamma; [|destruct Henv].
      eapply value_ok_closed. eauto.
    + simpfun.
  - simpl.
    destruct (IHHtyped1 _ Henv) as [v1 [Hstep1 Hval1]].
    destruct (IHHtyped2 _ Henv) as [v2 [Hstep2 Hval2]].
    eapply expr_ok_step; eauto using rtc_step_App.
    eapply value_ok_App; eauto.
  - simpl. eexists. split. { apply rtc_refl. }
    simpl. exists 0. auto.
  - simpl. apply IHHtyped in Henv.
    destruct Henv as [e' [Hstep Hval]].
    exists (Succ e'). split.
    + eauto using rtc_step_Succ.
    + simpl in Hval. destruct Hval as [n ->].
      simpl. exists (S n). auto.
  - destruct (IHHtyped1 _ Henv) as [v1 [Hstep1 Hval1]].
    destruct (IHHtyped2 _ Henv) as [v2 [Hstep2 Hval2]].
    destruct (IHHtyped3 _ Henv) as [v3 [Hstep3 Hval3]].
    eapply expr_ok_step; eauto using rtc_step_Rec.
    simpl in Hval1. destruct Hval1 as [n1 ->].
    eapply expr_ok_rec; eauto.
Defined.

(* Final theorem *)

Theorem termination (e : expr) (t : ty) :
  typed empty e t ->
  terminates e.
Proof.
  intros Htyped.
  eapply (termination_general empty empty) in Htyped.
  - rewrite subst_map_empty in Htyped.
    destruct Htyped as [e' [Hstep Hval]].
    exists e'. split; auto.
    eapply value_ok_value. eauto.
  - constructor.
Defined.


(* Definition ack m := rec m S (fun f => fun n => rec (S n) 1 f). *)

Definition Ack := 
  Lam "m" (Rec (Var "m") (Lam "x" (Succ (Var "x")))
    (Lam "f" (Lam "n" (Rec (Succ (Var "n")) (Succ Zero) (Var "f"))))).

Lemma Ack_typed :
  typed empty Ack (Fun Nat (Fun Nat Nat)).
Proof.
  eauto 20 using typed.
Defined.

Definition ACK n m := App (App Ack (nat_to_expr n)) (nat_to_expr m).

Lemma nat_to_expr_typed n :
  typed empty (nat_to_expr n) Nat.
Proof.
  induction n; simpl; eauto using typed.
Defined.

Lemma ACK_typed n m :
  typed empty (ACK n m) Nat.
Proof.
  unfold ACK.
  eauto 20 using typed, Ack_typed, nat_to_expr_typed.
Defined.

Check ex_intro.

Compute (termination _ _ (ACK_typed 0 0)).

(* Better to define axioms and lemmas like this to see the proof terms like above *)
(* If you want the proofs to be runnable *)
