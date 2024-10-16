Require Import List.

(* Useful tactics for simplifying equalities *)
Ltac simpeq := repeat match goal with
  | _ => congruence || (progress subst)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  end.

Ltac inv H := inversion H; clear H; simpeq.

Require Import String.

Inductive expr : Type :=
  | Var : string -> expr
  | Lam : string -> expr -> expr
  | App : expr -> expr -> expr
  | Zero : expr
  | Succ : expr -> expr
  | Rec : expr -> expr -> expr -> expr.

Fixpoint subst (x : string) (v : expr) (e : expr) :=
  match e with
  | Var y => if string_dec x y then v else Var y
  | Lam y e' => Lam y (if string_dec x y then e' else subst x v e')
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | Zero => Zero
  | Succ e => Succ (subst x v e)
  | Rec e1 e2 e3 => Rec (subst x v e1) (subst x v e2) (subst x v e3)
  end.

Inductive value : expr -> Prop :=
  | Zero_value : value Zero
  | Succ_value e : value e -> value (Succ e)
  | Lam_value x e : value (Lam x e).

Inductive step : expr -> expr -> Prop :=
  | App_step x e v:
      step (App (Lam x e) v) (subst x v e)
  | Rec_Zero_step e1 e2 :
      value e1 -> value e2 ->
      step (Rec Zero e1 e2) e1
  | Rec_Succ_step v e1 e2 :
      value e1 -> value e2 ->
      step (Rec (Succ v) e1 e2) (Rec v (App e2 e1) e2)
  | App_step_1 e e' e2:
      step e e' ->
      step (App e e2) (App e' e2)
  | App_step_2 e e' e1:
      step e e' ->
      step (App e1 e) (App e1 e')
  | Succ_step_1 e e' :
      step e e' ->
      step (Succ e) (Succ e')
  | Rec_step_1 e e' e2 e3 :
      step e e' ->
      step (Rec e e2 e3) (Rec e' e2 e3)
  | Rec_step_2 e e' e1 e3 :
      step e e' ->
      step (Rec e1 e e3) (Rec e1 e' e3)
  | Rec_step_3 e e' e1 e2 :
      step e e' ->
      step (Rec e1 e2 e) (Rec e1 e2 e').

Inductive ty :=
  | Nat : ty
  | Fun : ty -> ty -> ty.

Check (Fun Nat Nat).

Definition insert {A:Type} (x : string) (v : A) (f : string -> option A) : (string -> option A) :=
  fun y => if string_dec x y then Some v else f y.

Inductive typed : (string  -> option ty) -> expr -> ty -> Prop :=
  | Var_typed Gamma x t :
      Gamma x = Some t ->
      typed Gamma (Var x) t
  | Lam_typed Gamma a b e x: 
      typed (insert x a Gamma) e b ->
      typed Gamma (Lam x e) (Fun a b)
  | App_typed Gamma e1 e2 a b:
      typed Gamma e1 (Fun a b) ->
      typed Gamma e2 a ->
      typed Gamma (App e1 e2) b
  | Zero_typed Gamma : 
      typed Gamma Zero Nat
  | Succ_typed Gamma e :
      typed Gamma e Nat ->
      typed Gamma (Succ e) Nat
  | Rec_typed Gamma e1 e2 e3 A :
      typed Gamma e1 Nat ->
      typed Gamma e2 A ->
      typed Gamma e3 (Fun A A) ->
      typed Gamma (Rec e1 e2 e3) A.

Definition empty {A} : string -> option A := fun x => None.

Lemma progress e t :
  typed empty e t -> value e \/ exists e', step e e'.
Proof.
  intros H.
  remember empty as Gamma.
  induction H.
  - exfalso. subst. unfold empty in *. discriminate.
  - left. constructor.
  - right. destruct IHtyped1; auto.
    + inv H1; inv H.
      destruct IHtyped2; auto.
      * eauto using step.
      * destruct H. eauto using step.
    + destruct H1. eauto using step.
  - eauto using value.
  - destruct IHtyped; auto.
    + eauto using value.
    + destruct H0. eauto using step.
  - destruct IHtyped1 as [?|[]]; eauto using step.
    destruct IHtyped2 as [?|[]]; eauto using step.
    destruct IHtyped3 as [?|[]]; eauto using step.
    inv H2; inv H; eauto using step.
Qed.

Lemma weakening Gamma v t :
  typed empty v t ->
  typed Gamma v t.
Proof.
Admitted.

Lemma insert_insert x0 a0 a (Gamma0 : string -> option ty):
  insert x0 a0 (insert x0 a Gamma0) = insert x0 a0 Gamma0.
Proof.
Admitted.

Lemma insert_commute x x0 a a0 (Gamma0 : string -> option ty) :
  x <> x0 ->
  insert x0 a0 (insert x a Gamma0) =
  insert x a (insert x0 a0 Gamma0).
Proof.
Admitted.

Lemma subst_typed Gamma v a x e t :
  typed empty v a ->
  typed (insert x a Gamma) e t ->
  typed Gamma (subst x v e) t.
Proof.
  intros Hv He.
  remember (insert x a Gamma) as Gamma'.
  revert Gamma HeqGamma'.
  induction He; intros; subst; simpl.
  - unfold insert in H. destruct string_dec.
    + simpeq. eapply weakening. auto.
    + eauto using typed.
  - econstructor. destruct string_dec.
    + subst. rewrite insert_insert in He. eapply He.
    + eapply IHHe. apply insert_commute. auto.
  - eauto using typed.
  - eauto using typed.
  - eauto using typed.
  - eauto using typed.
Qed.

Lemma preservation e e' t :
  typed empty e t ->
  step e e' ->
  typed empty e' t.
Proof.
  intros Ht Hs.
  revert t Ht.
  induction Hs; intros; inv Ht; eauto using typed.
  - inv H2. eapply subst_typed; eauto.
  - inv H5. eauto using typed.
Qed.
    

