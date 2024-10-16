(*|
============================
Lecture 14: Separation Logic
============================

Author
  Greg Morrisett, with modifications by the EPFL CS 628 and Cornell CS 6115 course staff.

License
  No redistribution allowed (usage by permission in CS 6115).

.. contents::

.. coq:: none
|*)

(*|
Using Hoare logic we can derive statements like this, which capture the
specification of the function that increments a variable::

   { x = n }
   inc(x)
   { x = n + 1}

We'd like to be able to use such statements to construct proofs of statements
that involve procedures like `inc()`, defined as follows:

  {x = n âˆ§ y = m }
  inc(x);
  inc(y);
  {x = n+1 âˆ§ y = m+1}

The problem is that we need an intermediate proposition that is stronger than
what the specification for `inc()` gives us directly. One approach is to somehow
say that things other than `x` aren't modified by the first increment.

There have been a number of attempts to extend the logic to support modular
reasoning about heaps and procedures. Of these, separation logic is probably
the most popular.

Separation logic has a similar structure to Hoare logic, but the meaning of
{P}c{Q} is different. Semantically, âˆ€h1, âˆ€h2, if P(h1), thenÂ running c in heap
(h1 â¨„ h2) yields a heap h3 = h4 â¨„ h2 where Q(h4). Note that by â¨„ here we 
mean disjoint union.

Specifications in separation logic generally have the following syntax::

    emp            the heap is empty
    x â†¦ v          the heap contains a single mapping from x to v
    P * Q          * is the _separating conjunction_ of separation logic.
                   Holds on heap h = h1 â¨„ h2 where P(h1) and Q(h2).
    P âˆ§ Q          Usual semantics
    P -* Q         The "magic wand" implication. Idea: a heap satisfies it 
                   if it satisfies Q when extended with some disjoint heap that
                   satisfies P. This is useful for weakest preconditions.

This is nice because the rules for assignment, consequence etc. still hold::

    {x â†¦ _ } x := v { x â†¦ v}

just like in standard Hoare Logic.
|*)

Require Import Eqdep.
Require Import Lia.
Require Import List.
Set Implicit Arguments.

Axiom proof_irrelevance : forall (P:Prop) (H1 H2:P), H1 = H2.

(*|
In this lecture, we will develop a separation logic for reasoning about
imperative Coq programs.  Separation logic gives us a crucial principle
for modularly reasoning about programs -- the *frame rule*.
|*)
Module FunctionalSepIMP.

  Definition ptr := nat.
  Definition ptr_eq := PeanoNat.Nat.eq_dec.
  Definition le_gt_dec := Arith.Compare_dec.le_gt_dec.
  
(*|
As a demonstration, let's fix the universe of storable types by giving some
names to a few standard types as well as an interpretation.
|*)
  Inductive stype : Set := 
  | Nat_t : stype
  | Pair_t : stype -> stype -> stype
  | Sum_t : stype -> stype -> stype
  | Fn_t : stype -> stype -> stype.

  Definition stype_eq (t1 t2:stype) : {t1=t2} + {t1<>t2}.
    decide equality.
  Defined.

  Fixpoint interp(t:stype) : Set := 
    (match t with 
       | Nat_t => nat
       | Pair_t t1 t2 => (interp t1) * (interp t2)
       | Sum_t t1 t2 => (interp t1) + (interp t2)
       | Fn_t t1 t2 => (interp t1) -> (interp t2)
     end)%type.

  Compute interp Nat_t.
  Compute interp (Pair_t Nat_t (Pair_t Nat_t Nat_t)).
  Compute interp (Pair_t Nat_t (Fn_t Nat_t Nat_t)).

(*|
Heaps
-----

We're going to need to store dynamic values -- a pair of an `stype t` and a
value of type `interp t`.
|*)
  Print sigT.
  Check sigT interp.
  (* @ means no implicit arguments *)
  Check @sigT stype interp.
  
  Definition dynamic := sigT interp.

(*|
We will continue to use lists of pointers and values as the model for heaps.
However, to support an easy definition of disjoint union, we  will impose the
additional constraint that the list is sorted in (strictly) increasing order.
It's possible to capture this constraint by defining heaps as a sigma type,
where we include a proof that the heap is sorted. That makes some things easier
(e.g., arguing that disjoint union is commutative) but makes other things harder.
For example, equality on sigmas would demand we need to compare proofs, and use
proof-irrelevance.  To avoid this we can put in well-formedness constraints in
just the right places. 
|*)

  Definition heap := list (ptr * dynamic).

  Definition empty_heap : heap := nil.

(*|
Here is a predicate which says that each pointer in `h` is greater than `x`.
|*)
  Fixpoint list_greater (x:ptr) (h:heap) : Prop := 
    match h with 
      | nil => True
      | (y,v)::h' => x < y /\ list_greater x h' 
    end.

(*|
A heap is *well-formed* if each pointer is less than the rest of the heap,
and the rest of the heap is well-formed. 
|*)
  Fixpoint wf (h:heap) : Prop := 
    match h with 
      | nil => True
      | (x,v)::h' => list_greater x h' /\ wf h'
    end.
  
  Fixpoint indom (x:ptr) (h:heap) : Prop := 
    match h with 
      | nil => False
      | (y,_)::h' => if ptr_eq x y then True else indom x h'
    end.

(*|
A pointer `x` is fresh for `h` when it's not in the domain of `h`.
|*)
  Definition fresh x (h:heap) : Prop := ~ indom x h.

(*|
Here are standard `lookup` and `remove` functions on heaps.
|*)
  Fixpoint lookup (x:ptr) (h:heap) : option dynamic := 
    match h with 
      | nil => None
      | (y,v)::h' => if ptr_eq x y then Some v else lookup x h'
    end.

  Fixpoint remove (x:ptr) (h:heap) : heap := 
    match h with 
      | nil => nil
      | (y,v)::h' => if ptr_eq x y then h' else (y,v)::(remove x h')
    end.

(*|
Two heaps are disjoint when each pointer in `h1` is fresh for `h2`. 
|*)
  Fixpoint disjoint (h1 h2:heap) : Prop := 
    match h1 with 
      | nil => True
      | (x,_)::h1' => ~indom x h2 /\ disjoint h1' h2
    end.

(*|
To `insert` into a heap, we use insertion sort. 
|*)
  Fixpoint insert (x:nat) (v:dynamic) (h:heap) : heap := 
    match h with 
      | nil => (x,v)::nil
      | (y,w)::h' => 
        if le_gt_dec x y then 
          (x,v)::(y,w)::h'
          else 
            (y,w)::(insert x v h')
    end.

(*|
We can merge two heaps using our `insert` function.
|*)
  Definition merge (h1 h2:heap) : heap := 
    List.fold_right (fun p h => insert (fst p) (snd p) h) h2 h1.

(*|
Commands
--------
As in earlier lectures, we model commands via shallow embedding and using a
monad. That is, a command takes a heap and returns an optional heap and a
result.
|*)
  Definition Cmd(t:Type) := heap -> option(heap * t).

  Definition ret t (x:t) : Cmd t := fun h => Some (h,x).

  Definition exit t : Cmd t := fun h => None.

  Definition bind t u (c:Cmd t) (f:t -> Cmd u) : Cmd u := 
    fun h1 => match c h1 with 
                | None => None
                | Some (h2,v) => f v h2
              end.

  Declare Scope cmd_scope.
(*|
We introduce some notation similar to Haskell's "do" notation. 
|*)
  Notation "x <- c ; f" := (bind c (fun x => f))
    (right associativity, at level 84) : cmd_scope.
  Notation "c ;; f" := (bind c (fun _:unit => f))
    (right associativity, at level 84) : cmd_scope.
  Local Open Scope cmd_scope.

  Definition run(t:Type)(c:Cmd t) := c empty_heap.

(*|
The untyped read operation returns a dynamic value. 
|*)
  Definition untyped_read (p:ptr) : Cmd dynamic := 
    fun h => match lookup p h with 
               | None => None
               | Some u => Some (h,u)
             end.

(*|
This abbreviation may look funny (since we don't use `t`), but it will make it
easier for Coq to figure out the `stype` at  which we're using things.  Note
that this is a little misleading because in general, a `ptr` can map to a
value of any stype! 
|*)
  Definition tptr (t:stype) := ptr.

(*|
The typed read operation first does an untyped read, and then checks that the
`stype` matches what we expected, failing if not, and returning the underlying
value otherwise. 
|*)
  Definition read (t:stype) (p:tptr t) : Cmd (interp t).
    refine ((fun t p =>
               d <- untyped_read p;
               match d with
               | existT _ t' v =>
                   match stype_eq t t' with 
                   | left Heq => ret _
                   | right _ => exit _
                   end
               end) t p).
    subst.
    apply v.
  Defined.

(*|
Likewise, we have untyped and typed write operations.
|*)
  Definition untyped_write (p:ptr) (v:dynamic) : Cmd unit := 
    fun h => match lookup p h with 
               | None => None
               | Some _ => Some (insert p v (remove p h), tt)
             end.

  Definition write (t:stype) (p:tptr t) (v:interp t) : Cmd unit := 
    untyped_write p (existT interp t v).

(*|
To allocate a new pointer, we need to pick something fresh for the heap. So we
choose the maximum value in the heap plus one. 
|*)
  Definition max (p1 p2:ptr) := if le_gt_dec p1 p2 then p2 else p1.

  Definition max_heap(h:heap) := List.fold_right (fun p n => max (fst p) n) 0 h.

  Definition untyped_new (v:dynamic) : Cmd ptr := 
    fun h => let p := 1 + max_heap h in Some (insert p v h, p).

  Definition new(t:stype)(v:interp t) : Cmd (tptr t) :=
    untyped_new (existT interp t v).

  Definition free (p:ptr) : Cmd unit := 
    fun h => match lookup p h with 
               | None => None
               | Some _ => Some(remove p h, tt)
             end.

(*|
Heap Predicates (AKA "hprops")
------------------------------
An `hprop` is a predicate on heaps. 
|*)
  Definition hprop := heap -> Prop.

(*|
`emp` holds only when the heap is empty.  One way to think of `emp` is that as
a pre-condition, it tells us that we don't have the right to access anything in
the heap.  `emp` plays the role of a unit for `star` which is defined below. 
|*)
  Definition emp : hprop := fun h => h = nil.

(*|
`top` holds on any heap. 
|*)
  Definition top : hprop := fun _ => True.

  Declare Scope sep_scope.
(*|
`x ---> d` holds when the heap contains exactly one pointer `x` which
points to `d`.  So we can think of this predicate as permission to 
read or write `x` and if we read it, we'll get out the dynamic value `d`.  
However, we're not allowed to read or write any other location if this
is our only pre-condition. 
|*)
  Definition ptsto (x:ptr) (d:dynamic) : hprop := fun h => h = (x,d)::nil.
  Infix "--->" := ptsto (at level 70) : sep_scope.
  Local Open Scope sep_scope.

(*|
`x --> v` is the same as above, except we make the type explicit.
|*)
  Definition typed_ptsto (t:stype) (x:tptr t) (v:interp t) : hprop := 
    x ---> (existT interp t v).
  Arguments typed_ptsto {t}.
  Infix "-->" := typed_ptsto (at level 70) : sep_scope.

(*|
`P ** Q` holds when the heap can be broken into disjoint heaps `h1` and `h2` such that `h1` satisfies `P` and `h2` satisfies `Q`. For example `x --> v ** y --> v` tells us that we have the right to access both `x` and `y`, but that `x <> y`. 
|*)
  Definition star (P Q:hprop) : hprop := 
    fun h => exists h1:heap, exists h2:heap, 
      wf h1 /\ wf h2 /\ P h1 /\ Q h2 /\ h = merge h1 h2 /\ disjoint h1 h2.
  Infix "**" := star (right associativity, at level 80) : sep_scope.

(*|
When `P` is a pure predicate in the sense that it doesn't refer to a
heap, then we can use `pure P` as a predicate on the heap.  Note that
we require that the heap that it corresponds to is empty. 
|*)
  Definition pure (P:Prop) : hprop := fun h => emp h /\ P.

(*|
`sing h` is the singleton predciate on heaps -- i.e., it holds on `h'`
only when `h'` is equal to `h`. 
|*)
  Definition sing (h:heap) : hprop := fun h' => h = h'.

(*|
This definition lifts an existential quantifier up to a predicate on heaps. 
|*)
  Definition hexists (T:Type) (f:T -> hprop) : hprop := fun h => exists x:T, f x h.

(*|
So for instance, we can define `x -->?` as follows 
|*)
  Local Open Scope sep_scope.
  Definition ptsto_some (x:ptr) := hexists (fun v => x ---> v).
  Notation "x '-->?'" := (ptsto_some x) (at level 70) : sep_scope.

(*|
This notation will be useful for reasoning about when one separation
predicate can be used in lieu of another -- i.e., a form of implication
over heaps. Note that this is not the "magic-wand" of separation logic,
but rather, a meta-level implication. 
|*)
  Definition himp(P Q:hprop) : Prop := forall h, wf h -> P h -> Q h.
  Infix "==>" := himp (at level 90) : sep_scope.

(*|
Here is a standard Greg (Morrisett) simplification tactic.
|*)
  Ltac mysimp := repeat (simpl ; 
    match goal with 
      | [ p : (_ * _)%type |- _ ] => destruct p
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : exists _, _ |- _ ] => destruct H
      | [ |- context[ptr_eq ?x ?y] ] => destruct (ptr_eq x y) ; try subst ; try congruence
      | [ H : context[ptr_eq ?x ?y] |- _ ] => 
        destruct (ptr_eq x y) ; try subst ; try congruence
      | [ |- context[le_gt_dec ?x ?y] ] => destruct (le_gt_dec x y) ; try lia
      | [ H : context[le_gt_dec ?x ?y] |- _ ] => destruct (le_gt_dec x y) ; try lia
      | [ |- _ /\ _ ] => split
      | [ H : (_,_) = (_,_) |- _ ] => injection H ; clear H ; intros ; try subst
      | [ H : Some _ = Some _ |- _ ] => injection H ; clear H ; intros ; try subst
      | [ H : Some _ = None |- _ ] => congruence
      | [ H : None = Some _ |- _ ] => congruence
      | [ H : ?x <> ?x |- _ ] => congruence
      | [ H : ~ True |- _ ] => contradiction H ; auto
      | [ H : False |- _ ] => contradiction H ; auto
      | [ |- forall _, _ ] => intros
      | _ => auto 
    end).

(*|
We need a ton of lemmas for reasoning about heaps.  The keys ones are
showing that various operations preserve well-formedness, or that 
merging well-formed heaps is commutative and associative, etc. 
|*)

(*|
For example, removing a pointer keeps a heap well-formed.
|*)
  Lemma remove_wf x (h:heap) : wf h -> wf (remove x h).
  Proof.
    induction h ; mysimp. generalize h H ; induction h0 ; mysimp.
  Qed.

  Lemma disjoint_indom :
    forall h1 h2 p,
      disjoint h1 h2 -> indom p h1 -> ~indom p h2.
  Proof.
    induction h1.
    - mysimp.
    - intros.
      destruct a as [p1 d1].
      destruct (ptr_eq p p1).
      + rewrite <- e in H.
        unfold disjoint in H.
        mysimp.
      + apply IHh1.
        unfold disjoint in H.
        mysimp.
        unfold indom in H0.
        mysimp.
  Qed.

  Lemma not_indom_cons:
    forall (h:heap) (p0:ptr) (p:ptr) (d:dynamic),
      ~indom p0 ((p,d)::h) -> ~indom p0 h.
  Proof.
    mysimp.
  Qed.
    
  Lemma disjoint_cons:
    forall h1 h2 p,
      disjoint h1 (p::h2) -> disjoint h1 h2.
  Proof.
    induction h1.
    - intros.
      mysimp.
    - intros.
      mysimp.
      eapply (not_indom_cons h2 p0 p d).
      unfold disjoint in H.
      destruct H.
      apply H.
      apply (IHh1 h2 (p,d)).
      unfold disjoint in H.
      mysimp.
  Qed.
  
(*|
Disjointness is commutative. 
|*)
  Lemma disjoint_comm : forall (h1 h2:heap),
      disjoint h1 h2 -> disjoint h2 h1.
  Proof.
    induction h1; induction h2; mysimp.
    apply (disjoint_indom ((p,d) :: h2) h1 p).
    apply IHh1, H0.
    mysimp.
    apply IHh2.
    mysimp.
    apply (disjoint_cons h1 h2 (p,d)).
    mysimp.
  Qed.
  
  Lemma lg_trans x y : x < y -> forall h, list_greater y h -> list_greater x h.
    induction h ; mysimp. lia.
  Qed.

(*|
Inserting a fresh pointer keeps a heap well-formed. 
|*)
  Lemma insert_wf h : wf h -> forall x v, fresh x h -> wf (insert x v h).
  Proof.
    unfold fresh ; induction h ; mysimp. lia. eapply (@lg_trans x p) ; auto. lia. 
    generalize (IHh H1 x v H0). destruct h ; mysimp. lia. 
    eapply (@lg_trans p p0) ; auto. lia. simpl in H. lia. simpl in *.
    assert (p < p0). lia. eapply lg_trans ; eauto.
  Qed.

  Lemma lg_imp_not_indom p h : list_greater p h -> fresh p h.
  Proof.
    unfold fresh ; induction h ; mysimp. lia.
  Qed.

  Lemma not_indom_insert x h : 
    fresh x h -> forall y v, y <> x -> fresh x (insert y v h).
  Proof.
    unfold fresh ; induction h ; mysimp. 
  Qed.

  Lemma not_indom_merge h1 h2 p : fresh p h1 -> fresh p h2 -> fresh p (merge h1 h2).
  Proof.
    unfold fresh ; induction h1 ; mysimp. apply not_indom_insert ; unfold fresh ; auto.
  Qed.

(*|
Merging two well-formed, disjoint heaps results in a well-formed heap. 
|*)
  Lemma merge_wf h1 h2 : wf h1 -> wf h2 -> disjoint h1 h2 -> wf (merge h1 h2).
  Proof.
    induction h1; mysimp. generalize (IHh1 H3 H0 H2). intros.
    eapply insert_wf; auto. generalize (lg_imp_not_indom p h1).
    intros. apply not_indom_merge ; auto.
  Qed.
      
(*|
Insertion is commutative for distinct pointers.
|*)
  Lemma insert_comm h x1 v1 x2 v2 : 
    x1 <> x2 -> insert x1 v1 (insert x2 v2 h) = insert x2 v2 (insert x1 v1 h).
  Proof.
    induction h ; unfold ptr. mysimp. destruct a. intros. simpl.
    mysimp ; try (assert False ; [lia|contradiction]). rewrite IHh ; auto.
  Qed.

(*|
Merge is commutative when the heaps are well-formed and disjoint.
|*)
  Lemma merge_comm h1 h2 : wf h1 -> wf h2 -> disjoint h1 h2 -> merge h1 h2 = merge h2 h1.
  Proof.
    induction h1 ; mysimp. induction h2 ; simpl in * ; mysimp.
    rewrite <- IHh2 ; auto. destruct h2 ; simpl in * ; mysimp.
    rewrite (IHh1 H3 H0 H2). clear IHh1.
    induction h2. mysimp. destruct h1 ; simpl in * ; mysimp.
    mysimp. simpl in * ; mysimp. rewrite <- (IHh2 H4 H1).
    rewrite insert_comm ; auto. generalize (disjoint_comm _ _ H2).
    mysimp. apply disjoint_comm ; auto.
  Qed.
  
  Lemma disjoint_merge : forall h1 h2 h3, disjoint h1 h3 -> disjoint h2 h3 -> 
    disjoint (merge h1 h2) h3.
  Proof.
    induction h1 ; mysimp. generalize (IHh1 _ _ H1 H0). 
    generalize (merge h1 h2). induction h ; mysimp.
  Qed.

(*|
Well-formed merges are associative. 
|*)
  Lemma merge_assoc : forall h1 h2 h3, 
    wf h1 -> wf h2 -> wf h3 -> disjoint h1 h2 -> disjoint h1 h3 -> 
    disjoint h2 h3 -> merge h1 (merge h2 h3) = merge (merge h1 h2) h3.
  Proof.
    induction h1 ; mysimp.
    rewrite (IHh1 _ _ H7 H0 H1 H6 H5 H4). assert (wf (merge h1 h2)).
    apply merge_wf ; auto. generalize H8 ; clear H8.
    assert (~indom p (merge h1 h2)). apply not_indom_merge ; auto. 
    apply lg_imp_not_indom ; auto. generalize H8 ; clear H8. 
    assert (disjoint (merge h1 h2) h3). apply disjoint_merge ; auto. 
    generalize H8 ; clear H8. generalize (merge h1 h2). induction h ; mysimp.
    rewrite insert_comm ; auto. rewrite IHh ; auto.
  Qed.

  Lemma indom_insert x h y v : x <> y -> fresh x (insert y v h) -> fresh x h.
  Proof.
    unfold fresh ; induction h ; simpl in * ; intros ; mysimp ; simpl in * ; mysimp.
  Qed.

(*|
If `p` is fresh for `merge h1 h2`, then it's also fresh for both `h1` and `h2`. 
|*)
  Lemma merge_not_indom h1 h2 p : fresh p (merge h1 h2) -> fresh p h1 /\ fresh p h2.
  Proof.
    unfold fresh ; induction h1 ; simpl ; auto. destruct a. intros ; 
    destruct (ptr_eq p0 p). subst. simpl in *. assert False. apply H. 
    generalize (merge h1 h2). induction h ; mysimp. contradiction. mysimp;    
    apply IHh1; eapply indom_insert ; eauto.
  Qed.

  Lemma merge_disjoint h1 h2 h3 : 
    disjoint h1 (merge h2 h3) -> disjoint h1 h2 /\ disjoint h1 h3.
  Proof.
    induction h1. mysimp. simpl. destruct a. intros. destruct H.
    destruct (merge_not_indom h2 h3 H).
    generalize (IHh1 H0). mysimp.
  Qed.

  Lemma max_heap_fresh : forall h n, n > max_heap h -> fresh n h.
  Proof.
    unfold fresh ; induction h ; mysimp ; unfold max in *. mysimp. mysimp. apply IHh. 
    simpl in *. lia.
  Qed.

  Lemma remove_not_indom : forall p h, wf h -> fresh p (remove p h).
  Proof.
    unfold fresh ; induction h ; mysimp. apply lg_imp_not_indom ; auto.
  Qed.

  Lemma lookup_insert : forall x v h, lookup x (insert x v h) = Some v.
  Proof.
    induction h ; mysimp. assert False. lia. contradiction.
  Qed.
  
  Lemma remove_insert : forall x v h, remove x (insert x v h) = h.
  Proof.
    induction h ; mysimp. assert False. lia. contradiction.
  Qed.

(*|
Separation Reasoning
--------------------
Reasoning directly in terms of heaps is painful.  So we will define
some rules for reasoning directly at the level of the separation logic. 
This list of lemmas is by no means complete... 
|*)
  Lemma emp_star P : P ==> emp ** P.
  Proof.
    unfold himp, star, emp, disjoint ; simpl ; intros. exists empty_heap. exists h. 
    mysimp. 
  Qed.
  Hint Resolve emp_star : sep_db.

  Lemma star_comm P Q : P ** Q ==> Q ** P.
  Proof.
    unfold himp, star ; mysimp ; exists x0 ; exists x ; simpl in * ; mysimp ;
      try rewrite merge_comm ; auto ; apply disjoint_comm ; simpl ; auto.
  Qed. 

  Lemma star_emp P : P ==> P ** emp.
  Proof.
    unfold himp, star, emp ; intros. apply star_comm ; auto. apply emp_star ; auto.
  Qed.
  Hint Resolve star_emp : sep_db.

  Lemma star_assoc P Q R : P ** (Q ** R) ==> (P ** Q) ** R.
  Proof.
    unfold himp, star ; mysimp ; subst.
    generalize (merge_disjoint _ _ _ H5). mysimp.
    exists (merge x x1). exists x2. mysimp. apply merge_wf ; auto.
    exists x. exists x1. mysimp. rewrite merge_assoc ; auto. 
    apply disjoint_merge ; auto.
  Qed.

  Lemma pure_elim (P:hprop) (R:hprop) (Q:Prop) : Q -> (R ==> P) -> (R ==> (pure Q) ** P).
  Proof.
    unfold himp, pure, star, emp, disjoint. intros. exists empty_heap. exists h. mysimp.
  Qed.
  Hint Resolve pure_elim : sep_db.

  Lemma comm_conc P Q R : P ==> Q ** R -> P ==> R ** Q.
  Proof.
    intros. intros h Hwf HP. apply star_comm ; auto.
  Qed.

  Lemma himp_id : forall P, P ==> P.
    unfold himp. auto.
  Qed.
  Hint Resolve himp_id : sep_db.

  Lemma ptsto_ptsto_some : forall t (x:tptr t) (v:interp t), x --> v ==> x -->?.
    unfold himp, typed_ptsto, ptsto_some, hexists, ptsto. intros.
    exists (existT interp t v). auto.
  Qed.
  Hint Resolve ptsto_ptsto_some : sep_db.

  Lemma hyp_comm : forall P Q R, P ** Q ==> R -> Q ** P ==> R.
  Proof.
    unfold himp ; mysimp. apply H ; auto. apply star_comm ; auto.
  Qed.
  
  Lemma hyp_pure : forall (P:Prop) Q R, (P -> Q ==> R) -> (pure P) ** Q ==> R.
  Proof.
    unfold himp, star, pure, emp ; mysimp ; subst ; simpl in *. apply H ; auto. 
  Qed.
  Hint Resolve hyp_pure : sep_db.

  Lemma ptsto_hexist : forall t (p:tptr t) (v:interp t), 
    p --> v ==> hexists (fun v => p --> v).
  Proof.
    unfold himp, hexists, typed_ptsto, ptsto ; mysimp ; subst ; mysimp. eauto.
  Qed.
  Hint Resolve ptsto_hexist : sep_db.

  Lemma hyp_hexists : forall t (F:t->hprop) R, 
    (forall x:t, F x ==> R) -> hexists F ==> R.
  Proof.
    unfold hexists. intros. intros h Hwf. mysimp. apply (H x h) ; auto.
  Qed.

  Definition himp_split P1 P2 Q1 Q2 : P1 ==> Q1 -> P2 ==> Q2 -> P1**P2 ==> Q1**Q2.
  Proof.
    unfold himp, star ; intros ; mysimp. exists x. exists x0. mysimp.
  Qed.

(*|
This little tactic helps prove things are disjoint: 
|*)
  Ltac disj := 
    repeat
      match goal with 
        | [ H : disjoint ?x ?y |- disjoint ?y ?x ] => apply disjoint_comm ; auto
        | [ |- disjoint (merge _ _) _ ] => apply disjoint_merge 
        | [ |- disjoint _ (merge _ _) ] => apply disjoint_comm
        | [ H : disjoint (merge _ _) _ |- _ ] => 
          generalize (merge_disjoint _ _ _ (disjoint_comm _ _ H)) ; clear H ; mysimp
        | [ H : disjoint _ (merge _ _) |- _ ] => 
          generalize (merge_disjoint _ _ _ H) ; clear H ; mysimp
        | [ |- wf (merge _ _) ] => apply merge_wf ; mysimp
        | [ |- _ ] => assumption
      end.

  Lemma star_assoc_l P Q R : (P ** Q) ** R ==> P ** Q ** R.
  Proof.
    unfold himp, star. mysimp ; disj. subst. exists x1. exists (merge x2 x0).
    mysimp ; disj. exists x2. exists x0. mysimp ; disj. rewrite merge_assoc ; 
    auto ; disj.
  Qed.

(*|
This lemma will help me simplify some reasoning involving existentials. 
|*)
  Lemma existPull(A:Type)(F:A->Prop)(Y Z:Prop) : 
    (exists x:A, F x) -> (Y -> Z) -> 
    ((exists x:A, F x) -> Y) -> Z.
    mysimp. apply H0. apply H1. eauto.
  Qed.

  Lemma hyp_assoc_r P1 P2 P3 Q : 
    P1 ** P2 ** P3 ==> Q -> (P1 ** P2) ** P3 ==> Q.
  Proof.
    unfold himp ; intros. apply H ; auto with sep_db. apply star_assoc_l ; auto.
  Qed.
  Hint Resolve hyp_assoc_r : sep_db.

  Lemma conc_emp P Q : P ==> Q -> P ==> Q ** emp.
    unfold himp, emp, star. intros. apply star_comm ; auto. unfold star.
    exists nil. exists h. mysimp.
  Qed.
  Hint Resolve conc_emp : sep_db.

  Lemma hyp_emp P Q : P ==> Q -> emp ** P ==> Q.
    unfold himp, emp, star. mysimp. subst. simpl in *. auto.
  Qed.
  Hint Resolve hyp_emp : sep_db.

  Lemma assoc_concl P Q1 Q2 Q3 : 
    P ==> Q1 ** Q2 ** Q3 -> P ==> (Q1 ** Q2) ** Q3.
  Proof.
    unfold himp ; intros. apply star_assoc ; auto.
  Qed.

  Lemma himp_mp Q P R : Q ==> R -> P ==> Q -> P ==> R.
  Proof.
    unfold himp ; mysimp.
  Qed.

(*|
Separation Logic
----------------

In separation logic, a total correctness assertion::

   [{{ P }} c {{ Q }}]

holds iff (1) we start with a heap `h` that can be broken into two parts, one that satisfies `P` and another satisfying `sing h2` for some h2, (2) we run the command `c` on heap `h` and get out `Some` heap `h'` and value `v`, and (3) the output heap `h'` satisfies  `Q v ** sing h2`.  That is, the output heap can be broken into two disjoint heaps, one satisfying `Q v`, and one satisfying `sing h2`.

This effectively forces the command to be parametric in some part of the heap (`h2`) and leave it alone.  In turn, this means that if we have proven a separate property about `h2`, this property will be preserved when we run `c`.    
|*)
  (* You can talk about initial values in Q: hprop -> t -> hprop, but they chose not to because we don't need it *)
  Definition sep_tc_triple(t:Type) (P:hprop)(c:Cmd t)(Q:t -> hprop) := 
    forall h h2, (P ** sing h2) h -> 
      match c h with 
        | None => False
        | Some (h',v) => (Q v ** sing h2) h'
      end.
  Notation "{{ P }} c {{ Q }}" := (sep_tc_triple P c Q) (at level 90) : cmd_scope.
  
(*|
Lots of definitions to be unwound... 
|*)
  Ltac unf := unfold sep_tc_triple, star, hexists, pure, emp, sing.

(*|
This says that `ret v` can be run in a heap satisfying `emp` and returns a heap satisfying `emp` and the return value is equal to v. But remember that this really means that `ret` can be run in any heap `h` that can be broken into a portion satisfying `emp` (i.e., the empty heap and some other heap (which must be `h`!) and that the other portion will be preserved.  In short, the specification captures the fact that `ret` will not change the heap. 
|*)
  Lemma ret_tc (t:Type) (v:t) : {{ emp }} ret v {{ fun x => pure (x = v) }}.
  Proof.
    unf ; mysimp ; subst. exists empty_heap. exists x0. mysimp.
  Qed.

(*|
`new v` consumes an empty heap, and produces a pointer `x` and a heap satisfying `x --> v`.  Because of the definition of the separation-total-correctness triple, `x` must be fresh for the whole heap.
|*)
  Lemma new_tc (t:stype)(v:interp t) : 
    {{ emp }} new t v {{ fun (x:tptr t) => x --> v }}.
  Proof.
    unfold new, typed_ptsto ; unf ; mysimp ; subst. 
    exists ((S (max_heap x0),existT interp t v)::nil). exists x0.
    mysimp. unfold ptsto ; auto. apply max_heap_fresh. lia.
  Qed.

(*|
`free x` is nicely dual to `new`. 
|*)
  Lemma free_tc (p:ptr) : 
    {{ p-->? }} free p {{ fun _ => emp }}.
  Proof.
    unf ; unfold ptsto_some, hexists, ptsto, free ; mysimp ; subst ; mysimp.
    rewrite lookup_insert. exists nil. exists x0. mysimp. 
    rewrite remove_insert. auto.
  Qed.

(*|
`write p v` requires a heap where `p` points to some value, and ensures `p` points to `v` afterwards. 
|*)
  Lemma write_tc (t:stype) (p:tptr t) (v:interp t) : 
    {{ p -->? }} write p v {{ fun _ => p --> v }}.
  Proof.
    unfold ptsto_some, typed_ptsto, hexists, ptsto, write, untyped_write ; unf.
    mysimp ; subst ; mysimp ; simpl in *.
    rewrite lookup_insert. exists ((p,existT interp t v)::nil). exists x0. mysimp.
    rewrite remove_insert ; auto. 
  Qed.

(*|
`read p` requires a heap where `p` points to some value `v`, and ensures `p` points to `v` afterwards, and the result is equal to `v`. 
|*)
  Lemma read_tc (t:stype) (p:tptr t) (v:interp t) :
    {{ p --> v }} 
    read p 
    {{ fun x => p --> x ** pure(x = v) }}.
  Proof.
    unf ; unfold typed_ptsto, ptsto, read, untyped_read, bind ; 
      mysimp ; subst ; mysimp ; simpl in * ; mysimp.
    rewrite lookup_insert. destruct (stype_eq t t) ; try congruence. 
    rewrite (proof_irrelevance e (eq_refl t)). unfold eq_rec_r ; simpl. 
    simpl. exists ((p,existT interp t v)::nil). exists x0. mysimp. 
    exists ((p,existT interp t v)::nil). exists nil. mysimp.
  Qed.
  
(*|
This is one possible proof rule for `bind`.  Basically, we require that the post-condition of the first command implies the pre-condition of the second command. 
|*)
  Lemma bind_tc(T1 T2:Type) P1 Q1 P2 Q2 (c:Cmd T1)(f: T1 -> Cmd T2) : 
    {{ P1 }} c {{ Q1 }} -> 
    (forall x, {{ P2 x }} (f x) {{ Q2 }}) -> 
    (forall x, Q1 x ==> P2 x) -> 
    {{ P1 }} bind c f {{ Q2 }}.
  Proof.
    unfold bind ; unf ; mysimp ; subst. 
    generalize (H (merge x x0) x0). clear H. 
    apply existPull. exists x. exists x0. mysimp. destruct (c (merge x x0)) ; 
    mysimp. subst. generalize (H0 t (merge x1 x2) x2). clear H0.
    apply existPull. exists x1. exists x2. mysimp. eapply H1 ; eauto. auto.
  Qed.
  Arguments bind_tc {T1 T2 P1 Q1 P2 Q2 c f}.
  
(*|
And we also have a rule of consequence which allows us to strengthen the
pre-condition and weaken the post-condition.  Note however, that this will
not allow us to "forget" any locations in our footprint. 
|*)
  Lemma consequence_tc (T:Type) P1 Q1 P2 Q2 (c:Cmd T) : 
    {{ P1 }} c {{ Q1 }} -> 
    P2 ==> P1 -> 
    (forall x, Q1 x ==> Q2 x) -> 
    {{ P2 }} c {{ Q2 }}.
  Proof.
    unf ; mysimp ; subst ; mysimp. generalize (H (merge x x0) x0). clear H.
    apply existPull. exists x. exists x0. mysimp. destruct (c (merge x x0)) ; mysimp.
    subst. exists x1. exists x2. mysimp. eapply H1 ; mysimp.
  Qed.
  Arguments consequence_tc {T} _ _ {P2 Q2 c}.
  
(*|
This is a specialization of consequence that is a little more useful. 
|*)
  Lemma strengthen_tc (T:Type) P1 P2 Q1 (c:Cmd T): 
    {{P1}}c{{Q1}} -> 
    P2 ==> P1 -> 
    {{P2}}c{{Q1}}.
  Proof.
    intros. eapply consequence_tc ; eauto with sep_db.
  Qed.
  Arguments strengthen_tc {T} _ {P2 Q1 c}.

(*|
This is a specialization of consequence that is a little more useful. 
|*)
  Lemma weaken_tc (T:Type) P1 Q1 Q2 (c:Cmd T): 
    {{P1}}c{{Q1}} -> 
    (forall x, Q1 x ==> Q2 x) -> 
    {{P1}}c{{Q2}}.
  Proof.
    intros. eapply consequence_tc ; eauto with sep_db.
  Qed.

(*|
Finally, this is the most important rule and the one we lacked with Hoare logic:  If `{{ P }} c {{ Q }}`, then also `{{ P ** R }} c {{ Q ** R }}`.  That is, properties such as `R` which are disjoint from the footprint are preserved when we run the command.  
|*)
  Lemma frame_tc(T:Type)(c : Cmd T) P Q R : 
    {{ P }} c {{ Q }} -> {{ P ** R }} c {{ fun x => (Q x) ** R }}.
  Proof.
    unf ; mysimp ; subst ; mysimp. rewrite <- merge_assoc ; auto ; disj.
    generalize (H (merge x1 (merge x2 x0)) (merge x2 x0)). clear H.
    apply existPull. exists x1. exists (merge x2 x0). mysimp ; disj. 
    destruct (c (merge x1 (merge x2 x0))) ; mysimp ; subst.
    exists (merge x x2). exists x0. mysimp ; disj. 
    exists x. exists x2. mysimp ; disj. rewrite merge_assoc ; disj ; auto.
  Qed.
  Arguments frame_tc {T c P Q}.
  
  Ltac sep := repeat
    (simpl in * ; (try subst) ; 
      match goal with 
        | [ |- forall _, _ ] => intros
        | [ |- _ ** ?Q ==> _ ** ?Q ] => eapply himp_split
        | [ |- ?P ** _ ==> ?P ** _ ] => eapply himp_split
        | [ |- ?P ** _ ==> _ ** ?P ] => eapply hyp_comm
        | [ |- hexists _ ==> _ ] => eapply hyp_hexists
        | [ |- _ ** pure _ ==> _ ] => eapply hyp_comm ; eapply hyp_pure
        | [ |- (_ ** _) ** _ ==> _ ] => eapply hyp_assoc_r
        | [ |- _ ==> (_ ** _) ** _ ] => eapply assoc_concl
        | _ => eauto with sep_db
      end).

(*|
Examples
---------

Following are a few examples that illustrate the use of Separation Logic.
|*)
  Definition inc(p:tptr Nat_t) := 
    v <- read p ; 
    write p (1 + v).

(*|
The next definition says that if we start in a state where `p` holds `n`,
then after running inc, we do not fail and get into a state 
where `p` holds `1+n`.  Notice that it's rather delicate to
hang on to the fact that the value read out is equal to `n`.  If
we used binary post-conditions (a relation on both the input heap
and output heap), this wouldn't be necessary.  
|*)
  Definition inc_tc(p:tptr Nat_t)(n:interp Nat_t) :
    {{ p --> n }} inc p {{ fun _ => p --> 1+n }}.
  Proof.
    unfold inc; sep.
    eapply bind_tc; sep.
    eapply (@read_tc Nat_t _ _); sep. simpl.
    eapply consequence_tc.
    eapply (frame_tc (pure (x = n))).
    eapply write_tc. sep. simpl. sep.
  Qed.
    
(*|
The great part is that now if we have a property on some disjoint
part of the state, say `p2 --> n2`, then after calling `inc`, we
are guaranteed that property is preserved via the frame rule. 
|*)
  Definition inc_two(p1 p2:tptr Nat_t)(n1 n2:interp Nat_t) : 
    {{ p1 --> n1 ** p2 --> n2 }} inc p1 {{ fun _ => p1 --> 1+n1 ** p2 --> n2 }}.
  Proof.
    intros.
    apply (frame_tc (p2 --> n2)).
    apply inc_tc.
  Qed.

(*|
Here is a function to swap the contents of two pointers.
|*)
  Definition swap(t:stype)(p1 p2:tptr t) := 
    v1 <- read p1 ; 
    v2 <- read p2 ; 
    write p2 v1 ;; 
    write p1 v2.

(*|
Alas, reasoning isn't quite as simple as we might hope. We have to not only put in the right uses of the frame and consequence rules, but we must also so a lot of commuting and re-associating to discharge the verification conditions. For Ynot, Adam Chlipala wrote an Ltac tactic that mostly took care of this sort of simple reasoning. And Gonthier et al. have done some nice work showing how to use  type-classes or canonical-structures to automate a lot of this sort of thing. Below, we'll see you an alternative technique based on reflection. 
|*)
  Lemma swap_tc(t:stype)(p1 p2:tptr t)(v1 v2:interp t) : 
    {{ p1 --> v1 ** p2 --> v2 }} swap p1 p2 {{ fun _ => p1 --> v2 ** p2 --> v1 }}.
  Proof.
    unfold swap ; sep.
    eapply bind_tc ; sep.
    eapply (frame_tc (p2 --> v2)).
    eapply read_tc. sep.
    eapply (consequence_tc ((p2 --> v2 ** p1 --> x) ** pure (x = v1))).
    eapply (frame_tc (pure (x = v1))).
    eapply bind_tc ; sep.
    eapply (frame_tc (p1 --> x)).
    eapply read_tc ; sep. simpl.
    eapply (consequence_tc ((p2 -->? ** p1 --> x) ** pure (x0 = v2))).
    eapply (frame_tc (pure (x0 = v2))).
    eapply bind_tc ; sep.
    eapply (frame_tc (p1 --> x)).
    eapply write_tc ; sep. sep.
    eapply (consequence_tc (p1 -->? ** p2 --> x)).
    eapply (frame_tc (p2 --> x)).
    eapply write_tc ; sep. apply hyp_comm. sep. sep. eapply himp_id.
    sep. eapply himp_split ; sep. sep. eapply himp_id.
    eapply hyp_comm. sep. sep.
  Qed.

(*|
Reflection and a Simple, Correct Semi-Decision Procedure
--------------------------------------------------------

Our goal will be to build a Coq function that can simplify a separation implication `P ==> Q` and prove that function correct. One simple strategy is to flatten out all of the stars and cross off all of the simple predicates that appear in both `P` and `Q`.  

But of course, we can't just crawl over an `hprop` because in general, these are functions!  So our trick is to write down some syntax that represents a particular predicate, and then give an interpretation that maps that syntax back to our real predicate. Then we can compute with the syntax.

The Quote library should help us with this, but alas, it's not as clever as we might hope it would be... 
|*)
  Definition hprop_name := nat.
  Definition hprop_map := list (hprop_name * hprop).
  Definition hprop_name_eq := PeanoNat.Nat.eq_dec.

(*|
We begin by giving a basic syntax for predicates. `Atom` will be used to represent things like abstract predicates (e.g., a variable `P`) or a points-to-predicate etc.  We'll use an environment to map an `hprop_name` to the real `hprop`.
|*)
  Inductive Hprop : Set := 
  | Emp : Hprop
  | Atom : hprop_name -> Hprop
  | Star : Hprop -> Hprop -> Hprop.

  Infix "#" := Star (right associativity, at level 80) : sep_scope.

  Fixpoint lookup_hprop (n:hprop_name) (hp:hprop_map) := 
    match hp with 
      | nil => (pure False)
      | (m,P)::rest => if hprop_name_eq n m then P else lookup_hprop n rest
    end.

  Section HINTERP.
(*|
We'll assume we have an `hprop_map` lying around. 
|*)
    Variable hmap : hprop_map.

(*|
Now we given an interpretation to the syntax for predicates: 
|*)
    Fixpoint hinterp (hp:Hprop) : hprop := 
      match hp with 
        | Emp => emp
        | Atom n => lookup_hprop n hmap
        | Star h1 h2 => star (hinterp h1) (hinterp h2)
      end.

(*|
We can flatten a predicate into a list of `hprop_name`.
|*)
    Fixpoint flatten (hp:Hprop) : list hprop_name := 
      match hp with 
        | Emp => nil
        | Atom n => n::nil
        | Star h1 h2 => (flatten h1) ++ (flatten h2)
      end.

(*|
This function removes exactly one copy of `n`, an `hprop_name`, from the input list, returning `None` if we fail to find a copy of `n`. 
|*)
    Fixpoint remove_one(n:hprop_name)(hps : list hprop_name) :option (list hprop_name) := 
      match hps with 
        | nil => None
        | (m::rest) => 
          if hprop_name_eq n m then Some rest else
            match remove_one n rest with 
              | None => None
              | Some hps' => Some (m::hps')
            end
      end.

(*|
This is the heart of our simplification algorithm.  Here, we are running through the list of names `hp1`, trying to cross off each one that occurs in `hp2`.  If the current name doesn't occur, we add it to the end of `hp0` so that we can keep track of it.  That is, our invariant at each step should be that `hp0 ** hp1 ==> hp2` once we map the list back to an `hprop`. 
|*)
    Fixpoint simplify (hp0 hp1 hp2:list hprop_name) := 
      match hp1 with 
        | nil => (hp0,hp2)
        | (n::hp1') => 
          match remove_one n hp2 with 
            | Some hp2' => simplify hp0 hp1' hp2'
            | None => simplify (hp0 ++ n::nil) hp1' hp2
          end
      end.

(*|
Convert a list of names back into an `hprop`. 
|*)
    Definition collapse := List.fold_right (fun n p => Star (Atom n) p) Emp.
(*|
Convert a list of names into an `hprop`. 
|*)
    Definition interp_list := List.fold_right (fun n p => (lookup_hprop n hmap) ** p) emp.

(*|
Our cross-off algorithm takes two `hprop`, flattens them into lists of names, simplifies the two lists by crossing off common names, and then returns the two `hprop` we get by collapsing the resulting simplified lists. 
|*)
    Definition cross_off (hp1 hp2 : Hprop) : Hprop * Hprop := 
      let (hp1', hp2') := simplify nil (flatten hp1) (flatten hp2) in 
        (collapse hp1', collapse hp2').

    Lemma collapse_interp hp : hinterp (collapse hp) = interp_list hp.
    Proof.
      induction hp ; mysimp. rewrite IHhp. auto.
    Qed.

(*|
The following are various lemmas needed to reason about the interpretation
of the syntax. 
|*)
    Lemma interp_list_app hp1 hp2 : 
      interp_list (hp1 ++ hp2) ==> ((interp_list hp1) ** (interp_list hp2)).
    Proof.
      induction hp1. simpl. intros. apply comm_conc. apply conc_emp. auto with sep_db.
      simpl. intros. sep.
    Qed.

    Lemma app_interp_list hp1 hp2 : 
      ((interp_list hp1) ** (interp_list hp2)) ==> interp_list (hp1 ++ hp2).
    Proof.
      induction hp1. simpl. intros. apply hyp_emp. sep. simpl ; intros. sep.
    Qed.

    Lemma hinterp_flatten hp : hinterp hp ==> interp_list (flatten hp).
    Proof.
      induction hp ; simpl. sep. apply conc_emp. sep.
      eapply himp_mp. eapply app_interp_list. eapply himp_split ; eauto.
    Qed.

    Lemma remove_one_splits n hp: 
      match remove_one n hp with 
        | Some hp' => exists hp1, exists hp2, hp = hp1 ++ n::hp2 /\ hp' = hp1 ++ hp2
        | None => True
      end.
    Proof.
      induction hp ; mysimp. destruct (hprop_name_eq n a). subst.
      exists nil. exists hp. mysimp. destruct (remove_one n hp).
      mysimp. subst. exists (a::x). exists x0. mysimp. mysimp.
    Qed.

    Lemma interp_list_comm x1 x2 : interp_list (x1 ++ x2) ==> interp_list (x2 ++ x1).
    Proof.
      induction x1 ; simpl. intros.
      rewrite app_nil_r. sep.
      intros. eapply himp_mp. eapply app_interp_list. 
      eapply comm_conc. simpl. sep. apply interp_list_app.
    Qed.

    Lemma himp_remove_one n hp1 hp2 : 
      match remove_one n hp1, remove_one n hp2 with 
        | Some hp1', Some hp2' => 
          (interp_list hp1' ==> interp_list hp2') -> 
          interp_list hp1 ==> interp_list hp2
        | _, _ => True
      end.
    Proof.
      intros. 
      generalize (remove_one_splits n hp1). generalize (remove_one_splits n hp2).
      destruct (remove_one n hp1) ; auto. destruct (remove_one n hp2) ; auto. 
      mysimp. subst. 
      eapply himp_mp. eapply interp_list_comm. sep.
      eapply (@himp_mp (interp_list ((n::x0) ++ x))) ; try apply interp_list_comm.
      sep. eapply himp_mp. apply interp_list_comm. 
      eapply (@himp_mp (interp_list (x ++ x0))). auto. apply interp_list_comm.
    Qed.

    Lemma himp_simp n hp1 hp2 : 
      match remove_one n hp2 with 
        | Some hp2' => 
          (interp_list hp1 ==> interp_list hp2') -> 
          (interp_list (n::hp1) ==> interp_list hp2)
        | None => True
      end.
    Proof.
      intros. generalize (himp_remove_one n (n::hp1) hp2). simpl. 
      destruct (hprop_name_eq n n) ; mysimp.
    Qed.

(*|
This is the key invariant for our `simplify` routine. 
|*)
    Lemma simplify_corr :
      forall hp1 hp0 hp2,
        interp_list (fst (simplify hp0 hp1 hp2)) ==> 
        interp_list (snd (simplify hp0 hp1 hp2)) ->
        interp_list (hp0 ++ hp1) ==> interp_list hp2.
    Proof.
      induction hp1; simpl; intros.
      - rewrite app_nil_r.
        auto.
      - generalize (himp_simp a (hp0 ++ hp1) hp2).
        intros.
        destruct (remove_one a hp2).
        eapply himp_mp.
        eapply H0.
        apply (IHhp1 hp0 l).
        eauto with sep_db.
        eapply (@himp_mp (interp_list ((a::hp1) ++ hp0))).
        sep.
        apply interp_list_comm.
        apply interp_list_comm. 
        generalize (IHhp1 (hp0 ++ (a::nil)) hp2); rewrite <- app_assoc; simpl; auto.
    Qed.

    Lemma flatten_hinterp hp : interp_list (flatten hp) ==> hinterp hp.
    Proof.
      induction hp ; mysimp. sep. apply hyp_comm. apply hyp_emp. sep.
      eapply (@himp_mp (interp_list (flatten hp1) ** interp_list (flatten hp2))). 
      eapply himp_split ; auto. apply interp_list_app.
    Qed.

(*|
This is the proof that the `cross_off` algorithm is correct. That is, if we can prove that the resulting implication holds after crossing off, then the original implication holds. 
|*)
    Lemma cross_off_corr : 
      forall hp1 hp2, 
        let (hp1',hp2') := cross_off hp1 hp2 in 
        (hinterp hp1') ==> (hinterp hp2') ->
        (hinterp hp1) ==> (hinterp hp2).
    Proof.
      intros. remember (cross_off hp1 hp2) as e. unfold cross_off in Heqe.
      destruct e. intros.
      eapply (@himp_mp (interp_list (flatten hp1))) ; [ idtac | apply hinterp_flatten ].
      generalize (simplify_corr (flatten hp1) nil (flatten hp2)). intros.
      eapply himp_mp. eapply flatten_hinterp. simpl in H0. apply H0.
      destruct (simplify nil (flatten hp1) (flatten hp2)). simpl in *.
      repeat rewrite <- collapse_interp. injection Heqe ; intros ; subst. auto.
    Qed.
  End HINTERP.

(*|
Here is an example using the reflection. We have a large implication to prove that demands many re-associations, commutations, etc. So we first build an `hmap` from numbers to `hprop`, then we build syntax that parallels the predicates, being sure to use the right atoms according to the `hmap`, and finally we invoke the `cross_off_corr` lemma to get a much simplified routine. In this case, the simplification gets everything down to `emp ==> emp`.
|*)
  Lemma crazy P Q R S T : Q ** (P ** R) ** (S ** T) ==> T ** (S ** P) ** Q ** R.
    intros.
    generalize (
      let hmap := (0,P)::(1,Q)::(2,R)::(3,S)::(4,T)::nil in 
      let H1 := Atom 1 # (Atom 0 # Atom 2) # (Atom 3 # Atom 4) in 
      let H2 := Atom 4 # (Atom 3 # Atom 0) # Atom 1 # Atom 2 in 
        cross_off_corr hmap H1 H2
    ). 
    simpl.
    intro H. apply H.
    sep.
  Qed.

  Ltac lookup_name term map := 
    match map with 
    | (?n,?P)::?rest => 
        match term with 
        | P => constr:(Some (Atom n))
        | _ => lookup_name term rest
        end
    | _ => constr:(@None Hprop)
    end.
  
  Ltac reflect term map := 
    match term with 
    | star ?P ?Q => 
        match reflect P map with
        | (?t1,?map1) => 
            match reflect Q map1 with
            | (?t2, ?map2) => constr:((Star t1 t2, map2))
            end
        end
    | emp => constr:((Emp, map))
    | _ => 
        match lookup_name term map with
        | Some ?t =>
            constr:((t, map))
        | None =>
            let n := constr:(S (List.length map)) in 
            constr:((Atom n, ((n,term)::map)))
        end
    end.
  
  Ltac cross := 
    match goal with 
    | [ |- ?A ==> ?B ] => 
        let map := constr:(@nil (hprop_name * hprop)) in 
        match reflect A map with 
        | (?t1, ?map1) => 
            match reflect B map1 with 
            | (?t2, ?map2) => 
                apply (cross_off_corr map2 t1 t2) ; simpl
            end
        end
    end.
  
  Lemma crazy2 P Q R S T: Q ** (P ** R) ** (S ** T) ==> T ** (S ** P) ** Q ** R.
    intros.
    cross.
    sep.
  Defined.
  Eval compute in crazy2.
  
  Lemma crazy3 (p q r s:tptr Nat_t) : 
    (p --> 0 ** q --> 1) ** (r --> 2 ** emp) ** (s --> 3) ==> 
     s --> 3 ** q --> 1 ** p --> 0 ** r --> 2.
  Proof.
    intros.
    cross.
    sep.
  Defined.
  
End FunctionalSepIMP.
