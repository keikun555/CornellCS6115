(*|
=======================
Lecture 10: Auto-mation
=======================
|*)

Require Import String.
Open Scope string_scope.
Require Import List.
Open Scope list_scope.
Require Import Lia.
Require Import Arith.
Require Import Nat.

(*|
Type Classses
-------------
Last time we saw type classes, which can be thought of as defining
a kind of interface for a type. For example, the `Show` type class models
types that can be printed as a string.
|*)

Class Show (A:Type) := {
  show : A -> string
  }.

Definition digit2string(d:nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
  | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
  | 8 => "8" | _ => "9"
  end.

Fixpoint digits'(fuel n:nat) (accum : string) : string :=
  match fuel with
  | 0 => accum
  | S fuel' =>
      match n with
      | 0 => accum
      | _ => let d := digit2string(n mod 10) in
             digits' fuel' (n / 10) (d ++ accum)
      end
  end.

Definition digits (n:nat) : string :=
  match digits' n n "" with
  | "" => "0"
  | ds => ds
  end.

Instance natShow : Show nat := {
  show := digits
}.

(* Instance natShow' : Show nat := { *)
(*   show := fun _ => "<dummy>" *)
(* }. *)

Compute show 42.

(*|
Monoids
-------
We already saw definitions monoids when we introduced the module system. Let's see
how we might define monoids using type classes instead.
|*)
Class Monoid (M:Type) := {
    munit : M;
    mplus : M -> M -> M;                                  
  }.

(*|
We can define instances of a monoid, such as strings, integers, and lists.
|*)
Instance StringMonoid : Monoid string := {
    munit := "";
    mplus := String.append;
  }.

Instance NatMonoid : Monoid nat := {
    munit := 0;
    mplus := Nat.add;
  }.

Instance ListMonoid {A:Type} : Monoid (list A) := {
    munit := List.nil;
    mplus := @List.app _;
  }.

(*|
How would we use a monoid? As a running example, let's define a simple interpreter.
|*)

Definition env := string -> nat.

Inductive expr : Type :=
  | Const : nat -> expr
  | Var : string -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr.

(*|
We extend the usual evaluator with two additional inputs:

- A function `f` that maps expressions to monoid elements
- An initial monoid element `m`

Intuitively, this interpreter will encode its steps as a
monoid element, using `f` at each step.
|*)

Fixpoint eval {A:Type} `{Monoid A} (f:expr -> A) (m:A)
  (env : env) (e : expr) : (A * nat) :=
  match e with
  | Const n =>
      (mplus (f e) m, n)
  | Var x =>
      (mplus (f e) m, env x)
  | Plus e1 e2 =>
      let (m1,n1) := eval f m env e1 in
      let (m2,n2) := eval f m env e2 in
      (mplus (mplus m (mplus m1 m2)) (f e), n1 + n2)
  | Mult e1 e2 =>
      let (m1,n1) := eval f m env e1 in
      let (m2,n2) := eval f m env e2 in
      (mplus (mplus m (mplus m1 m2)) (f e), n1 * n2)
  | Minus e1 e2 =>
      let (m1,n1) := eval f m env e1 in
      let (m2,n2) := eval f m env e2 in
      (mplus (mplus m (mplus m1 m2)) (f e), n1 - n2)
  end.

Definition e := Plus (Const 7) (Mult (Const 3) (Const 4)).
Definition init_env := fun (_:string) => 0.
Definition f_count (e:expr) := 1.
Definition f_debug (e:expr) :=
  match e with
  | Const _ => "const,"
  | Var _ => "var,"
  | Plus _ _ => "plus,"
  | Mult _ _ => "mult,"
  | Minus _ _ => "minus,"
  end.

Compute (eval f_count 0 init_env e).
Compute (eval f_debug "" init_env e).

(*|
We can also define a monoid given any pair of monoids, in the obvious way.
|*)
Instance pairMonoid (A B:Type)
  (MA : Monoid A) (MB : Monoid B)
  : Monoid (A*B) :=
{
    munit := (munit, munit);
    mplus := (fun p1 p2 =>
                match p1,p2 with
                | (a1,b1),(a2,b2) => (mplus a1 a2, mplus b1 b2)
                end);
}.

Compute (eval (fun e => (f_count e, f_debug e)) (0,"") init_env e).

(*|
Monads
------
Monads are useful for modeling things that are not just pure functions,
but have some kind of external effect on the world such as
reading input or producing output. They're essential for modeling
statefulness a in pure, stateless, functional language like Coq.

Now we define a generic class for Monads.  Here, it's not a type
that's a monad, but rather a type constructor (i.e., a function from
types to types, aka a functor.  Monads have two operations: `ret` and
`bind`.

If we think of monads as a pattern for encoding effects, such as
exceptions or state or non-determinism, then we can think of `M A` as
describing side-effecting computations that produce a value of type `A`.

The `ret` operation takes a pure (effect-free) value of type `A` and
injects it into the space of side-effecting computations.

The `bind` operation sequences two side-effecting computations,
allowing the latter to depend upon the value of the first one.
|*)

Class Monad (M:Type -> Type) := {
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(*|
We will define the usual, more convenient, notation for `bind`.
|*)
Notation "x <- c1 ;; c2" :=
  (bind c1 (fun x => c2)) 
    (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" :=
  (bind c1 (fun _ => c2)) (at level 100, right associativity).

(*|
One instance of the generic `Monad` class is the `option` monad defined as
follows. It's a bit like exceptions where there is only one possible
exception: `None`.
|*)
Instance OptionMonad : Monad option := {
  ret := fun {A:Type} (x:A) => Some x ; 
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with 
              | None => None
              | Some y => f y
            end
}.

(* Chaining together many functions that take Some types are simpler with above *)

(*|
How might we use this monad? We can 'fix' subtraction, which
ordinarily has odd semantics in Coq, so that any computation of a
negative number fails and that failure propagates to the final result.
|*)
Fixpoint subtract (x y:nat) : option nat := 
  match x, y with 
    | x, 0 => ret x
    | 0, S _ => None
    | S x', S y' => subtract x' y'
  end.

Instance exprShow : Show expr := {
  show := fix show_exp (e:expr) : string := 
              match e with 
                | Const n => show n
                | Var x => x
                | Plus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "+" ++ (show_exp e2) ++ ")"
                | Mult e1 e2 => 
                  "(" ++ (show_exp e1) ++ "*" ++ (show_exp e2) ++ ")"
                | Minus e1 e2 => 
                  "(" ++ (show_exp e1) ++ "-" ++ (show_exp e2) ++ ")"
              end %string
}.

(*|
Now we can write an expression evaluator very conveniently:
|*)
Fixpoint eval' (env:env) (e:expr) : option nat := 
  match e with 
  | Const n => ret n
  | Var x => ret (env x)                   
  | Plus e1 e2 => n1 <- eval' env e1 ;; 
                  n2 <- eval' env e2 ;;
                  ret (n1 + n2)
  | Mult e1 e2 => n1 <- eval' env e1 ;; 
                  n2 <- eval' env e2 ;;
                  ret (n1 + n2)
  | Minus e1 e2 => n1 <- eval' env e1 ;; 
                   n2 <- eval' env e2 ;;
                   subtract n1 n2
  end.

Example e1 : expr := Plus (Const 2) (Minus (Const 0) (Const 1)).
Compute show e1.
Compute (eval' init_env e1).

(*|
This is clearly better than with Coq's usual evaluation for naturals:
|*)
Compute 2 + (0 - 1).

(*|
Going a step further, we can define an exception monad.
|*)

Inductive Exn (A:Type) : Type := 
| Result : A -> Exn A
| Fail : string -> Exn A.
Arguments Result {A}.
Arguments Fail {A}.

Instance ExnMonad : Monad Exn := {
  ret := fun {A:Type} (x:A) => Result x ; 
  bind := fun {A B:Type} (x:Exn A) (f:A -> Exn B) =>
            match x with 
              | Result y => f y
              | Fail s => Fail s
            end
}. 

Fixpoint eval'' (env:env) (e:expr) : Exn nat := 
  match e with 
  | Const n => ret n
  | Var x => ret (env x)
  | Plus e1 e2 => n1 <- eval'' env e1 ;;
                  n2 <- eval'' env e2 ;;
                  ret (n1 + n2)
  | Mult e1 e2 => n1 <- eval'' env e1 ;;
                  n2 <- eval'' env e2 ;;
                  ret (n1 * n2)
  | Minus e1 e2 => n1 <- eval'' env e1 ;; 
                   n2 <- eval'' env e2 ;;
                   match subtract n1 n2 with 
                   | None => Fail "underflow"
                   | Some v => ret v
                   end
  end.

Definition tryCatch {A} (e:Exn A) (s:string) (handler:Exn A) : Exn A := 
  match e with 
    | Fail s' => if string_dec s s' then handler else e
    | _ => e
  end.

Definition eval_to_zero (e:expr) : Exn nat := 
  tryCatch (eval'' init_env e) "underflow" (ret 0).

Check eval_to_zero.
Compute eval'' init_env (Minus (Const 2) (Const 5)).
Compute eval_to_zero (Minus (Const 2) (Const 5)).

(*|
We can also use monads to model stateful computations. To illustrate the idea,
we'll define a simple language of "expressions" with imperative updates.
|*)
Inductive expr_s : Type := 
| Var_s : string -> expr_s
| Plus_s : expr_s -> expr_s -> expr_s
| Times_s : expr_s -> expr_s -> expr_s
| Set_s : string -> expr_s -> expr_s
| Seq_s : expr_s -> expr_s -> expr_s
| If0_s : expr_s -> expr_s -> expr_s -> expr_s.

Definition state := string -> nat.

Definition upd (x:string) (n:nat) (s:state) : state := 
  fun v => if string_dec x v then n else s x.

(*|
An evaluator can be written that passes the state through everywhere, but
it's rather tedious.
|*)
Fixpoint eval_s (e:expr_s)(s:state) : (state * nat) := 
  match e with 
    | Var_s x => (s, s x)
    | Plus_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1+n2)
    | Times_s e1 e2 =>
      let (s1, n1) := eval_s e1 s in
      let (s2, n2) := eval_s e2 s1 in 
      (s2, n1*n2)
    | Set_s x e => 
      let (s1, n1) := eval_s e s in 
      (upd x n1 s1, n1)
    | Seq_s e1 e2 => 
      let (s1, n1) := eval_s e1 s in
      eval_s e2 s1
    | If0_s e1 e2 e3 => 
      let (s1, n1) := eval_s e1 s in 
      match n1 with 
        | 0 => eval_s e2 s1
        | _ => eval_s e3 s1
      end
  end.
        
Definition state_comp (A:Type) := state -> (state * A).

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (s,x)) ; 
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) => 
            fun (s:state) => 
              let (s',v) := c s in 
              f v s'
}.

Definition read (x:string) : state_comp nat := 
  fun s => (s, s x).

Definition write (x:string) (n:nat) : state_comp nat := 
  fun s => (upd x n s, n).

(*|
The evaluator looks much cleaner with the state monad,
using the functions [read] and [write] to capture interaction
with the state.
|*)
Fixpoint eval_sm (e:expr_s) : state_comp nat := 
  match e with 
    | Var_s x => read x
    | Plus_s e1 e2 => 
      n1 <- eval_sm e1 ;; 
      n2 <- eval_sm e2 ;;
      ret (n1 + n2)
    | Times_s e1 e2 =>
      n1 <- eval_sm e1 ;; 
      n2 <- eval_sm e2 ;; 
      ret (n1 * n2)
    | Set_s x e => 
      n <- eval_sm e ;; 
      write x n 
    | Seq_s e1 e2 => 
      _ <- eval_sm e1 ;; 
      eval_sm e2
    | If0_s e1 e2 e3 => 
      n <- eval_sm e1 ;;
      match n with 
        | 0 => eval_sm e2
        | _ => eval_sm e3 
      end
  end.

(*|
We can also use monads to model nondeterministic computation.
|*)

Inductive expr_nd : Type := 
| Choose_nd : list nat -> expr_nd
| Plus_nd : expr_nd -> expr_nd -> expr_nd
| Times_nd : expr_nd -> expr_nd -> expr_nd.

Definition flatten {A:Type} (xs:list (list A)) : list A := 
  fold_right (fun x a => x ++ a) nil xs.

Instance listMonad : Monad list := {
  ret := fun {A:Type} (x:A) => (x::nil) ;
  bind := fun {A B:Type} (c:list A) (f: A -> list B) => 
            flatten (map f c)
}.

Fixpoint eval_nd (e:expr_nd) : list nat := 
  match e with 
  | Choose_nd ns =>
      ns
  | Plus_nd e1 e2 => 
      n1 <- eval_nd e1 ;; 
      n2 <- eval_nd e2 ;; 
      ret (n1 + n2)
  | Times_nd e1 e2 => 
      n1 <- eval_nd e1 ;; 
      n2 <- eval_nd e2 ;;
      ret (n1 * n2)
  end.

Compute eval_nd (Plus_nd
                   (Choose_nd (1::2::nil))
                   (Choose_nd (3::4::nil))).

(*|
Monads ideally satisfy the following laws, and a good exercise is to try to
show that any monad you define satisfies these laws.
|*)

Class Monad_with_Laws (M: Type -> Type) {MonadM : Monad M} := {
  m_left_id : forall {A B:Type} (x:A) (f:A -> M B),
    bind (ret x) f = f x ;
  m_right_id : forall {A B:Type} (c:M A),
    bind c ret = c ;
  m_assoc : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)
}.

Lemma option_left_id : forall {A B:Type } (x:A) (f:A -> option B),
    bind (ret x) f = f x.
Proof.
  intros.
  reflexivity.
Qed.  

Lemma option_right_id : forall {A B:Type } (c:option A),
    bind c ret = c.
Proof.
  intros.
  destruct c; reflexivity. 
Qed.

Lemma option_assoc : forall {A B C} (c:option A)
                            (f:A->option B) (g:B -> option C),
    bind (bind c f) g = bind c (fun x => bind (f x) g).
Proof.
  intros.
  destruct c; reflexivity.
Qed.

(*|
This demonstration is easy for the option monad:
|*)
Instance OptionMonadLaws : @Monad_with_Laws option _ := {
    m_left_id := @option_left_id;
    m_right_id := @option_right_id;
    m_assoc := @option_assoc
  }.

(*|
Proof Automation
----------------

Note: the following material is adapted from EPFL CS 628 by Barrière, Foster, and Pit-Claudel, which in turn is based on materials from Chlipala's FRAP. Used with permission.

Next we'll see how we can use Coq's features for automating proofs, which can
be seen as similar to logic programming.
|*)

(*|
Recall the definition of addition from the standard library.
|*)

Print Nat.add.

(*|
.. massert::

   .s(Print).msg(fix)

This is a recursive definition, in the style of functional programming.  We
might also define addition in style of logic programming, using the inductive relations we have seen in previous lectures.
|*)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(*|
Intuitively, a fact `plusR n m r` only holds when `plus n m = r`.  It is not
hard to prove this correspondence formally.
|*)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
Proof.
  induction n; simpl.
  - constructor.
  - constructor.
    apply IHn.
Qed.

(*|
We see here another instance of the very mechanical proof pattern that came
up before: keep trying constructors and hypotheses.  The tactic `auto` will
automate searching through sequences of that kind, when we prime it with good
suggestions of single proof steps to try, as with this command:
|*)

(* Manipulate the database of hints for auto *)
Local Hint Constructors plusR : core.

(*|
That is, every constructor of `plusR` should be considered as an atomic proof
step, from which we enumerate step sequences.
|*)

Theorem plus_plusR_snazzy : forall n m,
  plusR n m (n + m).
Proof.
  (* info_auto tells us what steps were found *)
  (* induction n; simpl; info_auto. *)
  induction n; simpl; auto.
Qed.

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
Proof.
  intros; induction H; lia.
Qed.

(*|
With the functional definition of `plus`, simple equalities about arithmetic
follow by computation.
|*)

Example four_plus_three : 4 + 3 = 7.
Proof.
  reflexivity.
Qed.

Print four_plus_three.

(*|
With the relational definition, the same equalities take more steps to prove,
but the process is completely mechanical.  For example, consider this
simple-minded manual proof search strategy.  The steps prefaced by `Fail` are
intended to fail; they're included for explanatory value, to mimic a
simple-minded try-everything strategy.

.. coq:: unfold
|*)

Example four_plus_three' : plusR 4 3 7. (* .in *)
Proof.
  Fail apply PlusO. (* .unfold .fails .no-goals *)
  apply PlusS.
  Fail apply PlusO. (* .unfold .fails .no-goals *)
  apply PlusS.
  Fail apply PlusO. (* .unfold .fails .no-goals *)
  apply PlusS.
  Fail apply PlusO. (* .unfold .fails .no-goals *)
  apply PlusS.
  apply PlusO.

(*|
At this point the proof is complete.  It is no doubt clear that a simple
procedure could find all proofs of this kind for us.  We are just exploring
all possible proof trees, built from the two candidate steps `apply PlusO`
and `apply PlusS`.  Thus, `auto` is another great match!
|*)

Restart.
  auto.
Qed.

Print four_plus_three'.

(*|
Let us try the same approach on a slightly more complex goal.
|*)

Example five_plus_three : plusR 5 3 8.
Proof.
  auto. (* .unfold *)

(*|
.. massert::

   .s(auto).g(plusR)

This time, `auto` is not enough to make any progress.  Since even a single
candidate step may lead to an infinite space of possible proof trees,
`auto` is parameterized on the maximum depth of trees to consider.  The
default depth is 5, and it turns out that we need depth 6 to prove the
goal.
|*)

  auto 6.

(*|
Sometimes it is useful to see a description of the proof tree that `auto`
finds, with the `info_auto` variant.
|*)

Restart.
  info_auto 6. (* .unfold *)
Qed.

(*|
The two key components of logic programming are *backtracking* and
*unification*.  To see these techniques in action, consider this further
silly example.  Here our candidate proof steps will be reflexivity and
quantifier instantiation.
|*)

Example seven_minus_three : exists x, x + 3 = 7.
Proof.

(*|
For explanatory purposes, let us simulate a user with minimal understanding
of arithmetic.  We start by choosing an instantiation for the quantifier.
It is relevant that `ex_intro` is the proof rule for existential-quantifier
instantiation.
|*)

  apply ex_intro with 0.
  Fail reflexivity.

(*|
This seems to be a dead end.  Let us *backtrack* to the point where we ran
`apply` and make a better alternative choice.
|*)

Restart.
  apply ex_intro with 4.
  reflexivity.
Qed.

(*|
The above was a fairly tame example of backtracking.  In general, any node in
an under-construction proof tree may be the destination of backtracking an
arbitrarily large number of times, as different candidate proof steps are
found not to lead to full proof trees, within the depth bound passed to `auto`.

Next we demonstrate unification, which will be easier when we switch to the
relational formulation of addition.
|*)

Example seven_minus_three' : exists x, plusR x 3 7.
Proof.

(*|
We could attempt to guess the quantifier instantiation manually as before,
but here there is no need.  Instead of `apply`, we use `eapply`, which
proceeds with placeholder *unification variables* standing in for those
parameters we wish to postpone guessing.
|*)

  eapply ex_intro.

(*|
Now we can finish the proof with the right applications of `plusR`'s
constructors.  Note that new unification variables are being generated to
stand for new unknowns.
|*)

  apply PlusS.
  apply PlusS. apply PlusS. apply PlusS.
  apply PlusO.

(*|
The `auto` tactic will not perform these sorts of steps that introduce
unification variables, but the `eauto` tactic will.  It is helpful to work
with two separate tactics, because proof search in the `eauto` style can
uncover many more potential proof trees and hence take much longer to
run.
|*)

Restart.
  info_eauto 6. (* .unfold *)
Qed.

(*|
This proof gives us our first example where logic programming simplifies
proof search compared to functional programming.  In general, functional
programs are only meant to be run in a single direction; a function has
disjoint sets of inputs and outputs.  In the last example, we effectively ran
a logic program backwards, deducing an input that gives rise to a certain
output.  The same works for deducing an unknown value of the other input.
|*)

Example seven_minus_four' : exists x, plusR 4 x 7.
Proof.
  eauto 6.
Qed.

(*|
By proving the right auxiliary facts, we can reason about specific functional
programs in the same way as we did above for a logic program.  Let us prove
that the constructors of `plusR` have natural interpretations as lemmas about
`plus`.  We can find the first such lemma already proved in the standard
library, using the `Search` command to find a library function proving
an equality whose lefthand or righthand side matches a pattern with
wildcards.
|*)

Search (O + _).

(*|
The command `Hint Immediate` asks `auto` and `eauto` to consider this lemma
as a candidate step for any leaf of a proof tree, meaning that all premises
of the rule need to match hypotheses.
|*)

Local Hint Immediate plus_O_n : core.

(*|
The counterpart to `PlusS` we will prove ourselves.
|*)

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
Proof.
  lia.
Qed.

(*|
The command `Hint Resolve` adds a new candidate proof step, to be attempted
at any level of a proof tree, not just at leaves.
|*)

Local Hint Resolve plusS : core.

(*|
Now that we have registered the proper hints, we can replicate our previous
examples with the normal, functional addition `plus`.
|*)

Example seven_minus_three'' : exists x, x + 3 = 7.
Proof.
  eauto 6.
Qed.

Example seven_minus_four : exists x, 4 + x = 7.
Proof.
  eauto 6.
Qed.

(*|
This new hint database is far from a complete decision procedure, as we see in
a further example that `eauto` does not solve.
|*)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  info_eauto 6.
Fail Qed.
Abort.

(*|
A further lemma will be helpful.
|*)

Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
Proof.
  lia.
Qed.

Local Hint Resolve plusO : core.

(*|
Note that, if we consider the inputs to `plus` as the inputs of a
corresponding logic program, the new rule `plusO` introduces an ambiguity.
For instance, a sum `0 + 0` would match both of `plus_O_n` and `plusO`,
depending on which operand we focus on.  This ambiguity may increase the
number of potential search trees, slowing proof search, but semantically it
presents no problems, and in fact it leads to an automated proof of the
present example.
|*)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
Proof.
  eauto 7.
Qed.

(*|
.. note::

   Instead of adding `plusO` to the `core` database explicitly, we could configure it to allow more flexibility in unification:
|*)

Section AllowUnfold.
  Remove Hints plusO : core.
  Remove Hints plus_n_O : core.

  Example seven_minus_four_zero' : exists x, 4 + x + 0 = 7.
  Proof.
    Fail solve [eauto 10]. (* .unfold .fails .no-goals *)
  Abort.

  Hint Constants Transparent : core.

  Example seven_minus_four_zero' : exists x, 4 + x + 0 = 7.
  Proof.
    info_eauto 9. (* .unfold *)
  Qed.

(*|
   This works because `4 + x` simplifies to `S (S (S (S x)))`, which allows `plusS` to apply; should the term have been written as `x + 4` instead, it would not have helped:
|*)

  Example seven_minus_four_zero'' : exists x, x + 4 + 0 = 7.
  Proof.
    Fail solve [eauto 10].
  Abort.
End AllowUnfold.

(*|
Just how much damage can be done by adding hints that grow the space of
possible proof trees?  A classic gotcha comes from unrestricted use of
transitivity, as embodied in this library theorem about equality:
|*)

Check eq_trans.

(*|
Hints are scoped over sections, so let us enter a section to contain the
effects of an unfortunate hint choice.
|*)

Section slow.
  Hint Resolve eq_trans : core.

(*|
The following fact is false, but that does not stop `eauto` from taking a
very long time to search for proofs of it.  We use the handy `Time` command
to measure how long a proof step takes to run.  None of the following steps
make any progress.
|*)

  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
    Time eauto 2.
    Time eauto 3.
    Time eauto 4.
    Time eauto 5.

(*|
We see worrying exponential growth in running time, and the `debug`
tactical helps us see where `eauto` is wasting its time, outputting a
trace of every proof step that is attempted.  The rule `eq_trans` applies
at every node of a proof tree, and `eauto` tries all such positions.
|*)

    debug eauto 3. (* .unfold .no-goals *)
  Abort.
End slow.

(*|
Sometimes, though, transitivity is just what is needed to get a proof to go
through automatically with `eauto`.  For those cases, we can use named
*hint databases* to segregate hints into different groups that may be called
on as needed.  Here we put `eq_trans` into the database `slow`.
|*)

Local Hint Resolve eq_trans : slow.

Example from_one_to_zero : exists x, 1 + x = 0.
Proof.
  Time eauto.

(*|
This `eauto` fails to prove the goal, but at least it takes substantially
less than the 2 seconds required above!
|*)

Abort.

(*|
One simple example from before runs in the same amount of time, avoiding
pollution by transitivity.
|*)

Example seven_minus_three_again : exists x, x + 3 = 7.
Proof.
  Time eauto 6.
Qed.

(*|
When we *do* need transitivity, we ask for it explicitly.
|*)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
Proof.
  info_eauto with slow. (* .unfold *)
Qed.

(*|
The `info` trace shows that `eq_trans` was used in just the position where it
is needed to complete the proof.  We also see that `auto` and `eauto` always
perform `intro` steps without counting them toward the bound on proof-tree
depth.

Searching for Underconstrained Values
=====================================

Recall the definition of the list length function.
|*)

Print Datatypes.length.

(*|
This function is easy to reason about in the forward direction, computing
output from input.
|*)

Example length_1_2 : length (1 :: 2 :: nil) = 2.
Proof.
  auto.
Qed.

Print length_1_2.

(*|
As in the last section, we will prove some lemmas to recast `length` in
logic-programming style, to help us compute inputs from outputs.
|*)

Theorem length_O : forall A, length (nil (A := A)) = O.
Proof.
  reflexivity.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
Proof.
  simpl; congruence.
Qed.

Local Hint Immediate length_O : core.
Local Hint Resolve length_S : core.

(*|
Let us apply these hints to prove that a `list nat` of length 2 exists.
|*)

Example length_is_2 : exists ls : list nat, length ls = 2.
Proof.
  eauto.

(*|
Coq leaves for us two subgoals to prove... `nat`?!  We are being asked to
show that natural numbers exists.  Why?  Some unification variables of that
type were left undetermined, by the end of the proof.  Specifically, these
variables stand for the 2 elements of the list we find.  Of course it makes
sense that the list length follows without knowing the data values.  In Coq
8.6 and up, the `Unshelve` command brings these goals to the forefront,
where we can solve each one with `exact O`, but usually it is better to
avoid getting to such a point.

To debug such situations, it can be helpful to print the current internal
representation of the proof, so we can see where the unification variables
show up.
|*)

  Show Proof.
Abort.

(*|
Paradoxically, we can make the proof-search process easier by constraining
the list further, so that proof search naturally locates appropriate data
elements by unification.  The library predicate `Forall` will be helpful.
|*)

Print Forall.

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 42) ls.
Proof.
  eauto 9.
Qed.

(*|
We can see which list `eauto` found by printing the proof term.
|*)

Print length_is_2.

(*|
Let us try one more, fancier example.  First, we use a standard higher-order
function to define a function for summing all data elements of a list.
|*)

Definition sum := fold_right plus O.

(*|
Another basic lemma will be helpful to guide proof search.
|*)

Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
Proof.
  lia.
Qed.

Local Hint Resolve plusO' : core.

(*|
Finally, we meet `Hint Extern`, the command to register a custom hint.  That
is, we provide a pattern to match against goals during proof search.
Whenever the pattern matches, a tactic (given to the right of an arrow `=>`)
is attempted.  Below, the number `1` gives a priority for this step.  Lower
priorities are tried before higher priorities, which can have a significant
effect on proof-search time, i.e. when we manage to give lower priorities to
the cheaper rules.
|*)

Local Hint Extern 1 (sum _ = _) => simpl : core.

(*|
Now we can find a length-2 list whose sum is 0.
|*)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
Proof.
  eauto 7.
Qed.

Print length_and_sum.

(*|
Printing the proof term shows the unsurprising list that is found.  Here is
an example where it is less obvious which list will be used.  Can you guess
which list `eauto` will choose?
|*)

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
Proof.
  eauto 15.
Qed.

Print length_and_sum'.

(*|
We will give away part of the answer and say that the above list is less
interesting than we would like, because it contains too many zeroes.  A
further constraint forces a different solution for a smaller instance of the
problem.
|*)

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
Proof.
  eauto 11.
Qed.

Print length_and_sum''.

(*|
Revisiting `eval`
-----------------

The same techniques apply to the `eval` function that we defined previously.
|*)

Module Simple.
  Notation var := string.
  Open Scope string_scope.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Minus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Coercion Const : nat >-> arith.
  Coercion Var : var >-> arith.
  Infix "+" := Plus : arith_scope.
  Infix "-" := Minus : arith_scope.
  Infix "*" := Times : arith_scope.
  Delimit Scope arith_scope with arith.

  Definition valuation := var -> option nat.

  Definition empty : valuation := fun _ => None.

  Definition get (x:var) (v:valuation) : option nat := v x.

  Definition set (x:var) (n:nat) (v:valuation) : valuation :=
    fun y =>
      match string_dec x y with
      | left H => Some n
      | right H' => get y v
      end.

(*|
We'll define `interp` as a relation, for maximum `eauto`-friendliness.
|*)

  Inductive interp (v: valuation): forall (e : arith) (n: nat), Prop :=
  | InterpConst (n: nat) : interp v (Const n) n
  | InterpVarNotFound (x: var) (n: nat) :
    get x v = None ->
    interp v (Var x) 0
  | InterpVarFound (x: var) (n: nat) :
    get x v = Some n ->
    interp v (Var x) n
  | InterpPlus (e1 e2: arith) n1 n2:
    interp v e1 n1 -> interp v e2 n2 ->
    interp v (Plus e1 e2) (n1 + n2)
  | InterpMinus (e1 e2: arith) n1 n2:
    interp v e1 n1 -> interp v e2 n2 ->
    interp v (Minus e1 e2) (n1 - n2)
  | InterpTimes (e1 e2: arith) n1 n2:
    interp v e1 n1 -> interp v e2 n2 ->
    interp v (Times e1 e2) (n1 * n2).

  Inductive cmd :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (e : arith) (then_ else_ : cmd)
  | While (e : arith) (body : cmd).

  Notation "x <- e" := (Assign x e%arith) (at level 75).
  Infix ";;;" := (* This one changed to avoid parsing clashes. *)
    Sequence (at level 76).
  Notation "'when' e 'then' then_ 'else' else_ 'done'" :=
    (If e%arith then_ else_) (at level 75, e at level 0).
  Notation "'while' e 'loop' body 'done'" :=
    (While e%arith body) (at level 75).

  Example factorial :=
    "output" <- 1;;;
    while "input" loop
      "output" <- "output" * "input";;;
      "input" <- "input" - 1
    done.

  Inductive eval : valuation -> cmd -> valuation -> Prop :=
  | EvalSkip : forall v,
    eval v Skip v
  | EvalAssign : forall v x e n,
    interp v e n ->
    eval v (Assign x e) (set x n v)
  | EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
  | EvalIfTrue : forall v e then_ else_ v' n,
    interp v e n
    -> n <> 0
    -> eval v then_ v'
    -> eval v (If e then_ else_) v'
  | EvalIfFalse : forall v e then_ else_ v' n,
    interp v e n
    -> n = 0
    -> eval v else_ v'
    -> eval v (If e then_ else_) v'
  | EvalWhileTrue : forall v e body v' v'' n,
    interp v e n
    -> n <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
  | EvalWhileFalse : forall v e body n,
    interp v e n
    -> n = 0
    -> eval v (While e body) v.

(*|
Our first proof is not the most satisfying:
|*)

  Theorem factorial_2 : exists v, eval (set "input" 3 empty) factorial v
                             /\ get "output" v = Some 6.
  Proof.
    unfold factorial. (* .unfold *)

(*|
`econstructor` simply loops, repeatedly applying `EvalWhileTrue`:
|*)

    Fail Timeout 2 repeat econstructor. (* .fails .unfold .no-goals *)

(*|
The manual alternative does not look great:
|*)

    eapply ex_intro.
    split.
    - eapply EvalSeq.
      + apply EvalAssign.
        apply InterpConst.
      + eapply EvalWhileTrue.
        * apply InterpVarFound; reflexivity.
        * congruence.
        * eapply EvalSeq.
          -- apply EvalAssign.
             apply InterpTimes.
             ++ apply InterpVarFound.
                reflexivity.
             ++ apply InterpVarFound.
                reflexivity.
          -- apply EvalAssign.
             apply InterpMinus.
             ++ apply InterpVarFound.
                reflexivity.
             ++ apply InterpConst.
        * eapply EvalWhileTrue.
          -- apply InterpVarFound.
             reflexivity.
          -- simpl; congruence.
          -- eapply EvalSeq.
             ++ apply EvalAssign.
                apply InterpTimes.
                ** apply InterpVarFound.
                   reflexivity.
                ** apply InterpVarFound.
                   reflexivity.
             ++ apply EvalAssign.
                apply InterpMinus.
                ** apply InterpVarFound.
                   reflexivity.
                ** apply InterpConst.
          -- eapply EvalWhileTrue.
             ++ apply InterpVarFound.
                reflexivity.
             ++ simpl; congruence.
             ++ eapply EvalSeq.
                ** apply EvalAssign.
                   apply InterpTimes.
                   --- apply InterpVarFound.
                       reflexivity.
                   --- apply InterpVarFound.
                       reflexivity.
                ** apply EvalAssign.
                   apply InterpMinus.
                   --- apply InterpVarFound.
                       reflexivity.
                   --- apply InterpConst.
             ++ eapply EvalWhileFalse.
                ** apply InterpVarFound.
                   reflexivity.
                ** reflexivity.
    - reflexivity.

(*|
Thankfully, with just a few hints, we can get eauto to do all the work for us!
|*)

      Restart.

      Hint Constructors interp eval : core.
      Hint Extern 1 => (simpl; congruence) : core.
      Hint Extern 1 => reflexivity : core.

      unfold factorial.
      debug eauto 50. (* .unfold *)
  Qed.
End Simple.

(*|
Backtracking without `auto`
---------------------------

We have already seen backtracking with `eauto`.  Let us see another with “multiple successes”.
|*)

Inductive EasyPeasy :=
| Nope0 (n: nat): n < 0 -> EasyPeasy
| Yep   (n: nat): n = 0 -> EasyPeasy
| Nope1 (n: nat): n < 0 -> EasyPeasy.

(*|
Note the order of constructors, chosen to trick `constructor` into trying `Nope` before `Yep`.
|*)

Hint Constructors EasyPeasy : core.

Goal EasyPeasy.

(*|
Unsurprisingly, a plain application of econstructor does not solve the goal.  In fact, it leaves an unprovable goal instead, because the argument of `Nope0` is not satisfiable:
|*)

  econstructor. (* .unfold *)

(*|
Uh oh.
|*)

  Restart. (* .unfold *)

(*|
Also unsurprisingly, `eauto` solves the goal (it tries constructors in reverse order, but the order is irrelevant for correctness, since it backtracks after attempting `Nope1`):
|*)

  debug eauto. (* .unfold *)

(*|
More interesting is what happens if we *chain* the `constructor` tactic with another one:
|*)

  Restart. (* .unfold *)
  econstructor; reflexivity.

(*|
The `econstructor` tactic produces a *stream* of proof states to attempt (one per applicable constructor, not just one for the first applicable constructor).

When the control flow reaches a period, all candidate states except the first are discarded.

Any time a tactic fails before reaching a period, however, the Ltac engine *backtracks*: it rewinds execution to the last `;` and tries the next available proof state in the stream produced by earlier tactics.

Here `reflexivity` fails to solve the goal `?n < 0` (the result of applying `Nope0`), so the Ltac interpreter backtracks to the next state produced by `constructor`, which is `?n = 0` (the result of applying `Yep`).  At this point, `reflexivity` completes the proof.

Another way to force backtracking is by inserting explicit failures.  The following does not solve the goal, because `eauto` does not fail if it cannot solve the goal:
|*)

  Restart. (* .unfold *)
  econstructor; eauto. (* .unfold *)

(*|
In contrast, the following works, because the `fail` tactic forces backtracking:
|*)

  Restart. (* .unfold *)
  econstructor; eauto; fail.

(*|
Or, we can create backtracking points by hand using the `+` operator:
|*)

  Restart. (* .unfold *)
  (eapply Nope0 + eapply Yep + eapply Nope1); reflexivity.

(*|
… or, should we want to condition the application of any of the branches, we can create backtracking points with `multimatch` instead:
|*)

  Restart. (* .unfold *)

  Fail match goal with
       | _ => eapply Nope0
       | _ => eapply Yep
       end; reflexivity. (* .unfold .fails .no-goals *)

  multimatch goal with
  | _ => eapply Nope0
  | _ => eapply Yep
  end; reflexivity.
Qed.

(*|
.. note:: Observing backtracking

   Here is a quick and dirty way to observe the backtracking that Ltac performs: printing the goal with `idtac`:
|*)

Goal EasyPeasy.
  econstructor;
    match goal with
    | [  |- ?g ] => idtac "The goal is:" g
    end;
    reflexivity. (* .unfold *)
Qed.

(*|
Other operators that control backtracking, including `once`, first`, and `[> … ]`, are documented in the reference manual.
|*)

(*|
Again, the moral of the story is: while proof search in Coq often feels
purely functional, unification variables allow imperative side effects to
reach across subgoals.  That's a tremendously useful feature for effective
proof automation, but it can also sneak up on you at times.

More on `auto` Hints
====================

Let us stop at this point and take stock of the possibilities for `auto` and
`eauto` hints.  Hints are contained within *hint databases*, which we have
seen extended in many examples so far.  When no hint database is specified, a
default database is used.  Hints in the default database are always used by
`auto` or `eauto`.  The chance to extend hint databases imperatively is
important, because, in Ltac programming, we cannot create "global variables"
whose values can be extended seamlessly by different modules in different
source files.  We have seen the advantages of hints so far, where a proof
script using `auto` or `eauto` can automatically adapt to presence of new
hints.

The basic hints for `auto` and `eauto` are:

- `Hint Immediate lemma`, asking to try solving a goal immediately by
  applying a lemma and discharging any hypotheses with a single proof step
  each

- `Hint Resolve lemma`, which does the same but may add new premises that are
  themselves to be subjects of nested proof search

- `Hint Constructors pred`, which acts like `Resolve` applied to every
  constructor of an inductive predicate

- `Hint Unfold ident`, which tries unfolding `ident` when it appears at the
  head of a proof goal

Each of these `Hint` commands may be used with a suffix, as in
`Hint Resolve lemma : my_db`, to add the hint only to the specified database,
so that it would only be used by, for instance, `auto with my_db`.  An
additional argument to `auto` specifies the maximum depth of proof trees to
search in depth-first order, as in `auto 8` or `auto 8 with my_db`.  The
default depth is 5.

All of these `Hint` commands can also be expressed with a more primitive hint
kind, `Extern`.

In general, many proofs can be automated in pleasantly modular ways with deft
combinations of `auto` and `autorewrite`.
|*)

