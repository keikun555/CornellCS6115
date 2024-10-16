(** Homework 4: Program Transformations *)

Require Import Lia.
Require Import List.
Import ListNotations.
Require Import String.

(*|
Modern compilers achieve excellent performance by leveraging a wide variety of
program transformations.  For example, GCC (the GNU C compiler) version 10.2
produces the *exact same* assembly code for the following two programs (if you
want to see for yourself, try it at the Compiler Exporer [https://godbolt.org]!

1. Recursive version with accumulator, naive division and modulo, no function
   inlining, multiple returns, redundant ``+ 1``, not tail-recursive::

      static unsigned int affine(unsigned int n,
                                 unsigned int slope,
                                 unsigned int offset) {
          return n * slope + offset;
      }

      unsigned int collatz1(unsigned int start) {
          if (start == 1)
            return 0;
          else if (start % 2 == 0)
            return collatz1(start / 2) + 1;
          else
            return collatz1(affine(start, 3, 1)) + 1;
      }

2. Single loop, inlined function, bitwise arithmetic::

      unsigned int collatz2(unsigned int start) {
          unsigned int flight = 0;
          while (start != 1) {
              flight++;
              if ((start & 1) == 0) {
                  start = start >> 1;
              } else {
                  start = start * 2 + start + 1;
              }
          }
          return flight;
      }

The way GCC achieves this is by applying a sequence of transformation passes on
the code: you can see the output of each intermediate pass (all ~320 of them)
using ``gcc -O3 -fdump-tree-all -fdump-rtl-all -c collatz1.c``.  For instance,
the ``ssa`` pass puts the code into a form similar to the three-address code
that we saw in class, the ``tailr1`` passes convert the recursive function to a
loop, etc.

Students interested in an introduction to the magic of modern compiler
optimizations might enjoy Matt Godbolt's 2017 talk at CPPCon, *What Has My
Compiler Done for Me Lately? Unbolting the Compiler's Lid*
(https://www.youtube.com/watch?v=bSkpMdDe4g4).

In this lab, we'll see how formal methods can help us reason about the
correctness of these optimization passes, focusing on a few commonly used
optimizations.

*A few notes of caution*:

- Many of the proofs in this lab can be a bit long to complete fully manually:
  we encourage you to try your hand at simple automation.  However, make sure
  that your whole file compiles in a reasonable amount of time (at most a minute
  or two).

- When decomposed into the right sequence of lemmas, most of the theorems in
  this exercise set have relatively short proofs.  The best way to find these
  lemmas is to approach each problem cautiously, trying to work an understanding
  of the proof before diving into long series of `inversion`, `econstructor`, etc.
  In general, it's also a good idea to admit lemmas until you are sure that they
  allow you to prove the complete theorem, then go back and prove the lemmas —
  but do take the time to convince yourself that your lemmas make sense, so that
  you don't waste time using incorrect lemmas.

- We have included plenty of hints below in the HINTS section of the 
  signature file.
|*)

(*|
IMPORTANT: The language we use in this exersice set is defined in [Lang.v]. We will also make use of an implementation of finite maps in [Maps.v].
Please skim [Maps.v] and read [Lang.v] before you go further.
|*)
Require Import Lang.
Require Import Map.

(*|
As a sanity check, we can prove that the semantics is deterministic:
|*)

Lemma eval_deterministic :
  forall phi c v0 v1 v2,
    eval phi v0 c v1 ->
    eval phi v0 c v2 ->
    v1 = v2.
Proof.
  Admitted.

(*|
Now let's check that our semantics compute the right values.  The `eval_intro`
tactic below may be useful for the following proofs.  You do not need to
understand its implementation; what matters is that it attempts to construct a
proof of `eval`, and it chooses between `EvalWhileTrue` and `EvalWhileFalse` and
between `EvalIfTrue` and `EvalIfFalse` by attempting to satisfy all the premises
of each of them.  It stops if it cannot conclusively decide which case applies.
|*)

Ltac simpl_maps := autorewrite with core in *.
Ltac eval_intro :=
  let eval_intro_solve :=
      intros; simpl in *; simpl_maps;
      lazymatch goal with
      | [  |- eval _ _ _ _ ] => idtac
      | _ => intuition congruence
      end in
  lazymatch goal with
  | [  |- eval _ _ Skip _ ] =>
    apply EvalSkip
  | [  |- eval _ _ (Assign _ _) _ ] =>
    eapply EvalAssign
  | [  |- eval _ _ (AssignCall _ _ _ _) _ ] =>
    eapply EvalAssignCall
  | [  |- eval _ _ (Sequence _ _) _ ] =>
    eapply EvalSequence
  | [  |- eval _ _ (While _ _) _ ] =>
    (eapply EvalWhileTrue + eapply EvalWhileFalse); eval_intro_solve
  | [  |- eval _ _ (If _ _ _) _ ] =>
    (eapply EvalIfTrue + eapply EvalIfFalse); eval_intro_solve
  | [  |- eval _ _ ?cmd _ ] =>
    unfold cmd at -1 || unfold cmd
  | [  |- interp_arith _ _ = _ _ ] => econstructor
  | _ => progress (intros; simpl in *; simpl_maps) || (intuition congruence)
  end.

(*|
To call functions, we need to specify their signatures:
|*)

Notation TimesThreePlus1_signature := (("n", ""), "n", Times3Plus1Body).
Notation Fact_signature := (("n", ""), "f", FactBody).
Notation FactRec_signature := (("n", ""), "f", FactRecBody).
Notation FactTailRec_signature := (("n", "acc"), "f", FactTailRecBody).
Notation Collatz_signature := (("start", "flight"), "flight", CollatzBody).

(*|
And to make goals more readable, we'll define a shorthand
`eval_returns phi v cmd outVar result`, which means “running `cmd` in
environment `phi` with valuation `v` returns `result` in `outVar`”:
|*)

Definition eval_returns phi v cmd outVar result :=
  exists v', eval phi v cmd v' /\ v' $? outVar = Some result.

(*|
Here are a few examples of execution:
|*)

Example TwoPlusTwoIsFour :
  eval_returns $0 $0 ("out" <- 2 + 2) "out" 4.
Proof.
  eexists.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Example EvalVars :
  eval_returns
    $0 $0
    ("x" <- 1 + 1;;
     "x" <- "x" + "x" + "y")
    "x" 4.
Proof.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Example EvalSimpleArith :
  eval_returns
    $0 $0
    ("out" <- ((((14 >> 1) + 8 / 4 / 2) * (7 - 2)) << 1) + 2 == 82)
    "out" 1.
Proof.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Example EvalTimes3Plus1: forall n,
    eval_returns $0 ($0 $+ ("n", n)) Times3Plus1Body "n" (3 * n + 1).
Proof.
  eexists; intuition idtac; repeat eval_intro.
  f_equal; lia.
Qed.

Lemma EvalFact6:
    eval_returns $0 ($0 $+ ("n", 3)) FactBody "f" 6.
Proof.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Notation Fact_env :=
  ($0
    $+ ("fact", Fact_signature)
    $+ ("fact_r", FactRec_signature)
    $+ ("fact_tr", FactTailRec_signature)).

Lemma EvalFactRec6:
    eval_returns Fact_env ($0 $+ ("n", 3)) FactRecBody "f"6.
Proof.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Lemma EvalFactTailRec6:
    eval_returns Fact_env ($0 $+ ("n", 3) $+ ("acc", 1)) FactTailRecBody "f" 6.
Proof.
  eexists; intuition idtac; repeat eval_intro.
Qed.

Notation Collatz_env :=
  ($0
    $+ ("collatz", Collatz_signature)
    $+ ("times3plus1", TimesThreePlus1_signature)).

Lemma collatz_result:
    eval_returns Collatz_env ($0 $+ ("flight", 0) $+ ("start", 10)) CollatzBody "flight" 6.
Proof.
  (* This proof is larger, so `eval_intro` will take a bit longer (a few seconds): *)
  eexists; intuition idtac; repeat eval_intro.
Qed.

(*|
Arithmetic optimizations
========================

Let's teach our compiler a few arithmetic optimizations.  All these
optimizations will be local, so we'll define them in terms of `interp_binop`:
every optimization will take a binary operator and two optimized expressions,
and it will return an optimized expression, without recursing.

Below, we will discuss four different flavors of arithmetic optimizations.  You
do not have to implement and prove all of them; instead, you just need to
implement the first one (constant folding) and one of the next three; you are
free to pick which one.

Here are the optimizations:

1. Folding constant subexpressions using properties of `+`, `*`, `/`
2. Precomputing constant subexpressions
3. Rewriting `*`, `/`, `mod` of powers of 2
4. Rewriting `*` as a sum of shifts

Options 4 is quite a bit more challenging than the others… but also quite
interesting!

To make sure that our optimizations are reasonable, we'll introduce a very
simple cost model; it gives us an estimate of the time it takes to run an
operation:
|*)

Fixpoint arith_cost (e: expr) : nat :=
  match e with
  | Binop b e1 e2 =>
    match b with
    | LogAnd | Eq | ShiftLeft | ShiftRight | Plus | Minus => 1
    | Times => 8
    | Divide | Modulo => 16
    end + arith_cost e1 + arith_cost e2
  | _ => 0
  end.

(*|
Constant folding
----------------

We'll start by applying the following rules:

- `n + 0 → n`
- `n * 0 → 0`
- `n / 1 → n`

This set is not complete in any sense; in addition to these three rewrites, we
encourage you to add extras and see how robust your proofs are to the changes.
Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_fold (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_fold !_ !_ !_ /. (* Coq magic *)

Example opt_binop_fold_test1 :
  opt_binop_fold Plus "x" 0 = "x".
Proof.
Admitted.

Lemma opt_binop_fold_sound : forall b e1 e2 v,
    interp_arith (opt_binop_fold b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Precomputation
--------------

This is the first of three options.  If you implement this optimization, you do
not have to implement the next two.

We'll teach the compiler to simplify constant expressions: if an operator has
two constants as arguments, we'll precompute the value.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_precompute (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_precompute !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_precompute_sound : forall b e1 e2 v,
    interp_arith (opt_binop_precompute b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Optimizing power-of-2 operations
--------------------------------

This is the second of three options.  If you implement this optimization, you do
not have to implement the other two.

Operations like multiplication, division, and modulo are typically relatively
slow, so we'd like to implement them more efficiently.  We'll use the following
trick:

- `n / 2^k` → `n >> k`
- `n * 2^k` → `n << k`
- `n mod 2^k` → `n & (2^k - 1)`

Here is a function that returns `Some k` if its input is equal to `2^k` and
`None` otherwise:
|*)

Definition log2 (n: nat) :=
  let l := Nat.log2 n in
  if 2 ^ l =? n then Some l else None.

Lemma log2_sound : forall n l, log2 n = Some l -> n = 2^l.
Proof.
  unfold log2; intros; simpl in *.
  destruct (2 ^ Nat.log2 n =? n) eqn: Heq; try congruence.
  inversion H; subst; clear H.
  apply Nat.eqb_eq in Heq; congruence.
Qed.

Lemma log2_complete : forall n, log2 n = None -> forall l, n <> 2^l.
Proof.
  unfold log2, not; simpl; intros.
  replace l with (Nat.log2 n) in *
    by (subst; rewrite Nat.log2_pow2; eauto using Nat.le_0_l).
  rewrite <- H0 in H. rewrite Nat.eqb_refl in H.
  congruence.
Qed.

(*|
Use `log2` to define the transformation above.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_log2 (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_log2 !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_log2_sound : forall b e1 e2 v,
    interp_arith (opt_binop_log2 b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Rewriting multiplications
-------------------------

This is the last of three options.  If you implement this optimization, you do
not have to implement the previous two.

All numbers can be written as sums of powers of two, so we can replace all
mutiplications by sums of bitshifts:

- `n * ∑_k 2^k` → `∑_k n << k`

Here is a function that computes a number's decomposition by returning the
offsets of its nonzero bits:
|*)

Fixpoint log2sp (n: positive) (pos: nat) :=
  match n with
  | xI x => pos :: log2sp x (S pos)
  | xO x => log2sp x (S pos)
  | xH => [pos]
  end.

Definition log2s (n: nat) :=
  match N.of_nat n with
  | N0 => []
  | Npos p => log2sp p 0
  end.

(*|
Computing `log2s 13` returns [0;2;3], because 13 = 2^0 + 2^2 + 2^3.
|*)

Compute log2s 13.

Lemma log2sp_sound : forall p j,
    List.fold_right
      (fun k acc => 2 ^ k + acc)
      0 (log2sp p j) =
    (2 ^ j * N.to_nat (Npos p)).
Proof.
  induction p; simpl; intros.
  3: rewrite ?Nat.add_0_r, ?Nat.mul_1_r; congruence.
  all: rewrite IHp, Nat.pow_succ_r by lia.
  all: rewrite ?Pnat.Pos2Nat.inj_xO, ?Pnat.Pos2Nat.inj_xI.
  all: lia.
Qed.

Lemma log2s_sound : forall n,
    List.fold_right (fun k acc => 2^k + acc) 0 (log2s n) = n.
Proof.
  unfold log2s; simpl; intros.
  rewrite <- (Nat2N.id n) at 2.
  destruct (N.of_nat n).
  - simpl. reflexivity.
  - rewrite log2sp_sound, Nat.mul_1_l; reflexivity.
Qed.

(*|
Use `log2s` to define a local optimization that implements the transformation above.

Note that your optimization function should *not* be recursive!  We will
implement repeated rule application later on top of your function.
|*)

Definition opt_binop_bitwise (b: BinopName) (e1 e2: expr) : expr.
Admitted.
Arguments opt_binop_bitwise !_ !_ !_ /. (* Coq magic *)

Lemma opt_binop_bitwise_sound : forall b e1 e2 v,
    interp_arith (opt_binop_bitwise b e1 e2) v =
    interp_binop b (interp_arith e1 v) (interp_arith e2 v).
Proof.
Admitted.

(*|
Putting it all together
-----------------------

We're ready to apply our optimizations over the whole AST of an expression:
write a recursive function which, at each `Binop` node of the expression,
applies all optimizations that you implemented and proved (at least
`opt_arith_constprop` and one of the next three).

Mind the order in which the optimizations are applied!
|*)

Definition opt_arith (e: expr) : expr.
Admitted.
Arguments opt_arith !e /. (* Coq magic *)

Example opt_arith_fold_test1 :
  opt_arith (1 + "z" * ("y" * ("x" * (0 + 0 / 1))))%expr =
  (1)%expr.
Proof.
Admitted.

Example opt_arith_precompute_test1:
  opt_arith (("x" + (3 - 3)) / (0 + 1) + ("y" + "y" * 0))%expr =
  ("x" + "y")%expr.
Proof.
Admitted.

Example opt_arith_precompute_test2 :
  opt_arith ((("y" / ("x" * 0 + 7 / 1)) mod (12 - 5)) / (2 * 3))%expr =
  (("y" / 7) mod 7 / 6)%expr.
Proof.
Admitted.

Example opt_arith_log2_test1 :
  opt_arith (("y" * 8) mod 8 / 4)%expr =
  (("y" << 3 & 7) >> 2)%expr.
Proof.
Admitted.

Example opt_arith_log2_test2 :
  opt_arith (("y" * 1 + (4 + 0)) mod 9 / 3)%expr =
  (("y" + 4) mod 9 / 3)%expr.
Proof.
Admitted.

Example opt_arith_bitwise_test1 :
  opt_arith ("y" * 13)%expr =
  ("y" + (("y" << 2) + ("y" << 3)))%expr.
Proof.
Admitted.

Example opt_arith_bitwise_test2 :
  opt_arith ("y" * (3 + 0))%expr =
  ("y" + ("y" << 1))%expr.
Proof.
Admitted.


Lemma opt_arith_sound : forall e v,
    interp_arith (opt_arith e) v =
    interp_arith e v.
Proof.
Admitted.

(*|
Optional: cost modeling
-----------------------

*This part is completely optional.*

Using the cost model introduced earlier, prove that your optimizer does reduce costs:
|*)

Lemma opt_arith_ok : forall e,
    arith_cost (opt_arith e) <= arith_cost e.
Proof.
Admitted.

(*|
That's it for expression optimizations!  Now, let's see command optimizations.

Command optimizations
=====================

In this part, we'll consider three optimizations.  You do not have to implement
all three; instead, you need to implement the first one and either one of the
last two:

- Simple dead-code elimination, by removing `Skip` nodes
- Constant propagation
- Loop unrolling

Loop unrolling is trickier than constant propagation.  And if you want a
challenge, constant propagation includes an *optional* generalization that makes
it *a lot* harder.

Oh, and if you're not excited about either of these optimizations, feel free to
pick a different one!  Just make sure that you run it by us so we can confirm
that it's reasonably difficult.  Want some ideas?  Check out
https://gcc.gnu.org/onlinedocs/gccint/Tree-SSA-passes.html.

Skip removal
------------

Our first optimization will be a very simple form of dead-code elimination, in
which we remove instances of `Skip`.  The following helper function might be useful: you can use it to check if a given command is a `Skip`: `if is_skip c then … else …` (of course, using a regular `match` works as well!).
|*)

Fixpoint opt_unskip (c: cmd) : cmd.
Admitted.

Example opt_unskip_test1 :
  opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
  Skip.
Proof.
Admitted.

Example opt_unskip_test2 :
  opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
              while 0 loop Skip;; Skip done;; Skip) =
  (when 0 then Skip else Skip done;; while 0 loop Skip done).
Proof.
Admitted.

(*|
Now let's prove this optimization correct.  The following two lemmas and the
below are provided for your convenience.
|*)

Lemma WhileTrue_inv : forall phi v e body v'' c,
    interp_arith e v = c ->
    c <> 0 ->
    eval phi v (While e body) v'' ->
    exists v',
      eval phi v body v' /\
      eval phi v' (While e body) v''.
Proof.
  intros.
  inversion H1; eauto; subst; congruence.
Qed.

Lemma WhileFalse_inv : forall phi v e body v',
    interp_arith e v = 0 ->
    eval phi v (While e body) v' ->
    v = v'.
Proof.
  intros.
  inversion H0; auto; subst; congruence.
Qed.

Lemma opt_unskip_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_unskip c) v'.
Proof.
Admitted.

(*|
Constant propagation
--------------------

This is the first of two options.  If you implement this optimization, you do
not have to implement the next one.

At the beginning of this exercise we looked at constant folding, which uses
properties of arithmetic operations to simplify expressions.  Here, we'll look
at something slightly different: constant propagation.

Constant propagation is a form of static evaluation: it analyzes assignments to
detect cases in which the value being assigned is a constant; when it is, it
propagates it through the rest of the program.  This means that in a program
like `Assign x (Const n);; …`, we'll want to replace all instances of `x` with
`Const n` in `…`.  We'll keep a map `consts` tracking variables that have
constant values and use it to rewrite the program.

The first step is to define constant propagation for arithmetic expressions.
Since there are no assignments in expressions, this is just a matter of
substituting known values recursively:
|*)

Fixpoint opt_arith_constprop (c: expr) (consts: valuation) {struct c} : expr.
Admitted.

(*|
What is the correctness criterion for constant propagation?  The environment of
statically known values, `consts`, needs to be consistent with the dynamic
valuation.  This is what `consts $<= v` means; `$<=` is a notation for the
`includes` function.
|*)

Lemma opt_arith_constprop_sound : forall e v consts,
    consts $<= v ->
    interp_arith (opt_arith_constprop e consts) v =
    interp_arith e v.
Proof.
Admitted.

(*|
We can now define constant propagation on commands.  Propagating constants
through a program returns a new program, as well as a new set of known
constants.  Think carefully about the following cases:

- Assignments and function calls: these should update the `consts` map.  If the
  value being assigned is a constant, then it should be added to the map;
  otherwise, it should be removed from the map, using the `$-` operator.

- Conditionals: in a fully general implementation, we would want to reconcile
  the information learned along both branches of the `If`.  In this simple
  version, we will not do that: we'll simply reset the `consts` map to `$0`
  after constant-propagating through both branches.

- Loops: Constant-propagating through loops requires tracking the set of
  variables written in the loop.  Instead, we will reset the `consts` map when
  entering the body of a loop and reset it as well after exiting the loop.

In addition to propagating constants, you may be tempted to remove the
corresponding `Assign` node from the AST (replacing it with a `Skip`, for
example).  But in fact, the assignment *should be kept*: it's not safe to remove
the assignment entirely — can you see why?
|*)


(* HINT 1-2 *)
Definition opt_constprop (c: cmd) : cmd.
Admitted.
Arguments opt_constprop !_ /. (* Coq magic *)

Example opt_constprop_test1 :
  opt_constprop FactBody = FactBody.
Proof.
Admitted.

Example opt_constprop_test2 :
  opt_constprop ("x" <- 7;; "y" <- "x";;
                 when "x" mod "w" then
                   "z" <- "x";; "t" <- "z";; while "t" loop "t" <- "t" - 1 done
                 else
                   "z" <- "u" + "x";; "t" <- "z"
                 done;;
                 "r" <- "z") =
 ("x" <- 7;; "y" <- 7;;
  when 7 mod "w" then
    "z" <- 7;; "t" <- 7;; while "t" loop "t" <- "t" - 1 done
  else
    "z" <- "u" + 7;; "t" <- "z"
  done;;
  "r" <- "z").
Proof.
Admitted.


Lemma opt_constprop_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_constprop c) v'.
Proof.
Admitted.

(*|
Loop unrolling
--------------

This is the second of two options.  If you implement this optimization, you do
not have to implement the previous one.

Reasoning across loop iterations is trickier than reasoning about loop-free
code, so one common optimization in compilers is *loop unrolling*, a process
whereby a loop body is repeated multiple times.  For example, consider the
following snippet::

    for (i = 0; i < len; i++) {
       out[i] = in[i];
    }

an optimizing compiler might replace it with the following::

    for (i = 0; i + 4 <= len; i += 4) { // Unrolled loop
       out[i] = in[i];
       out[i + 1] = in[i + 1];
       out[i + 2] = in[i + 2];
       out[i + 3] = in[i + 3];
    }
    for (; i < len; i++) { // Fix-up
       out[i] = in[i];
    }

In this example, unrolling would enable the compiler to optimize the
assignments, for example by coalescing them into larger memory operations
(“vectorizing”)::

    for (i = 0; i + 4 <= len; i += 4) { // Unrolled loop
       out[i:i+4] = in[i:i+4];
    }
    for (; i < len; i++) { // Fix-up
       out[i] = in[i];
    }

Let's implement a simple form of this optimization.  Since we have `while` loops
instead of `for` loops we'll recognize a slightly different pattern::

   while (counter) loop
     …body…;;
     counter <- counter - 1
   done

And for simplicity, we'll unroll each loop twice, so we'll generate the
following code::

   when (counter mod 2) then
     …body…;;
     counter <- counter - 1
   done
   while (counter) loop
     …body…;;
     counter <- counter - 1
     …body…;;
     counter <- counter - 1
   done

First, let's write a function to make sure that a given program (`body`) does
not write to a variable.  We'll need this to make sure that the loop body
doesn't overwrite the loop variable.
|*)

(* HINT 3-4 *)
Fixpoint read_only (c: cmd) (x0: var) {struct c} : bool.
Admitted.

(*|
With this, we can define the loop-unrolling transformation, in three steps:

First, a function that checks whether a program looks exactly like the
unrollable template above; if it does, this function returns the loop variable
and the body of the loop; otherwise it returns `None`; it does not recurse:
|*)

Definition opt_unroll_match_loop (c: cmd) : option (var * cmd).
Admitted.
Arguments opt_unroll_match_loop : simpl never. (* Coq magic *)

(*|
We recommend that you define a lemma that tells you what must be true about `c`
if `opt_unroll_match_loop c = Some (x, body)` holds.
|*)


(*|
Second, we need a function to generate the unrolled pattern; you can use any
implementation you want for the fix-up phase as long as you're indeed
implementing unrolling (the fix-up phase is the phase that adjusts for the fact
that the loop variable may not be a multiple of 2 at the start of the loop).
This is just a transcription of the C code shown earlier: it takes a loop body
and the variable it iterates on, and it returns a program similar to the
unrolled loop shown above.
|*)

Definition opt_unroll_template_de (x: var) (body: cmd) : cmd.
Admitted.

(*|
Third, we can write the full optimization, which runs `opt_unroll_match_loop` at
all places in the AST and uses `opt_unroll_template_de` when it finds a relevant
place.  For simplicity, you do not have to unroll loops recursively within the
body of an unrolled loop.
|*)

Fixpoint opt_unroll (c: cmd) : cmd.
Admitted.

Example opt_unroll_test1 :
  opt_unroll CollatzBody = CollatzBody.
Proof.
Admitted.

Example opt_unroll_test2 :
  opt_unroll FactBody <> FactBody.
Proof.
Admitted.

(*|
For the proof of correctness, you'll want to prove a number of side lemmas (our
solution has 5!).  To help you get started, here are a few facts on modulo (you
can refer to them using `Mod2.…`, e.g. `Mod2.small`:
|*)

Module Mod2.
  Lemma even_not_one n: n mod 2 = 0 -> n <> 1.
  Proof. destruct n; try destruct n; simpl in *; congruence. Qed.

  Lemma small n: n mod 2 = 0 \/ n mod 2 = 1.
  Proof. pose proof Nat.mod_upper_bound n 2; lia. Qed.

  Lemma pm n: n <> 0 -> (n - 1) mod 2 = (n + 1) mod 2.
  Proof.
    erewrite <- Nat.Div0.mod_add with (b := 1); try congruence.
    intros. f_equal. lia.
  Qed.

  Lemma even_pred_odd n: n <> 0 -> n mod 2 = 0 -> (n - 1) mod 2 = 1.
  Proof.
    intros. rewrite pm by assumption.
    rewrite Nat.Div0.add_mod by lia.
    replace (n mod 2); reflexivity.
  Qed.

  Lemma odd_pred_even n: n mod 2 = 1 -> (n - 1) mod 2 = 0.
  Proof.
    intros. rewrite pm.
    { destruct n.
      - simpl in *; try congruence.
      - rewrite Nat.Div0.add_mod by lia.
        rewrite H. reflexivity. }
    destruct n; simpl in *; congruence.
  Qed.
End Mod2.

(*|
Good luck with the correctness proof!  Remember to check the hints in the signature file or come to office hours if you run into issues.  To get you started, here is a lemma that lets you use `read_only _ _ _` hypotheses:
|*)

Lemma eval_read_only: forall {phi v v' x c},
    eval phi v c v' ->
    read_only c x = true ->
    v' $? x = v $? x.
Proof.
Admitted.

Lemma opt_unroll_sound phi : forall c v v',
    eval phi v c v' ->
    eval phi v (opt_unroll c) v'.
Proof.
Admitted.

(*|
Going further
=============

The following are suggestions, if you are interested in exploring further.
Beware that proving correctness for the optimizations below can be quite
time-consuming!

Tail-call elimination
---------------------

Tail-call elimination transforms recursive functions into loops, which saves
stack space and time pushing and popping items on the stack.  You can read more
about tail-call elimination at https://en.wikipedia.org/wiki/Tail_call .

The first step is to check that all calls to a given function are tail calls:
|*)

Axiom may_tco: forall (is_tail: bool) (f: string) (c: cmd), bool.

(*|
Then, we can perform tail-call elimination, under the assumption that calls to
`f` are in fact tail calls:
|*)

Axiom opt_tco : forall (f: string) (x1 x2: var) (c: cmd), cmd.

(*|
The correctness lemma looks roughly like this:
|*)

Axiom opt_tco_sound : forall phi c f x1 x2,
    may_tco true f c = true ->
    forall v v',
      eval phi v c v' ->
      eval phi v (opt_tco f x1 x2 c) (v' $+ ("continue", 0)).

(*|
Function Inlining
-----------------

Inlining reveals optimization opportunities by allowing the compiler to
specialize a function's body to a given call site.

When inlining, the compiler needs to be particularly careful not to overwrite
the caller's variables, nor not to give the inlined function body access to the
caller's variables.
|*)

Axiom opt_inline : forall (phi: environment) (c: cmd), cmd.

(*|
Note that inlining a function will add the (renamed) locals of the function to
the current valuation, so the correctness theorem has to be a bit different:
|*)

Axiom opt_inline_sound : forall phi c v v',
    eval phi v c v' ->
    exists v'',
      eval phi v (opt_inline phi c) v'' /\
      (v' $<= v'').

(* Authors:
   Clément Pit-Claudel
   Alexandre Pinazza
   Yawen Guan
   Nate Foster
 *)
