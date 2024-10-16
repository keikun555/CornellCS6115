From Coq Require Export Arith.
From Coq Require Export Program.Equality.
Require Export Map Lang.
Require Export String.

(*|
This exercise set is a chose-your-own-adventure assignment,
so you can pick what to do.  Here is the complete rubric,
which choice indicated by `==`::

    Axiom opt_binop_fold_test1
    Axiom opt_binop_fold_sound
    Axiom eval_deterministic
    = Arith
      == Precompute
         Axiom opt_binop_precompute_sound
         Axiom opt_arith_precompute_test1
         Axiom opt_arith_precompute_test2
      == Log
         Axiom opt_binop_log2_sound
         Axiom opt_arith_log2_test1
         Axiom opt_arith_log2_test2
      == Bitwise
         Axiom opt_binop_bitwise_sound
         Axiom opt_arith_bitwise_test1
         Axiom opt_arith_bitwise_test2
    Axiom opt_arith_fold_test1
    Axiom opt_arith_sound
    Axiom opt_unskip_test1
    Axiom opt_unskip_test2
    Axiom opt_unskip_sound
    = Eval
      == ConstProp
         Axiom opt_arith_constprop_sound
         Axiom opt_constprop_test1
         Axiom opt_constprop_test2
         Axiom opt_constprop_sound
      == Unroll
         Parameter eval_read_only
         Axiom opt_unroll_test1
         Axiom opt_unroll_test2
         Axiom opt_unroll_sound
|*)

Module Type S.

  (*|
  IMPORTANT: The language we use in this exersice set is defined in [Lang.v].
  Please read [Lang.v] before you start working on the exercise.
  |*)

  Axiom eval_deterministic : forall phi c v0 v1 v2,
      eval phi v0 c v1 ->
      eval phi v0 c v2 ->
      v1 = v2.  
  
  Definition eval_returns phi v cmd outVar result :=
    exists v', eval phi v cmd v' /\ v' $? outVar = Some result.

  Axiom TwoPlusTwoIsFour :
    eval_returns $0 $0 ("out" <- 2 + 2) "out" 4.
  Axiom EvalVars :
    eval_returns $0 $0 ("x" <- 1 + 1;; "x" <- "x" + "x" + "y") "x" 4.
  Axiom EvalSimpleArith :
    eval_returns $0 $0 ("out" <- (((14 >> 1) + 8 / 4 / 2) * (7 - 2) << 1) + 2 == 82) "out" 1.
  Axiom EvalTimes3Plus1 : forall n : nat,
      eval_returns $0 ($0 $+ ("n", n)) Times3Plus1Body "n" (3 * n + 1).
  Axiom EvalFact6 : exists v : valuation,
      eval $0 ($0 $+ ("n", 3)) FactBody v /\ v $? "f" = Some 6.
  Axiom EvalFactRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3)) FactRecBody v /\ v $? "f" = Some 6.
  Axiom EvalFactTailRec6 : exists v : valuation,
      eval Fact_env ($0 $+ ("n", 3) $+ ("acc", 1)) FactTailRecBody v /\
      v $? "f" = Some 6.
  Axiom collatz_result : exists v : valuation,
      eval Collatz_env ($0 $+ ("flight", 0) $+ ("start", 10)) CollatzBody v /\
      v $? "flight" = Some 6.

  Parameter opt_binop_fold : BinopName -> expr -> expr -> expr.
  Axiom opt_binop_fold_test1 : opt_binop_fold Plus "x" 0 = "x".

  Axiom opt_binop_fold_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_fold b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_precompute : BinopName -> expr -> expr -> expr.
  Axiom opt_binop_precompute_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_precompute b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_log2 : BinopName -> expr -> expr -> expr.
  Axiom opt_binop_log2_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_log2 b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_binop_bitwise : BinopName -> expr -> expr -> expr.
  Axiom opt_binop_bitwise_sound :
    forall (b : BinopName) (e1 e2 : expr) (v : valuation),
      interp_arith (opt_binop_bitwise b e1 e2) v =
      interp_binop b (interp_arith e1 v) (interp_arith e2 v).

  Parameter opt_arith : expr -> expr.

  Axiom opt_arith_fold_test1 :
    opt_arith (1 + "z" * ("y" * ("x" * (0 + 0 / 1))))%expr =
    (1)%expr.
  Axiom opt_arith_precompute_test1:
    opt_arith (("x" + (3 - 3)) / (0 + 1) + ("y" + "y" * 0))%expr =
    ("x" + "y")%expr.
  Axiom opt_arith_precompute_test2 :
    opt_arith ((("y" / ("x" * 0 + 7 / 1)) mod (12 - 5)) / (2 * 3))%expr =
    (("y" / 7) mod 7 / 6)%expr.
  Axiom opt_arith_log2_test1 :
    opt_arith (("y" * 8) mod 8 / 4)%expr =
    (("y" << 3 & 7) >> 2)%expr.
  Axiom opt_arith_log2_test2 :
    opt_arith (("y" * 1 + (4 + 0)) mod 9 / 3)%expr =
    (("y" + 4) mod 9 / 3)%expr.
  Axiom opt_arith_bitwise_test1 :
    opt_arith ("y" * 13)%expr =
    ("y" + (("y" << 2) + ("y" << 3)))%expr.
  Axiom opt_arith_bitwise_test2 :
    opt_arith ("y" * (3 + 0))%expr =
    ("y" + ("y" << 1))%expr.

  Axiom opt_arith_sound :
    forall (e : expr) (v : valuation),
      interp_arith (opt_arith e) v = interp_arith e v.

  Parameter opt_unskip : cmd -> cmd.

  Axiom opt_unskip_test1 :
    opt_unskip (Skip;; (Skip;; Skip);; (Skip;; Skip;; Skip)) =
    Skip.
  Axiom opt_unskip_test2 :
    opt_unskip (when 0 then (Skip;; Skip) else Skip done;;
                while 0 loop Skip;; Skip done;; Skip) =
    (when 0 then Skip else Skip done;; while 0 loop Skip done).

  Axiom opt_unskip_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unskip c) v'.

  Parameter opt_arith_constprop : expr -> valuation -> expr.

  Axiom opt_arith_constprop_sound :
    forall (e : expr) (v consts : fmap var nat),
      consts $<= v ->
      interp_arith (opt_arith_constprop e consts) v = interp_arith e v.

  Parameter opt_constprop : cmd -> cmd.

  Axiom opt_constprop_test1 :
    opt_constprop FactBody = FactBody.
  Axiom opt_constprop_test2 :
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

  Axiom opt_constprop_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_constprop c) v'.

  Parameter read_only : forall (c: cmd) (x0: var), bool.

  Parameter eval_read_only: forall {phi v v' x c},
      eval phi v c v' ->
      read_only c x = true ->
      v' $? x = v $? x.

  Parameter opt_unroll : cmd -> cmd.

  Axiom opt_unroll_test1 :
    opt_unroll CollatzBody = CollatzBody.
  Axiom opt_unroll_test2 :
    opt_unroll FactBody <> FactBody.

  Axiom opt_unroll_sound :
    forall (phi : environment) (c : cmd) (v v' : valuation),
      eval phi v c v' -> eval phi v (opt_unroll c) v'.
End S.

Global Arguments Nat.modulo !_ !_ /.
Global Arguments Nat.div !_ !_.
Global Arguments Nat.log2 !_ /.

