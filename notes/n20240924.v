(*|
================================
Lecture 9: Fuel and Type Classes
================================
|*)

Require Import List.

(* Useful tactics for simplifying equalities *)
Ltac simpeq := repeat match goal with
  | _ => congruence || (progress subst)
  | H : ?x = ?x |- _ => clear H
  | H : _ = _ |- _ => progress injection H as H
  end.

Ltac inv H := inversion H; clear H; simpeq.

Fixpoint merge_fuel (fuel : nat) (xs ys : list nat) : list nat :=
  match fuel with
  | 0 => nil
  | S fuel' =>
    match xs,ys with
    | nil,ys => ys
    | xs,nil => xs
    | x::xs,y::ys =>
        if Nat.leb x y then
          x::merge_fuel fuel' xs (y::ys)
        else
          y::merge_fuel fuel' (x::xs) ys
    end
  end.

Compute (merge_fuel 4 (1::2::nil) (2::4::nil)).

Definition merge xs ys := merge_fuel (length xs + length ys) xs ys.

Compute (merge (1::3::nil) (2::4::nil)).

Inductive R : (list nat * list nat) -> (list nat * list nat) -> Prop :=
  | R_left x xs ys : R (xs, ys) (x::xs,  ys)
  | R_right y xs ys : R (xs, ys) (xs, y::ys).

Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop :=
  | Acc_intro : (forall y, R y x -> Acc R y) -> Acc R x.

Lemma all_acc (xs ys : list nat) : Acc R (xs, ys).
Proof.
  revert ys.
  induction xs; intros.
  - induction ys.
    + constructor. intros. inv H.
    + constructor. intros. inv H.
  - induction ys.
    + constructor. intros. inv H. auto.
    + constructor. intros. inv H. auto.
Defined.

Compute (all_acc (1::3::nil) (2::4::nil)).

Require Import Coq.Program.Wf.

(* Otherwise coq can't see whether what's inside a is the same as the passed in xs and ys *)
Program Fixpoint merge_acc (xs ys : list nat) (a : Acc R (xs, ys)) :=
  match a with
  | Acc_intro _ _ f =>
    match xs,ys with
    | nil,ys => ys
    | xs,nil => xs
    | x::xs,y::ys =>
        if Nat.leb x y then
          x::merge_acc xs (y::ys) (f (xs, y::ys) (R_left x xs (y::ys)))
        else
          y::merge_acc (x::xs) ys (f (x::xs, ys) (R_right y (x::xs) ys))
    end
  end.
(* Obligations solve that some things are equal *)
(* Print merge_acc. *)

Definition merge' xs ys := merge_acc xs ys (all_acc xs ys).

(* Need all_acc to be "Defined" for use in other definitions. *)
Compute (merge' (1::3::nil) (2::4::nil)).


(*|
Fuel
----
|*)

(* Fixpoint merge_fuel (fuel:nat) (xs ys : list nat) : list nat := *)
(*   match fuel with *)
(*   | 0 => nil *)
(*   | S fuel' => *)
(*     match xs,ys with *)
(*     | nil,_ => ys *)
(*     | _,nil => xs *)
(*     | x::xs, y::ys => *)
(*         if Nat.leb x y then *)
(*           x::merge_fuel fuel' xs (y::ys) *)
(*         else *)
(*           y::merge_fuel fuel' (x::xs) ys *)
(*     end *)
(*   end. *)

Compute merge_fuel 100 (1::3::nil) (2::4::nil).

Compute merge_fuel 4 (1::3::nil) (2::4::nil).
Compute merge_fuel 3 (1::3::nil) (2::4::nil).
Compute merge_fuel 2 (1::3::nil) (2::4::nil).
Compute merge_fuel 1 (1::3::nil) (2::4::nil).
Compute merge_fuel 0 (1::3::nil) (2::4::nil).

Definition merge1 xs ys := merge_fuel (length xs + length ys) xs ys.

Compute merge1 (1::3::nil) (2::4::nil).

(*|
Accesibility
------------

Last time, we saw that we could define a measure for the size of a list, and use it to prove the termination of a function.
We will now see how to do this manually by structural recursion on the accessibility predicate.
|*)

Require Import Coq.Program.Wf.

(*|
Our well-founded relation.

Read `R x y` as "x is strictly smaller than y".
|*)
(* Inductive R : (list nat * list nat) -> (list nat * list nat) -> Prop := *)
(*   | R_left x xs ys : R (xs,ys) (x::xs, ys) *)
(*   | R_right y xs ys : R (xs,ys) (xs, y::ys). *)

(*|
An element is accessible if all strictly smaller elements are accessible.
|*)
(* Inductive Acc {A : Type} (R : A -> A -> Prop) (x : A) : Prop := *)
(*   | Acc_intro : (forall y, R y x -> Acc R y) -> Acc R x. *)

(* Program Fixpoint merge_acc (xs ys : list nat) (a : Acc R (xs,ys)) *)
(*   : list nat := *)
(*   match a with *)
(*   | Acc_intro _ _ f => *)
(*     match xs,ys with *)
(*     | nil,_ => ys *)
(*     | _,nil => xs *)
(*     | x::xs, y::ys => *) 
(*         if Nat.leb x y then *)
(*           x::merge_acc xs (y::ys) (f (xs,y::ys) (R_left x xs (y::ys))) *)
(*         else *)
(*           y::merge_acc (x::xs) ys (f (x::xs,ys) (R_right y (x::xs) ys)) *)
(*     end *)
(*   end. *)
(* Fail Next Obligation. *)

(*|
We prove that all pairs of lists are accessible.
|*)

(* Lemma all_acc (xs ys : list nat) : Acc R (xs,ys). *)
(* Proof. *)
(*   revert ys. *)
(*   induction xs; intros. *)
(*   - induction ys. *)
(*     + constructor. intros. inv H. *)
(*     + constructor. intros. inv H. *)
(*   - induction ys. *)
(*     + constructor. intros. inv H. eauto. *)
(*     + constructor. intros. inv H. eauto. *)
(* Defined. *)

Definition merge2 xs ys := merge_acc xs ys (all_acc xs ys).

Compute merge2 (1::3::nil) (2::4::nil).

(*|
Type Classes
------------

A type class defines an interface for some type. For instance, let us say that
types `A` that implement the `Show` interface have a method named `show` that
will convert them to a `string.`
|*)

Require Import String.
Open Scope string_scope.
Require Import List.
Open Scope list_scope.

Require Import Arith.

Class Show (A:Type) := {
  show : A -> string
}.

(*|
Here is an instance for booleans.
|*)
Instance boolShow : Show bool := {
    show := fun (b:bool) => if b then "true" else "false"
  }.

Compute show true. (* .unfold *)
Compute show false. (* .unfold *)

(*|
Note that we cannot yet use this for natural numbers:
|*)
Compute (_: Show nat). (* .unfold *)
Eval compute in show 3. (* .unfold *)

(*|
To define a `Show` instance for natural numbers, let's first define a helper that shows a single digit.
|*)
Definition digit2string(d:nat) : string :=
  match d with
  | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
  | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
  | 8 => "8" | _ => "9"
  end.

(*|
Alas, it can be difficult to convince Coq that the iterated version of this helper function terminates.  So, we can simply give it fuel.
|*)
Fixpoint digits' (fuel n:nat) (accum : string) : string :=
  match fuel with
  | 0 => accum
  | S fuel' =>
      match n with
      | 0 => accum
      | _ => let d := digit2string(n mod 10) in
             digits' fuel' (n / 10) (d ++ accum)
      end
  end.

(*|
Fortunately, it's sufficient to use `n` as the fuel for itself, since we know we won't need to divide `n` by `10` more than `n` times.  We could of course use the `log` of `n` (base `10`) instead, but there's no benefit to being this precise, so we'll just use `n`.
|*)
Definition digits (n:nat) : string :=
  match digits' n n "" with
  | "" => "0"
  | ds => ds
  end.

(*|
Now we can define the `Show` instance for `nat`.
|*)

Instance natShow : Show nat := {
  show := digits
}.

Compute show 42. (* .unfold *)
Compute show (10+2). (* .unfold *)

(*|
Importantly, we still have the ability to show booleans.
|*)
Compute show true.

(*|
We can also parameterized instances, allowing us to show data structures.

The following is a generic instance in that if we can have two types
A and B that are instances of the Show class, then we can
build a generic Show for the product type (A*B).
|*)
Instance pairShow (A B:Type)
  (showA : Show A) (showB : Show B)
  : Show (A*B) :=
{
  show := (fun p => "(" ++
                      (show (fst p)) ++
                      "," ++
                      (show (snd p)) ++
                      ")")
            %string
}.

Compute show (3,4).
Compute show (true,42).

Print pairShow.

(*|
Similarly, we can define a generic show for lists, as long as the elements of the
lists are [show]able.
|*)
Definition show_list{A:Type}{showA:Show A}(xs:list A) : string := 
  ("[" ++ ((fix loop (xs:list A) : string := 
             match xs with 
               | nil => "]"
               | h::nil => show h ++ "]"
               | h::t => show h ++ "," ++ loop t
             end) xs))%string.

Instance listShow(A:Type)(showA:Show A) : Show (list A) := {
  (* What does the @ sign do *)
  show := @show_list A showA
}.

Compute show (1::2::3::nil).          
Compute show (true::false::nil).
Compute show ((1,true)::(42,false)::nil).
Compute show ((1::2::3::nil)::(4::5::nil)::(6::nil)::nil).

(*|
Here is another way to have an anonymous argument, other than using the name [_].
|*)
(* {_ : Show A} is the same as `{Show A} *)
Definition showOne {A:Type} `{Show A} (a:A) : string :=
  "The value is " ++ show a.

Compute showOne true.
Compute showOne 7.

Definition showTwo {A B:Type} `{Show A} `{Show B}
  (a:A) (b:B) : string :=
  "First is " ++ show a ++ " and second is " ++ show b.

Compute (showTwo true 7).
Print showOne.
Print showTwo.

(*|
Type classes are a powerful abstraction tool that fit very well
with some proof developments.

One tip is to make type classes as small and simple as possible. For
example, you probably want to separate out the operations you want to
use from the properties that the implementation is expected to
satisfy.
|*)

(*|
Monoids
-------
We already saw monoids when we discussed Coq's module system. Let's see how to
model monoids using type classes instead.
|*)
Class Monoid (M:Type) := {
    munit : M;
    mplus : M -> M -> M;                                  
  }.

(*|
We can define various instances of a monoid, such as strings, integers, and lists.
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
How might we use a monoid? We can define a generic loging for an interpreter 
|*)

Definition env := string -> nat.

Inductive expr : Type :=
  | Const : nat -> expr
  | Var : string -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr
  | Minus : expr -> expr -> expr.

Fixpoint eval {A:Type} {m:Monoid A} (f:expr -> A) (log:A)
  (env : env) (e : expr) : (A * nat) :=
  match e with
  | Const n =>
      (mplus (f e) log, n)
  | Var x =>
      (mplus (f e) log, env x)
  | Plus e1 e2 =>
      let (l1,n1) := eval f log env e1 in
      let (l2,n2) := eval f log env e2 in
      (mplus (mplus log (mplus l1 l2)) (f e), n1 + n2)
  | Mult e1 e2 =>
      let (l1,n1) := eval f log env e1 in
      let (l2,n2) := eval f log env e2 in
      (mplus (mplus log (mplus l1 l2)) (f e), n1 * n2)
  | Minus e1 e2 =>
      let (l1,n1) := eval f log env e1 in
      let (l2,n2) := eval f log env e2 in
      (mplus (mplus log (mplus l1 l2)) (f e), n1 - n2)
  end.

Definition e := Plus (Const 7) (Mult (Const 3) (Const 4)).
Definition init := fun (_:string) => 0.
Definition count (e:expr) := 1.
Definition debug (e:expr) :=
  match e with
  | Const _ => "const,"
  | Var _ => "var,"
  | Plus _ _ => "plus,"
  | Mult _ _ => "mult,"
  | Minus _ _ => "minus,"
  end.

Compute (eval count 0 init e).
Compute (eval debug "" init e).

(*|
We can also define a monoid from a pair of monoids.
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

Compute (eval (fun e => (count e, debug e)) (0,"") init e).

(*|
Monads
------
Monads are very useful for modeling things that are not just pure
functions, that have some kind of external effect on the world such as
reading input or producing output. They're essential for modeling
statefulness a in pure, stateless, functional language like Coq.

Now we define a generic class for Monads.  Here, it's not a type
that's a monad, but rather a type constructor (i.e., a function from
types to types, aka a functor.  Monads have two operations: [ret] and
[bind].

If we think of monads as a pattern for encoding effects, such as
exceptions or state or non-determinism, then we can think of "M A" as
describing side-effecting computations that produce a value of type A.

The [ret] operation takes a pure (effect-free) value of type A and
injects it into the space of side-effecting computations.

The [bind] operation sequences two side-effecting computations,
allowing the latter to depend upon the value of the first one.
|*)

Class Monad(M:Type -> Type) := {
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

(*|
We will define the usual, more convenient, notation for [bind].
|*)
Notation "x <- c1 ;; c2" :=
  (bind c1 (fun x => c2)) 
    (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" :=
  (bind c1 (fun _ => c2)) (at level 100, right associativity).

(*|
One instance of the generic [Monad] class is the [option] monad defined as
follows. It's a bit like exceptions where there is only one possible
exception: [None].
|*)
Instance OptionMonad : Monad option := {
  ret := fun {A:Type} (x:A) => Some x ; 
  bind := fun {A B:Type} (x:option A) (f:A -> option B) =>
            match x with 
              | None => None
              | Some y => f y
            end
}.

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

Example e1 : expr := Plus(Const 2) (Minus(Const 0) (Const 1)).
Compute (eval' init e1).

(*|
That's better than normal evaluation:
|*)
Compute 2 + (0 - 1).

Require Import String.

(*|
Going a step further, we can define an exception monad.
|*)

Inductive Exn(A:Type) : Type := 
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
  tryCatch (eval'' init e) "underflow" (ret 0).

Check eval_to_zero.
Compute eval'' init (Minus (Const 2) (Const 5)).
Compute eval_to_zero (Minus (Const 2) (Const 5)).

(*|
We can also use monads to model state.
|*)

(*|
We define a simple language of "expressions" with imperative update
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
it's tedious and error-prone:
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
