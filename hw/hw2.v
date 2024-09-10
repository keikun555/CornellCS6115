(** Homework 2: Higher-Order Functions and Containers *)

Require Import ZArith List Lia.
Import ListNotations.

(** In this exercise set, we will practice two working with:
    1) Higher-order functions (HOFs), i.e. functions that take other functions
    as arguments.
    2) Polymorphic container types, i.e. types parametrized by types,
    such as [option A], [list A], [tree A], and finally, [bitwise_trie A],
    which combines option and tree to obtain a new useful data structure.
 *)

(** ** Higher-order functions **)

(** Coq's built-in notion of equality is purely syntactic, which means that
    [f = fun n : Nat => n] and [g = fun n : Nat => 0 + n] are not considered
    equal even though we can prove that [forall n, f n = g n].
    Hence, for the following exercises we will use the following equivalence
    relation between functions.
 *)

Definition fun_equiv {A B : Type} (f g : A -> B) : Prop := forall x : A, f x = g x.

Infix "~=" := fun_equiv (at level 70, no associativity).

(** To warm up, let's first prove that [fun_equiv] is an equivalence relation *)
Lemma fun_equiv_refl : forall (A B : Type) (f : A -> B), f ~= f.
Proof.
  intros.
  unfold fun_equiv.
  intros.
  reflexivity.
Qed.

Lemma fun_equiv_symm : forall (A B : Type) (f g : A -> B),
    f ~= g -> g ~= f.
Proof.
  intros.
  unfold fun_equiv.
  unfold fun_equiv in H.
  intros.
  specialize (H x).
  rewrite H.
  reflexivity.
Qed.

Lemma fun_equiv_trans : forall (A B : Type) (f g h : A -> B),
    f ~= h -> h ~= g -> f ~= g.
Proof. 
  intros.
  unfold fun_equiv.
  unfold fun_equiv in H.
  unfold fun_equiv in H0.
  intros.
  specialize (H x).
  rewrite H.
  specialize (H0 x).
  rewrite H0.
  reflexivity.
Qed.

(** Here is the definition of the identity function [id], which just returns
    its argument without modification: *)
Definition id {A : Type} (x : A) : A := x.

(** We can define [compose], a higher-order function: [compose g f]
    which applies [f] to its input and then applies [g]. Argument order
    follows the general convention of functional composition in
    mathematics denoted by the small circle. *)
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C :=
  g (f x).

(** Let's use a small circle to refer to [compose]. This will make our
    goals much more readable. It's up to you to decide whether you also
    want to use the circle notation in your definitions or whether you
    prefer to write [compose].
    
    Users of Emacs with company-coq can simply type \circ RET
    to insert ∘. *)
Notation " g \circ f " := (compose g f) (at level 40, left associativity).
Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

(** Here are three simple properties of function composition.
    Together, these properties mean that functions with ∘ form
    a monoid. *)

Lemma compose_id_l : forall A B (f: A -> B),
    id ∘ f ~= f.
Proof.
  intros.
  unfold fun_equiv.
  intros.
  unfold id.
  unfold compose.
  reflexivity.
Qed.

Lemma compose_id_r : forall A B (f: A -> B),
    f ∘ id ~= f.
Proof.
  intros.
  unfold fun_equiv.
  intros.
  unfold compose.
  unfold id.
  reflexivity.
Qed.

Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
    h ∘ (g ∘ f) ~= h ∘ g ∘ f.
Proof.
  intros.
  unfold fun_equiv.
  intros.
  unfold compose.
  reflexivity.
Qed.

(** The selfCompose function takes a function and applies this function [n] times
    to the argument. There are different ways of defining it, but let's
    define it using only [id] and [compose]. *)
Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
  match n with
  | O => id
  | S n' => f ∘ (selfCompose f n')
  end.

(** Here's an example of what [selfCompose] can do:
    If we apply the function that adds 2 to its argument 7 times to the starting
    value 3, we obtain 3 + 7 * 2 = 17. *)
Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17.
Proof. reflexivity. Qed.

(** We can also use [selfCompose] to define exponentiation on natural numbers, by
    saying "to raise [base] to the power [e], apply the function that multiplies
    its argument by [base] to [1] [e] times".
    Define [exp] using [selfCompose] and [Nat.mul]. *)
Definition exp(base e: nat): nat := selfCompose (Nat.mul base) e 1.

(** Once you define [exp], you can replace [Admitted.] below by [Proof. reflexivity. Qed.] *)
Lemma test_exp_2_3: exp 2 3 = 8. Proof. reflexivity. Qed.
Lemma test_exp_3_2: exp 3 2 = 9. Proof. reflexivity. Qed.
Lemma test_exp_4_1: exp 4 1 = 4. Proof. reflexivity. Qed.
Lemma test_exp_5_0: exp 5 0 = 1. Proof. reflexivity. Qed.
Lemma test_exp_1_3: exp 1 3 = 1. Proof. reflexivity. Qed.

(** And here's another example to illustrate [selfCompose]. Make sure you understand
    why its result is 256. *)
Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256.
Proof. reflexivity. Qed.

(** ** Inverse functions **)

(** Using [compose] and [id], we can write a concise definition of when
    a function [g] is the left inverse of a function [f]: *)
Definition left_inverse {A B : Type} (f : A -> B) (g : B -> A) : Prop :=
  g ∘ f ~= id.

(** Here's an example: The function that subtracts two from its argument
    is the left inverse of the function that adds two to its argument. *)
Example plus2minus2:
  left_inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
Proof.
  intros.
  unfold left_inverse.
  unfold fun_equiv.
  intros.
  unfold compose.
  unfold id.
  lia.
Qed.

(** On the other hand, note that the other direction does not hold, because
    if a subtraction on natural numbers underflows, it just returns 0, so
    there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
    so it can't have a left inverse. *)
Example minus2plus2: ~ left_inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
Proof.
  intros.
  unfold left_inverse.
  unfold fun_equiv.
  unfold compose.
  unfold id.
  intros H.
  specialize (H 0).
  lia.
Qed.

(** Let us make the intuition from the previous paragraph more
    concrete, by proving that a function that is not injective
    cannot have a left inverse; or, in other words, that
    functions with left inverses are injective. *)

Lemma left_invertible_injective {A}:
  forall (f g: A -> A),
    left_inverse f g ->
    (forall x y, f x = f y -> x = y).
Proof.
  intros.
  unfold left_inverse in H.
  unfold fun_equiv in H.
  unfold compose in H.
  unfold id in H.
  assert (G := H).
  specialize (H x).
  specialize (G y).
  rewrite H0 in H.
  rewrite H in G.
  apply G.
Qed.

(** Bonus question: can you prove the reverse;
    i.e., can you prove that all injective functions have left
    inverses? *)

(** The identity function is the inverse of itself.
    Note: we're using "@" in front of "id" to say "we want to provide all implicit
    type arguments explicitly, because otherwise Coq would not be able to infer them." *)
Lemma left_inverse_id: forall A, left_inverse (@id A) (@id A).
Proof.
  intros.
  unfold id.
  unfold left_inverse.
  unfold compose.
  unfold id.
  unfold fun_equiv.
  intros.
  reflexivity.
Qed.

Lemma selfComposeAssoc{A: Type}: forall (f: A -> A) (n: nat),
  f \circ selfCompose f n ~= selfCompose f n \circ f.
Proof.
  intros.
  unfold fun_equiv.
  unfold compose.
  intros.
  induction n.
  - simpl.
    unfold id.
    reflexivity.
  - simpl.
    unfold compose.
    rewrite IHn.
    reflexivity.
Qed.
Print selfComposeAssoc.

Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
    left_inverse f g ->
    left_inverse (selfCompose f n) (selfCompose g n).
Proof.
  intros.
  unfold left_inverse.
  unfold id.
  unfold fun_equiv.
  unfold compose.
  induction n.
  - intros.
    simpl.
    unfold id.
    reflexivity.
  - intros.
    simpl.
    assert ((f \circ selfCompose f n) ~= (selfCompose f n)\circ f) as G.
    + apply selfComposeAssoc.
    + unfold fun_equiv in G.
      specialize (G x).
      rewrite G.
      unfold compose.
      specialize (IHn (f x)).
      rewrite IHn.
      unfold left_inverse in H.
      unfold compose in H.
      unfold id in H.
      apply H.
Qed.

(** ** Polymorphic container types *)

(** Let's start by lists as presented in class.
    
    [fold] is a higher-order function that is even more general
    than [map]. In essence, [fold f z] takes as input a list
    and produces a term where the [cons] constructor is
    replaced by [f] and the [nil] constructor is replaced
    by [z].
    
    [fold] is a "right" fold, which associates the binary operation
    the opposite way as the [fold_left] function from Coq's
    standard library. *)
Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
  (xs : list A) : B :=
  match xs with
  | nil => b_nil
  | cons x xs' => b_cons x (fold b_cons b_nil xs')
  end.

Example fold_example : fold plus 10 [1; 2; 3] = 16.
Proof.
  simpl.
  reflexivity.
Qed.

(** Prove that [map] can actually be defined as a particular
      sort of [fold]. *)
Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
    map f xs = fold (fun x ys => cons (f x) ys) nil xs.
Proof.
Admitted.

(** Since [fold f z] replaces [cons] with [f] and [nil] with
      [z], [fold cons nil] should be the identity function. *)
Theorem fold_id : forall {A : Type} (xs : list A),
    fold cons nil xs = xs.
Proof.
Admitted.

(** If we apply [fold] to the concatenation of two lists,
      it is the same as folding the "right" list and using
      that as the starting point for folding the "left" list. *)
Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                        (xs ys : list A),
    fold f z (xs ++ ys) = fold f (fold f z ys) xs.
Proof.
Admitted.

(** Using [fold], define a function that computes the
      sum of a list of natural numbers. *)
Definition sum : list nat -> nat. Admitted.

Example sum_example : sum [1; 2; 3] = 6.
Proof.
Admitted.

(** Using [fold], define a function that computes the
      conjunction of a list of Booleans (where the 0-ary
      conjunction is defined as [true]). *)
Definition all : list bool -> bool. Admitted.

Example all_example : all [true; false; true] = false.
Proof.
Admitted.


(** The following two theorems, [sum_append] and [all_append],
      say that the sum of the concatenation of two lists
      is the same as summing each of the lists first and then
      adding the result. *)
Theorem sum_append : forall (xs ys : list nat),
    sum (xs ++ ys) = sum xs + sum ys.
Proof.
Admitted.


Theorem all_append : forall (xs ys : list bool),
    all (xs ++ ys) = andb (all xs) (all ys).
Proof.
Admitted.

(** Using [fold], define a function that composes a list of functions,
      applying the *last* function in the list *first*. *)
Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.

Example compose_list_example :
  compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
Proof.
Admitted.

(** Show that [sum xs] is the same as converting each number
      in the list [xs] to a function that adds that number,
      composing all of those functions together, and finally
      applying that large composed function to [0].

      Note that function [plus], when applied to just one number as an
      argument, returns a function over another number, which
      adds the original argument to it! *)
Theorem compose_list_map_add_sum : forall (xs : list nat),
    compose_list (map plus xs) 0 = sum xs.
Proof.
Admitted.

(** In the next few exercices, we will work with binary trees. *)

Inductive tree {A} :=
| Leaf
| Node (l : tree) (d : A) (r : tree).
Arguments tree : clear implicits.

Fixpoint flatten {A} (t : tree A) : list A :=
  match t with
  | Leaf => []
  | Node l d r => flatten l ++ d :: flatten r
  end.

(** Define an operation to "mirror" that takes a tree and returns the
    mirrored version of the tree.

    The [mirror] definition should satisfy two properties: one is
    [mirror_mirror_id], which says that if you mirror a tree twice, it
    results in the original tree. The other is [flatten_mirror_rev] which
    states that flattening a mirrored tree is equivalent to reversing the
    list resulting from the flattening of that same tree.
 *)

Fixpoint mirror {A} (t : tree A) : tree A. Admitted.

Example mirror_test1 :
  mirror (Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))) =
    Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf.
Admitted.

Theorem mirror_mirror_id {A} : forall (t : tree A),
    mirror (mirror t) = t.
Proof.
Admitted.

Theorem flatten_mirror_rev {A} : forall (t : tree A),
    flatten (mirror t) = rev (flatten t).
Proof.
Admitted.

(** Bitwise tries are finite maps keyed by lists of Booleans.
      We will implement a bitwise trie with entries of type [A]
      by [tree (option A)]. The value at the root of the tree
      corresponds to the entry for the key [nil : list bool],
      the left subtree contains entries for those keys that
      begin with [true], and the right subtree contains entries
      for those keys that begin with [false].

      Tries are a common and powerful data structure; you can read
      more about them at https://en.wikipedia.org/wiki/Trie . *)
Definition bitwise_trie A := tree (option A).

(** Define [lookup] such that [lookup k t] looks up the
      map entry corresponding to the key [k : list bool] in the
      bitwise trie [t : bitwise_trie A].

      Look at the examples below to get a better sense of what
      this operation does: the argument [k] is a path, in which
      [true] means "go left" and [false] means "go right". *)
Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A. Admitted.

Example lookup_example1 :
  lookup [] (Node Leaf (None : option nat) Leaf) = None.
Proof.
Admitted.

Example lookup_example2 :
  lookup [false; true]
    (Node
       (Node Leaf (Some 2) Leaf)
       None
       (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
  = Some 1.
Proof.
Admitted.

(** [Leaf] represents an empty bitwise trie, so a lookup for
      any key should return [None]. *)
Theorem lookup_empty {A} : forall (k : list bool),
    lookup k (Leaf : bitwise_trie A) = None.
Proof.
Admitted.

(** Define an operation to "insert" a key and optional value
      into a bitwise trie. The [insert] definition should satisfy two
      properties: one is [lookup_insert] below, which says that if we
      look up a key [k] in a trie where [(k, v)] has just been inserted,
      the result should be [v]. The other is that lookups on keys different
      from the one just inserted should be the same as on the original map.

      If an entry for that key already exists, [insert] should replace
      that entry with the new one being inserted. Note that [insert] can
      be used to remove an entry from the trie, too, by inserting [None]
      as the value. *)
Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
  : bitwise_trie A. Admitted.

Example insert_example1 :
  lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
Proof.
Admitted.

Example insert_example2 :
  lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
Proof.
Admitted.

Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
  lookup k (insert k v t) = v.
Proof.
Admitted.

(** The rest of this assignment is optional -- you may skip it if you find that
    you are short on time *)

(** Define an operation to "merge" that takes two bitwise tries and merges
      them together. The [merge] definition should combine two bitwise tries,
      preferring map entries from the first bitwise trie when an entry exists
      for both bitwise tries.

      The [merge] definition should satisfy three properties: one is
      [left_lookup_merge], which says that if a trie contains an entry [v] for a
      key [k], then when this trie is the first trie in a merge with any other
      trie, then the resulting merged trie also contains an entry [v] for key [k].
      The other, [lookup_merge_None], says that if the merge of two tries
      contains no entry for a given key [k], then neither did the two original
      tries. The final is [merge_selfCompose], which says that if you repeatedly
      merge one trie with another one or more times, it is the same as merging
      the tries once. *)

Fixpoint merge {A} (t1 t2 : bitwise_trie A) : bitwise_trie A.
Admitted.

Lemma merge_example1 :
  merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
Proof. Admitted.
Lemma merge_example2 :
  merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
Proof. Admitted.
Lemma merge_example3 :
  merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
Proof. Admitted.

Theorem left_lookup_merge {A} : forall (t1 t2 : bitwise_trie A) k v,
    lookup k t1 = Some v ->
    lookup k (merge t1 t2) = Some v.
Proof.
Admitted.

Theorem lookup_merge_None {A} : forall (t1 t2 : bitwise_trie A) k,
    lookup k (merge t1 t2) = None ->
    lookup k t1 = None /\ lookup k t2 = None.
Proof.
Admitted.


Theorem merge_selfCompose {A} : forall n (t1 t2 : bitwise_trie A),
    0 < n ->
    selfCompose (merge t1) n t2 = merge t1 t2.
Proof.
Admitted.

(* Credits: Adapted from:
 * - MIT's 6.512 Formal Reasoning About Programs, Spring 2023
 * - EPFL's CS-628: Interactive Theorem Proving, Spring 2024
 * 
 * Contributors:
 * - Ben Sherman
 * - Adam Chlipala
 * - Nate Foster
 * - Samuel Gruetter
 * - Clément Pit-Claudel
 * - Amanda Liu
 * - Alexandre Pinazza
 *)
