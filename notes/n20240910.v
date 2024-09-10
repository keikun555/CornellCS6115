
Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Require Import Lia.

Inductive expr : Type :=
  | Const : nat -> expr
  | Var : string -> expr
  | Plus : expr -> expr -> expr
  | Mult : expr -> expr -> expr.

Fixpoint eval (env : string -> nat) e :=
  match e with
  | Const n => n
  | Var s => env s
  | Plus e1 e2 => eval env e1 + eval env e2
  | Mult e1 e2 => eval env e1 * eval env e2
  end.

Definition e1 := Plus (Const 3) (Var "x").

Definition env1 := fun s =>
  match s with
  | "x" => 5
  | _ => 0
  end.

Compute eval env1 e1.
Check eval env1 e1.
Print eval.

Inductive tree :=
  | Leaf : tree
  | Node : (nat -> tree) -> tree.

Definition t0 := Node (fun n => Leaf).
Definition t1 := Node (fun n => if Nat.leb n 10 then t0 else Leaf).

Fixpoint wide n :=
  match n with 
  | 0 => Leaf
  | S n' => Node (fun n => wide n')
  end.

Definition t2 := Node (fun n => wide n).

Fixpoint depth (path : nat -> nat) (t : tree) :=
  match t with
  | Leaf => 0
  | Node f => 1 + depth (fun n => path (S n)) (f (path 0))
  end.

Inductive op :=
  | PushOp : nat -> op
  | VarOp : string -> op
  | AddOp : op
  | MultOp : op.
