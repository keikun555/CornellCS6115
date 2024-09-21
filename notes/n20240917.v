Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.

Definition nat_lte := Compare_dec.le_gt_dec.

Check nat_lte.

Fail Fixpoint merge (xs ys:list nat) { struct xs } : list nat :=
  match xs, ys with
  | [],ys => ys
  | xs, [] => xs
  | x::xs', y::ys' => 
      if nat_lte x y then x :: merge xs' ys else y :: merge xs ys'
  end.

Fixpoint merge (xs:list nat) : list nat -> list nat :=
  match xs with
  | [] => fun ys => ys
  | x::xs' =>
      (fix inner_merge (ys:list nat) :=
        match ys with
        | [] => x::xs'
        | y::ys' => if nat_lte x y then x :: merge xs' ys else y:: inner_merge ys'
        end)
  end.

Require Import Coq.Program.Wf.

Program Fixpoint merge' (xs ys:list nat) { measure (length xs + length ys) } : list nat :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x::xs', y::ys' => 
      if nat_lte x y then
        x :: merge' xs' ys
      else
        y :: merge' xs ys'
  end.
Final Obligation.
  simpl. lia.
Defined.

Print merge'.
Print merge'_func.
Check Fix_sub.
Check merge'_func_obligation_4.
Print MR.
Check lt_wf.
Print well_founded.
Print Acc.
(* Every element that is less than x must also be accessible *)

Fixpoint merge_pairs (xs: list (list nat)) : list (list nat) :=
  match xs with
  | h1::h2::t => (merge h1 h2) :: (merge_pairs t)
  | xs' => xs'
  end.

Definition make_lists (xs: list nat) : list (list nat) :=
  List.map (fun x => x::nil) xs.
