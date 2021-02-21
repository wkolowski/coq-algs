Require Export WayOfTheCoq.

(** * Not that easy *)

Module NotEasy.

Fixpoint nth {A : Type} (n : nat) (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match n with
            | 0 => Some h
            | S n' => nth n' t
        end
end.

Definition sorted {A : Type} (l : list nat) : Prop :=
  forall i j : nat, i <= j ->
    forall n m : nat,
      nth i l = Some n -> nth j l = Some m -> n <= m.

Print nat.
(*
Inductive nat : Set := O : nat | S : nat -> nat
*)

Print le.
(*
Inductive le (n : nat) : nat -> Prop :=
    le_n : n <= n | le_S : forall m : nat, n <= m -> n <= S m
*)

Print list.
(*
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A
*)

End NotEasy.

(** * Improving patchwork definitions *)

Module ImprovingPatchworkDefinitions1.

Inductive LessThanAll (n : nat) : list nat -> Prop :=
    | LessThanAll_nil : LessThanAll n []
    | LessThanAll_cons :
        forall (h : nat) (t : list nat),
          n <= h -> LessThanAll n t -> LessThanAll n (h :: t).

Inductive Sorted : list nat -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_cons :
        forall (h : nat) (t : list nat),
          LessThanAll h t -> Sorted t -> Sorted (h :: t).

End ImprovingPatchworkDefinitions1.

Module ImprovingPatchworkDefinitions2.

Inductive Sorted : list nat -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_singl : forall n : nat, Sorted [n]
    | Sorted_cons :
        forall (n m : nat) (l : list nat),
          n <= m -> Sorted (m :: l) -> Sorted (n :: m :: l).

End ImprovingPatchworkDefinitions2.

Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | Sorted_nil : Sorted R []
    | Sorted_singl : forall x : A, Sorted R [x]
    | Sorted_cons :
        forall (x y : A) (l : list A),
          R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

(** * Just about right... or is it? Staying on the right track *)

Module Generating.

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
  | perm_nil1 :
      Permutation [] []
  | perm_skip :
      forall (x : A) (l1 l2 : list A),
        Permutation l1 l2 -> Permutation (x :: l1) (x :: l2)
  | perm_swap :
      forall (x y : A) (l : list A),
        Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans :
      forall l1 l2 l3 : list A,
        Permutation l1 l2 -> Permutation l2 l3 -> Permutation l1 l3.

End Generating.

Module Counting.

Fixpoint count {A : Type} (p : A -> bool) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => (if p h then 1 else 0) + count p t
end.

Definition Permutation {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

End Counting.

Module Moving.

Inductive Transposition {A : Type} : list A -> list A -> Prop :=
    | Transposition' :
        forall (l1 : list A) (x : A) (l2 : list A) (y : A) (l3 : list A),
          Transposition (l1 ++ x :: l2 ++ y :: l3) (l1 ++ y :: l2 ++ x :: l3).

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    | Permutation_refl :
        forall l : list A, Permutation l l
    | Permutation_step_trans :
        forall l1 l2 l3 : list A,
          Transposition l1 l2 -> Permutation l2 l3 -> Permutation l1 l3.

End Moving.

Module Moving2.

Inductive AdjacentTransposition {A : Type} : list A -> list A -> Prop :=
    | AdjacentTransposition' :
        forall (x y : A) (l1 l2 : list A),
          AdjacentTransposition (l1 ++ x :: y :: l2) (l1 ++ y :: x :: l2).

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    | Permutation_refl   :
        forall l : list A, Permutation l l
    | Permutation_step_trans :
        forall l1 l2 l3 : list A,
          AdjacentTransposition l1 l2 -> Permutation l1 l2 -> Permutation l2 l3.

End Moving2.

Class Sort
  {A : Type} (R : A -> A -> Prop) (f : list A -> list A) : Prop :=
{
    isSorted : forall l : list A, Sorted R (f l);
    isPermutation : forall l : list A, Permutation l (f l)
}.