Require Import List.
Import ListNotations.

Module M1.

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

End M1.

Module M2.

Inductive Sorted : list nat -> Prop :=
    | Sorted_nil : Sorted []
    | Sorted_singl : forall n : nat, Sorted [n]
    | Sorted_cons :
        forall (n m : nat) (l : list nat),
          n <= m -> Sorted (m :: l) -> Sorted (n :: m :: l).

End M2.