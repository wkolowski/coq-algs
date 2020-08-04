Require Import List.
Import ListNotations.

Module Moving.

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

End Moving.

Module Counting.

Fixpoint count {A : Type} (p : A -> bool) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => (if p h then 1 else 0) + count p t
end.

Definition Permutation {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

Require Import ImprovingPatchworkDefinitions.
Import M3.

Class Sort
  {A : Type} (R : A -> A -> Prop) (f : list A -> list A) : Prop :=
{
    isSorted : forall l : list A, Sorted R (f l);
    isPermutation : forall l : list A, Permutation l (f l)
}.

End Counting.