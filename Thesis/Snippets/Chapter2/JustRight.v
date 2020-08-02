Require Import List.
Import ListNotations.

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