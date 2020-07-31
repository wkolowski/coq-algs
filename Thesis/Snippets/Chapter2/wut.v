Require Import List.
Import ListNotations.

Inductive AllLess {A : Type} (R : A -> A -> Prop) (x : A) : list A -> Prop :=
    | AllLess_nil : AllLess R x []
    | AllLess_cons :
        forall (h : A) (t : list A),
          R x h -> AllLess R x t -> AllLess R x (h :: t).

Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | Sorted_nil : Sorted R []
    | Sorted_cons :
        forall (h : A) (t : list A),
          AllLess R h t -> Sorted R t -> Sorted R (h :: t).