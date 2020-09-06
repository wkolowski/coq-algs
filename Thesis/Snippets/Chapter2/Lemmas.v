Require Import Specification.

Require Export Setoid.

Lemma Permutation_refl :
  forall {A : Type} {l : list A},
    Permutation l l.
Proof.
Admitted.

Lemma Permutation_trans :
  forall {A : Type} {l1 l2 l3 : list A},
    Permutation l1 l2 ->
    Permutation l2 l3 ->
      Permutation l1 l3.
Proof.
Admitted.

Lemma Permutation_cons :
  forall {A : Type} {h : A} {t1 t2 : list A},
    Permutation t1 t2 ->
      Permutation (h :: t1) (h :: t2).
Proof.
Admitted.

Lemma Permutation_app :
  forall {A : Type} {l1 l2 l1' l2' : list A},
    Permutation l1 l1' ->
    Permutation l2 l2' ->
      Permutation (l1 ++ l2) (l1' ++ l2').
Proof.
Admitted.