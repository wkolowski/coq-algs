Require Import TreeSort.

(* TODO
Theorem Sorted_treeSort :
  forall (A : LinDec) (l : list A), Sorted A (treeSort A l).
Proof.
  unfold treeSort. intros. apply Sorted_BTree_toList. apply fromList_is_bst.
Qed.

Theorem treeSort_perm :
  forall (A : LinDec) (l : list A),
    perm l (treeSort A l).
Proof.
  unfold perm. induction l as [| h t]; cbn; intro.
    reflexivity.
    rewrite count_toList, count_ins, <- count_toList, <- IHt. reflexivity.
Qed.

Lemma Permutation_treeSort_aux :
  forall (A : LinDec) (x : A) (t : BTree A),
    Permutation (BTree_toList (BTree_ins x t)) (x :: BTree_toList t).
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    destruct (x <=? v); cbn.
      rewrite r. cbn. reflexivity.
      rewrite IHt1. rewrite Permutation_app_comm, perm_swap. cbn.
        constructor. rewrite Permutation_app_comm, Permutation_middle.
          reflexivity.
Qed.

Lemma Permutation_treeSort :
  forall (A : LinDec) (l : list A),
    Permutation (treeSort A l) l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_treeSort_aux. constructor. assumption.
Qed.

#[refine]
Instance Sort_treeSort (A : LinDec) : Sort A :=
{
    sort := @treeSort A;
    Sorted_sort := Sorted_treeSort A;
}.
Proof.
  intros. apply perm_Permutation. rewrite <- treeSort_perm. reflexivity.
Defined.

Lemma treeSort'_spec :
  @treeSort' = @treeSort.
Proof.
  ext A. ext l. unfold treeSort'.
  rewrite fromList'_spec, BTree_toList'_spec.
  unfold treeSort. reflexivity.
Qed.

#[refine]
Instance Sort_treeSort' (A : LinDec) : Sort A :=
{
    sort := @treeSort' A;
}.
Proof.
  all: intros; rewrite treeSort'_spec.
    apply Sorted_treeSort.
    apply perm_Permutation. rewrite <- treeSort_perm. reflexivity.
Defined.
*)