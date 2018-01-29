Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import TreeSort.

From mathcomp Require Import ssreflect.

Theorem treeSort_sorted :
  forall (A : LinDec) (l : list A), sorted A (treeSort A l).
Proof.
  unfold treeSort. intros. apply BTree_toList_sorted. apply fromList_is_bst.
Qed.

Theorem treeSort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (treeSort A l).
Proof.
  unfold treeSort, perm. intros.
  elim: l => [| h t IH] //=.
    by rewrite count_toList count_ins -count_toList -IH.
Qed.

Instance Sort_treeSort : Sort :=
{
    sort := treeSort;
    sort_sorted := treeSort_sorted;
    sort_perm := treeSort_perm
}.

Theorem treeSort'_sorted :
  forall (A : LinDec) (l : list A), sorted A (treeSort' A l).
Proof.
  unfold treeSort'. intros. apply toList'_sorted.
  try apply fromList'_is_bst.
Abort.