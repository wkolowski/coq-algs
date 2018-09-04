Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import TreeSort.

Theorem treeSort_sorted :
  forall (A : LinDec) (l : list A), sorted A (treeSort A l).
Proof.
  unfold treeSort. intros. apply BTree_toList_sorted. apply fromList_is_bst.
Qed.

Theorem treeSort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (treeSort A l).
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

Instance Sort_treeSort (A : LinDec) : Sort A :=
{
    sort := @treeSort A;
    sort_sorted := treeSort_sorted A;
    sort_perm := treeSort_perm A
}.

Lemma treeSort'_spec :
  @treeSort' = @treeSort.
Proof.
  ext A. ext l. unfold treeSort'.
  rewrite fromList'_spec, BTree_toList'_spec.
  unfold treeSort. reflexivity.
Qed.

Instance Sort_treeSort' (A : LinDec) : Sort A :=
{
    sort := @treeSort' A;
}.
Proof.
  all: intros; rewrite treeSort'_spec.
    apply treeSort_sorted.
    apply treeSort_perm.
Defined.