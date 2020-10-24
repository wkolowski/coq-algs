Require Export LinDec.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Definition treeSort
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : list A :=
    BTree_toList (fromList cmp l).

Lemma Sorted_treeSort :
  forall (A : Type) (cmp : cmp_spec A) (l : list A),
    Sorted cmpr (treeSort cmp l).
Proof.
  unfold treeSort. intros. apply Sorted_BTree_toList, isBST_fromList.
Qed.

Lemma perm_treeSort :
  forall (A : Type) (cmp : A -> A -> comparison) (l : list A),
    perm (treeSort cmp l) l.
Proof.
  induction l as [| h t]; intro; cbn.
    reflexivity. Search count insert.
    rewrite count_toList. Search count_BTree. count_BTree_insert, <- count_toList, <- IHt. reflexivity.
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
  intros. apply perm_Permutation. rewrite <- perm_treeSort. reflexivity.
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
    apply perm_Permutation. rewrite <- perm_treeSort. reflexivity.
Defined.