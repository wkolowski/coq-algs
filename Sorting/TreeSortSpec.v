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

Instance Sort_treeSort : Sort :=
{
    sort := treeSort;
    sort_sorted := treeSort_sorted;
    sort_perm := treeSort_perm
}.

Lemma treeSort'_spec :
  @treeSort' = @treeSort.
Proof.
  ext A. ext l. unfold treeSort'.
  rewrite fromList'_spec, BTree_toList'_spec.
  unfold treeSort. reflexivity.
Qed.

Instance Sort_treeSort' : Sort :=
{
    sort := treeSort';
}.
Proof.
  all: intros; rewrite treeSort'_spec.
    apply treeSort_sorted.
    apply treeSort_perm.
Defined.