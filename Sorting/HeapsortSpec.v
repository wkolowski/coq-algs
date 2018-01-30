Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export BTree.
Require Export BST.
Require Export LeftistHeap.

Require Export Heapsort.

Set Implicit Arguments.

Lemma toList_sorted :
  forall (A : LinDec) (t : BTree A),
    is_heap t -> sorted A (toList t).
Proof.
  intros A t. functional induction @toList A t.
    constructor.
    functional induction @toList A t'; constructor.
      eapply deleteMin_spec; eauto. eapply deleteMin_elem. eauto.
      apply IHl. eapply deleteMin_is_heap; eauto.
Qed.

Lemma fromList_is_heap :
  forall (A : LinDec) (l : list A),
    is_heap (fromList l).
Proof.
  intros. functional induction @fromList A l; cbn.
    constructor.
    unfold insert'. apply merge'_is_heap; auto.
      constructor; auto; inversion 1.
Qed.

Theorem leftistHeapsort_sorted :
  forall (A : LinDec) (l : list A),
    sorted A (leftistHeapsort A l).
Proof.
  unfold leftistHeapsort. intros.
    apply toList_sorted. apply fromList_is_heap.
Qed.

Lemma count_BTree_merge' :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    count_BTree x (merge' (t1, t2)) =
    count_BTree x t1 + count_BTree x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp;
  balance; cbn; rewrite (IHb _ _ _ eq_refl); dec.
Qed.

Lemma count_BTree_insert :
  forall (A : LinDec) (x y : A) (t : BTree A),
    count_BTree x (insert' y t) =
      if x =? y
      then S (count_BTree x t)
      else count_BTree x t.
Proof.
  intros. unfold insert'. rewrite count_BTree_merge'. dec.
Qed.

Lemma count_fromList :
  forall (A : LinDec) (x : A) (l : list A),
    count_BTree x (fromList l) = count A x l.
Proof.
  intros. functional induction @fromList A l;
  try rewrite count_BTree_insert; dec.
Qed.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (toList t) = count_BTree x t.
Proof.
  intros. functional induction @toList A t; cbn;
  destruct t; inv e; dec; rewrite IHl, count_BTree_merge'; trivial.
Qed.

Theorem leftistHeapsort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (leftistHeapsort A l).
Proof.
  unfold perm, leftistHeapsort. intros.
  rewrite count_toList, count_fromList. trivial.
Qed.

Instance Sort_leftistHeapsort : Sort :=
{
    sort := @leftistHeapsort;
    sort_sorted := @leftistHeapsort_sorted;
    sort_perm := leftistHeapsort_perm
}.