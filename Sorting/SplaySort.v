Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import BST.

Require Export SplayHeap.

Set Implicit Arguments.

(*Lemma size_deleteMin :
  forall (A : LinDec) (h : SplayHeap A),
    size (deleteMin h) = pred (size h).
Proof.
  intros. functional induction deleteMin h; cbn; trivial.
  rewrite IHs. destruct l; cbn.
    contradiction.
    trivial.
Qed.

Lemma size_deleteMin' :
  forall (A : LinDec) (h h' : SplayHeap A),
    h' = snd (deleteMin' h) -> size h' = pred (size h).
Proof.
  intros. functional induction deleteMin' h; cbn; inv H; trivial.
  destruct l; cbn.
    contradiction.
    rewrite e0 in IHp. cbn in IHp. rewrite IHp; trivial.
Qed.*)

Fixpoint fromList {A : LinDec} (l : list A) : SplayHeap A :=
match l with
    | [] => empty
    | h :: t => insert h (fromList t)
end.

Definition splaySort (A : LinDec) (l : list A) : list A :=
  BTree_toList (fromList l).

Lemma fromList_is_bst :
  forall (A : LinDec) (l : list A),
    is_bst (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply insert_is_bst. assumption.
Qed.

Theorem splaySort_sorted :
  forall (A : LinDec) (l : list A),
    sorted A (splaySort A l).
Proof.
  intros. unfold splaySort. apply BTree_toList_sorted, fromList_is_bst.
Qed.

Lemma count_BTree_fromList :
  forall (A : LinDec) (x : A) (l : list A),
    count_BTree A x (fromList l) = count A x l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite insert_count_BTree. dec.
Qed.

Theorem splaySort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (splaySort A l).
Proof.
  unfold splaySort, perm. intros.
  rewrite count_toList. rewrite count_BTree_fromList. reflexivity.
Qed.

