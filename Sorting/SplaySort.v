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

Theorem Sorted_splaySort :
  forall (A : LinDec) (l : list A),
    Sorted A (splaySort A l).
Proof.
  intros. unfold splaySort. apply Sorted_BTree_toList, fromList_is_bst.
Qed.

Lemma count_BTree_fromList :
  forall (A : LinDec) (p : A -> bool) (l : list A),
    count_BTree p (fromList l) = Perm.count p l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite insert_count_BTree. rewrite IHt.
      destruct (p h); reflexivity.
Qed.

Theorem splaySort_perm :
  forall (A : LinDec) (l : list A),
    perm l (splaySort A l).
Proof.
  unfold splaySort, perm. intros.
  rewrite count_toList. rewrite count_BTree_fromList. reflexivity.
Qed.

Lemma Permutation_partition :
  forall (A : LinDec) (pivot : A) (h h1 h2 : SplayHeap A),
    partition pivot h = (h1, h2) ->
      Permutation (BTree_toList h) (BTree_toList h1 ++ BTree_toList h2).
Proof.
  intros A pivot h.
  functional induction @partition A pivot h; cbn in *; intros.
    inv H.
    inv H. cbn. rewrite app_nil_r. reflexivity.
    inv H. cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. apply Permutation_app.
        reflexivity.
        constructor. apply IHp. assumption.
    inv H. cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. rewrite (IHp _ _ e3). rewrite <- !app_assoc. reflexivity.
    inv H.
    inv H. cbn. rewrite (IHp _ _ e3). rewrite <- !app_assoc. cbn.
      rewrite <- app_assoc. reflexivity.
    inv H. rewrite (IHp _ _ e3). cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma Permutation_BTree_toList_insert :
  forall (A : LinDec) (x : A) (t : BTree A),
    Permutation (BTree_toList (insert x t)) (x :: BTree_toList t).
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    unfold insert. destruct (partition x (node v l t1)) eqn: Heq.
      cbn. rewrite Permutation_app_comm. cbn. constructor.
        rewrite (@Permutation_partition _ _ _ _ _ Heq).
          apply Permutation_app_comm.
Qed.

Lemma Permutation_splaySort :
  forall (A : LinDec) (l : list A),
    Permutation (splaySort A l) l.
Proof.
  intros. unfold splaySort.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_BTree_toList_insert. constructor. assumption.
Qed.