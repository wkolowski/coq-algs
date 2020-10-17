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

Fixpoint fromList {A : Type} (p : A -> A -> bool) (l : list A) : SplayHeap A :=
match l with
    | [] => empty
    | h :: t => insert p h (fromList p t)
end.

Definition splaySort {A : Type} (p : A -> A -> bool) (l : list A) : list A :=
  BTree_toList (fromList p l).

(*
Lemma fromList_isBST :
  forall (A : LinDec) (p : A -> A -> comparison) (l : list A),
    isBST p (fromList p l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insert. assumption.
Qed.
*)

(*
Theorem Sorted_splaySort :
  forall (A : LinDec) (p : A -> A -> bool) (l : list A),
    Sorted A (splaySort p l).
Proof.
  intros. unfold splaySort. apply Sorted_BTree_toList, fromList_isBST.
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
*)

Lemma Permutation_partition :
  forall (A : LinDec) (p : A -> A -> bool) (pivot : A) (h h1 h2 : SplayHeap A),
    partition p pivot h = (h1, h2) ->
      Permutation (BTree_toList h) (BTree_toList h1 ++ BTree_toList h2).
Proof.
  intros A p pivot h.
  functional induction @partition A p pivot h; cbn in *; intros.
    inv H.
    inv H. cbn. rewrite app_nil_r. reflexivity.
    inv H. cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. apply Permutation_app.
        reflexivity.
        constructor. apply IHp0. assumption.
    inv H. cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. rewrite (IHp0 _ _ e3). rewrite <- !app_assoc. reflexivity.
    inv H.
    inv H. cbn. rewrite (IHp0 _ _ e3). rewrite <- !app_assoc. cbn.
      rewrite <- app_assoc. reflexivity.
    inv H. rewrite (IHp0 _ _ e3). cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma Permutation_BTree_toList_insert :
  forall (A : LinDec) (p : A -> A -> bool) (x : A) (t : BTree A),
    Permutation (BTree_toList (insert p x t)) (x :: BTree_toList t).
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    unfold insert. destruct (partition p x (node v l t1)) eqn: Heq.
      cbn. rewrite Permutation_app_comm. cbn. constructor.
        rewrite (@Permutation_partition _ _ _ _ _ _ Heq).
          apply Permutation_app_comm.
Qed.

Lemma Permutation_splaySort :
  forall (A : LinDec) (p : A -> A -> bool) (l : list A),
    Permutation (splaySort p l) l.
Proof.
  intros. unfold splaySort.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_BTree_toList_insert. constructor. assumption.
Qed.