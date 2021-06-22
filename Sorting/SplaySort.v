Require Export CoqAlgs.Base.
Require Export Sorting.Sort.
Require Export ListLemmas.

Require Import BST.

Require Export SplayTree.

Set Implicit Arguments.

Fixpoint fromList {A : Type} (p : A -> A -> bool) (l : list A) : SplayTree A :=
match l with
    | [] => empty
    | h :: t => insert p h (fromList p t)
end.

Definition splaySort {A : Type} (p : A -> A -> bool) (l : list A) : list A :=
  inorder (fromList p l).

Lemma isBST_fromList :
  forall (A : Type) (p : A -> A -> comparison) (l : list A),
    isBST p (fromList p l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insert. assumption.
Qed.

Theorem Sorted_splaySort :
  forall {A : Ord} (l : list A),
    Sorted cmp (splaySort cmp l).
Proof.
  intros. unfold splaySort. apply Sorted_inorder, isBST_fromList.
Qed.

Lemma Permutation_splay :
  forall (A : Ord) (p : A -> A -> bool) (pivot : A) (h h1 h2 : SplayTree A),
    splay p pivot h = (h1, h2) ->
      Permutation (inorder h) (inorder h1 ++ inorder h2).
Proof.
  intros A p pivot h.
  functional induction @splay A p pivot h; cbn in *; inv 1.
    cbn. rewrite app_nil_r. reflexivity.
    cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. apply Permutation_app.
        reflexivity.
        constructor. apply IHp0. assumption.
    cbn. rewrite <- !app_assoc. cbn. apply Permutation_app.
      reflexivity.
      constructor. rewrite (IHp0 _ _ e3). rewrite <- !app_assoc. reflexivity.
    cbn. rewrite (IHp0 _ _ e3). rewrite <- !app_assoc. cbn.
      rewrite <- app_assoc. reflexivity.
    rewrite (IHp0 _ _ e3). cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma Permutation_inorder_insert :
  forall (A : Ord) (p : A -> A -> bool) (x : A) (t : BTree A),
    Permutation (inorder (insert p x t)) (x :: inorder t).
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    unfold insert. destruct (splay p x (node v l t1)) eqn: Heq.
      cbn. rewrite Permutation_app_comm. cbn. constructor.
        rewrite (@Permutation_splay _ _ _ _ _ _ Heq).
          apply Permutation_app_comm.
Qed.

Theorem Permutation_splaySort :
  forall (A : Ord) (p : A -> A -> bool) (l : list A),
    Permutation (splaySort p l) l.
Proof.
  intros. unfold splaySort.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_inorder_insert. constructor. assumption.
Qed.

Instance Sort_splaySort (A : Ord) : Sort cmp :=
{
    sort := splaySort trich_leb;
    Sorted_sort := Sorted_splaySort;
    Permutation_sort := Permutation_splaySort A cmp;
}.

(* Another way to prove permutation properties *)

Lemma countBT_splay :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (pivot : A) (h h1 h2 : SplayTree A),
    splay cmp pivot h = (h1, h2) ->
      countBT p h = countBT p h1 + countBT p h2.
Proof.
  intros until h. revert p.
  functional induction splay cmp pivot h;
  inv 1; cbn; erewrite IHp; eauto;
  destruct (p x), (p y); cbn; unfold id; lia.
Qed.

Lemma countBT_insert :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (x : A) (h : SplayTree A),
    countBT p (insert cmp x h) =
    (if p x then 1 else 0) + countBT p h.
Proof.
  intros. unfold insert.
  destruct (splay cmp x h) eqn: Heq.
  apply (countBT_splay cmp p) in Heq.
  rewrite Heq. cbn. destruct (p x); reflexivity.
Qed.

Lemma countBT_merge :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (h1 h2 : SplayTree A),
    countBT p (merge cmp h1 h2) = countBT p h1 + countBT p h2.
Proof.
  intros until h2.
  functional induction (merge cmp h1 h2); cbn.
    reflexivity.
    apply (countBT_splay cmp p) in e0.
      destruct (p v); unfold id; lia.
Qed.

Lemma countBT_fromList :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (l : list A),
    countBT p (fromList cmp l) = Perm.count p l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite countBT_insert. rewrite IHt.
      destruct (p h); reflexivity.
Qed.

Theorem perm_splaySort :
  forall (A : Type) (cmp : A -> A -> bool) (l : list A),
    perm l (splaySort cmp l).
Proof.
  unfold splaySort, perm. intros.
  rewrite count_toList. rewrite countBT_fromList. reflexivity.
Qed.