Require Export Ord.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Function insertBT {A : Type} (cmp : A -> A -> bool) (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => node x empty empty
    | node v l r =>
        if cmp x v
        then node v (insertBT cmp x l) r
        else node v l (insertBT cmp x r)
end.

Fixpoint fromList
  {A : Type} (cmp : A -> A -> bool) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insertBT cmp h (fromList cmp t)
end.

Definition treeSort
  {A : Type} (cmp : A -> A -> bool) (l : list A) : list A :=
    inorder (fromList cmp l).

Lemma Elem_insertBT :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    Elem x (insertBT cmp y t) -> (* cmp x y = Eq *) x = y \/ Elem x t.
Proof.
  intros until t. revert x.
  functional induction (insertBT cmp y t);
  Elems'.
Qed.

(* TODO: split definition of BSTs into two *)Lemma isBST_insertBT :
  forall {A : Ord} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insertBT cmp x t).
Proof.
  intros until t.
  functional induction insertBT cmp x t;
  isBST'; Elems.
    apply Elem_insertBT in H. inv H.
      unfold comparison2bool in e0. trich.
      specialize (IHb0 H3). admit.
    apply Elem_insertBT in H. inv H. admit.
Admitted.

Lemma countBT_insertBT :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (x : A) (t : BTree A),
    countBT p (insertBT cmp x t) =
      (if p x then 1 else 0) + countBT p t.
Proof.
  intros until t.
  functional induction insertBT cmp x t;
  cbn; lia.
Qed.

Lemma isBST_fromList :
  forall {A : Ord} (l : list A),
    isBST cmp (fromList cmp l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insertBT. assumption.
Qed.

Lemma Sorted_treeSort :
  forall {A : Ord} (l : list A),
    Sorted cmp (treeSort cmp l).
Proof.
  unfold treeSort. intros. apply Sorted_inorder, isBST_fromList.
Qed.

Lemma perm_treeSort :
  forall {A : Type} (cmp : A -> A -> bool) (l : list A),
    perm (treeSort cmp l) l.
Proof.
  induction l as [| h t]; intro; cbn.
    reflexivity.
    rewrite count_toList, countBT_insertBT, <- count_toList, <- IHt. reflexivity.
Qed.

Lemma Permutation_treeSort_aux :
  forall {A : Type} (cmp : A -> A -> bool) (x : A) (t : BTree A),
    Permutation (inorder (insertBT cmp x t)) (x :: inorder t).
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    destruct (cmp x v); cbn.
      rewrite r. cbn. reflexivity.
      rewrite IHt1, Permutation_app_comm, perm_swap. cbn.
        constructor. rewrite Permutation_app_comm, Permutation_middle.
          reflexivity.
Qed.

Lemma Permutation_treeSort :
  forall {A : Type} (cmp : A -> A -> bool) (l : list A),
    Permutation (treeSort cmp l) l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_treeSort_aux. constructor. assumption.
Qed.

Instance Sort_treeSort {A : Ord} : Sort cmp :=
{
    sort := treeSort cmp;
    Sorted_sort := Sorted_treeSort;
    Permutation_sort := Permutation_treeSort cmp;
}.