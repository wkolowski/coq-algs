Require Export LinDec.
Require Export Sorting.Sort.

Require Export BTree.
Require Export BST.

Require Export ListLemmas.

Fixpoint insertBT {A : Type} (cmp : A -> A -> bool) (x : A) (t : BTree A) : BTree A :=
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
    BTree_toList (fromList cmp l).

Lemma Elem_insertBT :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    Elem x (insertBT cmp y t) -> cmp x y = Eq \/ Elem x t.
Proof.
Admitted.

Lemma isBST_insertBT :
  forall {A : Type} (cmp :  A -> A -> comparison) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insertBT cmp x t).
Proof.
  induction t as [| v l IHl r IHr]; cbn.
    auto.
    intro. destruct (cmp x v) eqn: Hcmp; cbn; auto.
      inv H. constructor; auto. intros. apply Elem_insertBT in H. destruct H; auto.
Admitted.

(* Lemma count_BTree_insert :
  forall (A : Type) (cmp : cmp_spec A) (p : A -> bool) (x : A) (t : BTree A),
    count_BTree p (insert cmp x t) =
      if p x then 1 + count_BTree p t else count_BTree p t.
Proof.
  induction t; cbn.
    reflexivity.
    destruct (cmpr_spec x a); cbn;
      rewrite ?IHt1, ?IHt2;
      destruct (p x) eqn: Hpx, (p a) eqn: Hpa; cbn; try lia.
Abort.
 *)

Lemma isBST_fromList :
  forall {A : Type} (cmp : A -> A -> comparison) (l : list A),
    isBST cmp (fromList cmp l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insertBT. assumption.
Qed.

Lemma Sorted_treeSort :
  forall {A : Type} (cmp : A -> A -> comparison) (l : list A),
    Sorted cmp (treeSort cmp l).
Proof.
  unfold treeSort. intros. apply Sorted_BTree_toList, isBST_fromList.
Qed.

Lemma count_BTree_insertBT :
  forall {A : Type} (cmp : A -> A -> bool) (p : A -> bool) (x : A) (t : BTree A),
    count_BTree p (insertBT cmp x t) =
      if p x then 1 + count_BTree p t else count_BTree p t.
Proof.
  induction t as [| v l r]; cbn.
    reflexivity.
    destruct (cmp x v); cbn; destruct (p v), (p x); lia.
Qed.

Lemma perm_treeSort :
  forall {A : Type} (cmp : A -> A -> bool) (l : list A),
    perm (treeSort cmp l) l.
Proof.
  induction l as [| h t]; intro; cbn.
    reflexivity.
    rewrite count_toList, count_BTree_insertBT, <- count_toList, <- IHt. reflexivity.
Qed.

Lemma Permutation_treeSort_aux :
  forall {A : Type} (cmp : A -> A -> bool) (x : A) (t : BTree A),
    Permutation (BTree_toList (insertBT cmp x t)) (x :: BTree_toList t).
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

Instance Sort_treeSort (A : Type) (cmp : A -> A -> comparison) : Sort cmp :=
{
    sort := treeSort cmp;
    Sorted_sort := Sorted_treeSort cmp;
    Permutation_sort := Permutation_treeSort cmp;
}.