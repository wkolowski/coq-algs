Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Require Import BST.

Set Implicit Arguments.

Inductive is_heap {A : LinDec} : BTree A -> Prop :=
    | is_heap_empty : is_heap empty
    | is_heap_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, elem x l -> v ≤ x) -> is_heap l ->
          (forall x : A, elem x r -> v ≤ x) -> is_heap r ->
            is_heap (node v l r).

Lemma is_heap_inv_l :
  forall (A : LinDec) (v : A) (l r : BTree A),
    is_heap (node v l r) -> is_heap l.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_heap_inv_r :
  forall (A : LinDec) (v : A) (l r : BTree A),
    is_heap (node v l r) -> is_heap r.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_heap_inv_leq :
  forall (A : LinDec) (v : A) (l r : BTree A),
    is_heap (node v l r) -> forall x : A,
      elem x (node v l r) -> v ≤ x.
Proof.
  do 2 inversion 1; subst; auto.
Qed.

Hint Resolve is_heap_inv_l is_heap_inv_r.

Fixpoint right_spine {A : Type} (t : BTree A) : nat :=
match t with
    | empty => 0
    | node _ _ r => S (right_spine r)
end.

Inductive left_biased {A : LinDec} : BTree A -> Prop :=
    | left_biased_empty : left_biased empty
    | left_biased_node :
        forall (v : A) (l r : BTree A),
          right_spine r <= right_spine l ->
          left_biased l -> left_biased r ->
            left_biased (node v l r).

Hint Constructors BTree elem is_heap left_biased.

Record LeftistHeap (A : LinDec) : Type :=
{
    tree :> BTree A;
    tree_is_heap : is_heap tree;
    tree_is_left_biased : left_biased tree
}.

Ltac lh x :=
  let t := fresh "t" in
  let H := fresh "H" in
  let H' := fresh "H" in
    destruct x as [t H H']; destruct t;
    try inversion H; try inversion H'; subst; cbn.

Ltac inv x := inversion x; subst; auto.

Definition getMin {A : LinDec} (h : LeftistHeap A)
  : option A := root h.

Theorem getMin_spec :
  forall (A : LinDec) (h : LeftistHeap A) (m : A),
    getMin h = Some m -> forall x : A, elem x h -> m ≤ x.
Proof.
  lh h; inversion 1; subst. inversion 1; auto.
Qed.

Definition emptyHeap {A : LinDec} : LeftistHeap A.
Proof.
  split with (tree := empty); auto.
Defined.

Theorem emptyHeap_spec :
  forall (A : LinDec) (x : A), ~ elem x emptyHeap.
Proof.
  inversion 1.
Qed.

Definition singleton {A : LinDec} (x : A) : LeftistHeap A.
Proof.
  split with (tree := node x empty empty);
  constructor; auto; inversion 1.
Defined.

Theorem singleton_spec :
  forall (A : LinDec) (x : A),
    elem x (singleton x).
Proof.
  cbn. constructor.
Qed.

Theorem singleton_spec' :
  forall (A : LinDec) (x y : A),
    x <> y -> ~ elem x (singleton y).
Proof.
  inversion 2; subst; try contradiction; inv H2.
Qed.

Definition balance {A : Type} (v : A) (l r : BTree A) : BTree A :=
  if right_spine r <=? right_spine l
  then node v l r
  else node v r l.

Ltac balance := unfold balance in *;
match goal with
    | H : context [right_spine ?r <=? right_spine ?l] |- _ =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
    | |- context [right_spine ?r <=? right_spine ?l] =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
end.

Lemma balance_len :
  forall (A : Type) (v : A) (l r : BTree A),
    len (balance v l r) = len (node v l r).
Proof.
  intros. balance.
    trivial.
    apply len_swap.
Qed.

Lemma balance_elem :
  forall (A : Type) (x v : A) (l r : BTree A),
    elem x (balance v l r) <-> elem x (node v l r).
Proof.
  intros. balance.
    firstorder.
    split; inversion 1; subst; auto.
Qed.

Require Import Recdef.

Definition sum_of_sizes {A : Type} (p : BTree A * BTree A) : nat :=
  len (fst p) + len (snd p).

Function merge' {A : LinDec} (p : BTree A * BTree A)
  {measure sum_of_sizes p} : BTree A :=
match p with
    | (empty, t2) => t2
    | (t1, empty) => t1
    | (node v l r as t1, node v' l' r' as t2) =>
        if v <=? v'
        then balance v l (merge' (r, t2))
        else balance v' l' (merge' (t1, r'))
end.
Proof.
  1-2: intros; cbn; omega.
Defined.

Arguments merge' [x] _.

Lemma elem_merge' :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x (merge' (t1, t2)) -> elem x t1 \/ elem x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp; auto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
Qed.

Lemma elem_merge'_v2 :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x t1 \/ elem x t2 -> elem x (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp; auto.
    inv H; inv H0.
    inv H. inv H0.
    inv H.
      rewrite balance_elem. inv H0. apply elem_right.
        eapply IHb. left. exact H2. reflexivity.
      rewrite balance_elem. apply elem_right.
        eapply IHb. right. exact H0. reflexivity.
    inv H.
      rewrite balance_elem. apply elem_right.
        eapply IHb. left. exact H0. reflexivity.
      rewrite balance_elem. inv H0. apply elem_right.
        eapply IHb. right. exact H2. reflexivity.
Qed.

Arguments elem_merge' [A x t1 t2] _.

Theorem merge'_len :
  forall (A : LinDec) (t1 t2 : BTree A),
    len (merge' (t1, t2)) = len t1 + len t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp.
    rewrite balance_len. cbn. rewrite (IHb r (node v' l' r') eq_refl).
      cbn. omega.
    rewrite balance_len. cbn. rewrite (IHb (node v l r) r' eq_refl).
      cbn. omega.
Qed.

Theorem merge'_is_heap :
  forall (A : LinDec) (t1 t2 : BTree A),
    is_heap t1 -> is_heap t2 -> is_heap (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp;
  inv H; inv H0; balance.
    constructor; auto.
      intros. destruct (elem_merge' H1); auto.
        destruct (leqb_spec v v'); inv e0. eapply leq_trans with v'.
          apply l1.
          inv H2.
      apply (IHb _ _ H7 H0 eq_refl).
    constructor; auto.
      intros. destruct (elem_merge' H1); auto.
        destruct (leqb_spec v v'); inv e0. eapply leq_trans with v'.
          dec.
          inv H2.
      apply (IHb _ _ H7 H0 eq_refl).
      constructor; auto.
        intros. destruct (elem_merge' H1); auto.
          destruct (leqb_spec v v'); inv e0. eapply leq_trans with v.
            dec.
            inv H2.
      apply (IHb _ _ H H11 eq_refl).
      constructor; auto.
        intros. destruct (elem_merge' H1); auto.
          destruct (leqb_spec v v'); inv e0. eapply leq_trans with v.
            dec.
            inv H2.
      apply (IHb _ _ H H11 eq_refl).
Qed.

Theorem merge'_left_biased :
  forall (A : LinDec) (t1 t2 : BTree A),
    left_biased t1 -> left_biased t2 -> left_biased (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp;
  inv H; inv H0; balance; cbn in *;
  constructor; auto; try omega.
    1-2: apply (IHb _ _ H6 H0 eq_refl).
    1-2: apply (IHb _ _ H H9 eq_refl).
Qed.

Definition merge {A : LinDec} (h1 h2 : LeftistHeap A)
  : LeftistHeap A.
Proof.
  destruct h1 as [t1 H11 H12], h2 as [t2 H21 H22].
  split with (tree := @merge' A (t1, t2)).
  apply merge'_is_heap; assumption.
  apply merge'_left_biased; assumption.
Defined.

Definition insert' {A : LinDec} (x : A) (t : BTree A) : BTree A :=
  merge' (node x empty empty, t).

Definition insert {A : LinDec} (x : A) (h : LeftistHeap A)
  : LeftistHeap A.
Proof.
  split with (tree := merge (singleton x) h).
    destruct (merge _ _). cbn. assumption.
    destruct (merge _ _). cbn. assumption.
Defined.

Theorem insert_spec :
  forall (A : LinDec) (x y : A) (h : LeftistHeap A),
    elem x (insert y h) <-> x = y \/ elem x h.
Proof.
  split; destruct h; subst; cbn; intros.
    destruct (elem_merge' H); auto. inv H0; inv H2.
    destruct H; subst; apply elem_merge'_v2; auto.
Qed.

Definition deleteMin {A : LinDec} (t : BTree A)
  : option A * BTree A :=
match t with
    | empty => (None, empty)
    | node v l r => (Some v, merge' (l, r))
end.

Theorem deleteMin_is_heap :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      is_heap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply merge'_is_heap; assumption.
Qed.

Theorem deleteMin_spec :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst; cbn.
  intros. destruct (elem_merge' H0); auto.
Qed.

Theorem deleteMin_len :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> len t = S (len t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite merge'_len. trivial.
Qed.

Theorem deleteMin_elem :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

(* Leftist heapsort *)
Function fromList {A : LinDec} (l : list A) : BTree A :=
match l with
    | [] => emptyHeap
    | h :: t => insert' h (fromList t)
end.

Function toList {A : LinDec} (t : BTree A)
  {measure len t} : list A :=
match deleteMin t with
    | (None, _) => []
    | (Some m, t') => m :: toList t'
end.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  rewrite merge'_len. omega.
Defined.

Arguments toList [x] _.

Definition leftistHeapsort (A : LinDec) (l : list A)
  : list A := toList (fromList l).

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
    count_BTree A x (merge' (t1, t2)) =
    count_BTree A x t1 + count_BTree A x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp.
    balance; cbn.
      rewrite (IHb _ _ _ eq_refl). dec.
      rewrite (IHb _ _ _ eq_refl). dec.
    balance; cbn.
      rewrite (IHb _ _ _ eq_refl). dec.
      rewrite (IHb _ _ _ eq_refl). dec.
Qed.

Lemma count_BTree_insert :
  forall (A : LinDec) (x y : A) (t : BTree A),
    count_BTree A x (insert' y t) =
      if x =? y
      then S (count_BTree A x t)
      else count_BTree A x t.
Proof.
  intros. unfold insert'. rewrite count_BTree_merge'. dec.
Qed.

Lemma count_fromList :
  forall (A : LinDec) (x : A) (l : list A),
    count_BTree A x (fromList l) = count A x l.
Proof.
  intros. functional induction @fromList A l; dec.
    rewrite count_BTree_insert. dec.
    rewrite count_BTree_insert. dec.
Qed.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (toList t) = count_BTree A x t.
Proof.
  intros. functional induction @toList A t; cbn.
    destruct t; inv e.
    destruct t; inv e. dec.
      rewrite IHl, count_BTree_merge'. trivial.
      rewrite IHl, count_BTree_merge'. trivial.
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