Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Import BST.

Require Export LinDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

Inductive is_heap {A : LinDec} : BTree A -> Prop :=
    | is_heap_empty : is_heap empty
    | is_heap_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, elem x l -> v ≤ x) -> is_heap l ->
          (forall x : A, elem x r -> v ≤ x) -> is_heap r ->
            is_heap (node v l r).

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

Definition isEmpty {A : Type} (h : BTree A) : bool :=
match h with
    | empty => true
    | _ => false
end.

Definition singleton {A : Type} (x : A) : BTree A :=
  node x empty empty.

Definition balance {A : Type} (v : A) (l r : BTree A) : BTree A :=
  if right_spine r <=? right_spine l
  then node v l r
  else node v r l.


Ltac elem :=
  intros; unfold singleton in *; cbn in *; subst; repeat
match goal with
    | |- elem ?x (node ?x _ _) => constructor
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ empty empty) |- _ => inv H
    | H : elem _ _ /\ elem _ _ |- _ => destruct H
    | H : elem _ _ \/ elem _ _ |- _ => destruct H
end; auto.

Ltac balance := unfold balance in *;
match goal with
    | H : context [right_spine ?r <=? right_spine ?l] |- _ =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
    | |- context [right_spine ?r <=? right_spine ?l] =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
end.

Require Import Recdef.

Definition sum_of_sizes {A : Type} (p : BTree A * BTree A) : nat :=
  size (fst p) + size (snd p).

Function merge {A : LinDec} (p : BTree A * BTree A)
  {measure sum_of_sizes p} : BTree A :=
match p with
    | (empty, t2) => t2
    | (t1, empty) => t1
    | (node v l r as t1, node v' l' r' as t2) =>
        if v <=? v'
        then balance v l (merge (r, t2))
        else balance v' l' (merge (t1, r'))
end.
Proof.
  1-2: intros; cbn; omega.
Defined.

Arguments merge [x] _.

Definition insert {A : LinDec} (x : A) (t : BTree A) : BTree A :=
  merge (node x empty empty, t).

Definition findMin := @root.

Definition deleteMin {A : LinDec} (t : BTree A)
  : option A * BTree A :=
match t with
    | empty => (None, empty)
    | node v l r => (Some v, merge (l, r))
end.

Theorem findMin_spec :
  forall (A : LinDec) (h : BTree A) (m : A),
    is_heap h -> findMin h = Some m -> forall x : A, elem x h -> m ≤ x.
Proof.
  destruct h; cbn; do 3 inv 1.
Qed.

Theorem empty_spec :
  forall (A : LinDec) (x : A), ~ elem x empty.
Proof. inv 1. Qed.

Theorem singleton_spec :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  split; elem.
Qed.


Lemma balance_size :
  forall (A : Type) (v : A) (l r : BTree A),
    size (balance v l r) = size (node v l r).
Proof.
  intros. balance.
    trivial.
    apply size_swap.
Qed.

Lemma balance_elem :
  forall (A : Type) (x v : A) (l r : BTree A),
    elem x (balance v l r) <-> elem x (node v l r).
Proof.
  intros. balance.
    firstorder.
    split; inv 1.
Qed.

Theorem balance_is_heap :
  forall (A : LinDec) (v : A) (l r : BTree A),
    (forall x : A, elem x l -> v ≤ x) ->
    (forall x : A, elem x r -> v ≤ x) ->
    is_heap l -> is_heap r -> is_heap (balance v l r).
Proof.
  intros. balance; constructor; elem.
Qed.

Theorem balance_left_biased :
  forall (A : LinDec) (v : A) (l r : BTree A),
    left_biased l -> left_biased r ->
      left_biased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; dec.
Qed.

Lemma elem_merge :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x (merge (t1, t2)) -> elem x t1 \/ elem x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; try clear Heqp; auto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
Qed.

Lemma elem_merge_v2 :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x t1 \/ elem x t2 -> elem x (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. 
  functional induction @merge A p; inv Heqp; try clear Heqp;
  elem; rewrite balance_elem.
    inv H. apply elem_right.
      eapply IHb; try ((left + right); eauto); reflexivity.
    apply elem_right.
      eapply IHb; try ((left + right); eauto); reflexivity.
    apply elem_right.
      eapply IHb; try ((left + right); eauto); reflexivity.
    inv H. apply elem_right.
      eapply IHb; try ((left + right); eauto); reflexivity.
Qed.

Theorem merge_spec :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x (merge (t1, t2)) <-> elem x t1 \/ elem x t2.
Proof.
  split; intros. elem.
    apply elem_merge. assumption.
    apply elem_merge_v2. assumption.
Qed.

Arguments elem_merge [A x t1 t2] _.

Theorem merge_size :
  forall (A : LinDec) (t1 t2 : BTree A),
    size (merge (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; try clear Heqp.
    rewrite balance_size. cbn. rewrite (IHb r (node v' l' r') eq_refl).
      cbn. omega.
    rewrite balance_size. cbn. rewrite (IHb (node v l r) r' eq_refl).
      cbn. omega.
Qed.

Theorem merge_is_heap :
  forall (A : LinDec) (t1 t2 : BTree A),
    is_heap t1 -> is_heap t2 -> is_heap (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; try clear Heqp;
  inv H; inv H0; apply balance_is_heap; elem.
    destruct (leqb_spec v v'); inv e0. destruct (elem_merge H); auto.
      eapply leq_trans with v'. auto. inv H0.
    eapply (IHb _ _ _ _ eq_refl).
    destruct (leqb_spec v v'), (elem_merge H); inv e0.
      eapply leq_trans with v. dec. inv H0.
    eapply (IHb _ _ _ _ eq_refl).
Unshelve.
  all: auto.
Qed.

Theorem merge_left_biased :
  forall (A : LinDec) (t1 t2 : BTree A),
    left_biased t1 -> left_biased t2 -> left_biased (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; try clear Heqp;
  inv H; inv H0; cbn in *; apply balance_left_biased; auto.
    eapply (IHb _ _ _ _ eq_refl).
    eapply (IHb _ _ _ _ eq_refl).
Unshelve.
  all: eauto.
Qed.

Theorem insert_spec :
  forall (A : LinDec) (x y : A) (h : BTree A),
    is_heap h -> elem x (insert y h) <-> x = y \/ elem x h.
Proof.
  intros. unfold insert. rewrite merge_spec. split; inv 1.
    inv H1; inv H2.
Qed.



Theorem deleteMin_spec :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst; cbn.
  intros. destruct (elem_merge H0); auto.
Qed.

Theorem deleteMin_size :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite merge_size. trivial.
Qed.

Theorem deleteMin_elem :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Theorem deleteMin_is_heap :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      is_heap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply merge_is_heap; assumption.
Qed.

Theorem deleteMin_left_biased :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    left_biased t -> deleteMin t = (Some m, t') ->
      left_biased t'.
Proof.
  destruct t; cbn; do 2 inversion 1; subst.
  apply merge_left_biased; assumption.
Qed.