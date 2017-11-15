Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

Inductive RSTree (A : Type) : Type :=
    | empty : RSTree A
    | node : nat -> A -> RSTree A -> RSTree A -> RSTree A.

Arguments empty [A].
Arguments node [A] _ _ _.

Definition right_spine {A : Type} (t : RSTree A) : nat :=
match t with
    | empty => 0
    | node n _ _ _ => n
end.

Inductive elem {A : Type} (x : A) : RSTree A -> Prop :=
    | elem_root : forall (n : nat) (l r : RSTree A),
        elem x (node n x l r)
    | elem_left : forall (n : nat) (v : A) (l r : RSTree A),
        elem x l -> elem x (node n v l r)
    | elem_right : forall  (n : nat) (v : A) (l r : RSTree A),
        elem x r -> elem x (node n v l r).

Inductive is_heap {A : LinDec} : RSTree A -> Prop :=
    | is_heap_empty : is_heap empty
    | is_heap_node :
        forall  (n : nat) (v : A) (l : RSTree A) (r : RSTree A),
          (forall x : A, elem x l -> v ≤ x) -> is_heap l ->
          (forall x : A, elem x r -> v ≤ x) -> is_heap r ->
            is_heap (node n v l r).

Lemma is_heap_inv_l :
  forall (A : LinDec) (n : nat) (v : A) (l r : RSTree A),
    is_heap (node n v l r) -> is_heap l.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_heap_inv_r :
  forall (A : LinDec) (n : nat) (v : A) (l r : RSTree A),
    is_heap (node n v l r) -> is_heap r.
Proof.
  inversion 1; eauto.
Qed.

Lemma is_heap_inv_leq :
  forall (A : LinDec) (n : nat) (v : A) (l r : RSTree A),
    is_heap (node n v l r) -> forall x : A,
      elem x (node n v l r) -> v ≤ x.
Proof.
  do 2 inversion 1; subst; auto.
Qed.

Hint Resolve is_heap_inv_l is_heap_inv_r.

Inductive left_biased {A : LinDec} : RSTree A -> Prop :=
    | left_biased_empty : left_biased empty
    | left_biased_node :
        forall (v : A) (l r : RSTree A),
          right_spine r <= right_spine l ->
          left_biased l -> left_biased r ->
            left_biased (node (S (right_spine r)) v l r).

Hint Constructors RSTree elem is_heap left_biased.

Ltac lh x :=
  let t := fresh "t" in
  let H := fresh "H" in
  let H' := fresh "H" in
    destruct x as [t H H']; destruct t;
    try inversion H; try inversion H'; subst; cbn.

Ltac inv x := inversion x; subst; auto.

Definition getMin {A : LinDec} (t : RSTree A) : option A :=
match t with
    | empty => None
    | node _ v _ _ => Some v
end.

(*Theorem getMin_spec :
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
Qed.*)

Definition singleton' {A : Type} (x : A)
  : RSTree A := node 1 x empty empty.

(*Definition singleton {A : LinDec} (x : A) : LeftistHeap A.
Proof.
  split with (tree := singleton' x);
  constructor; auto; inversion 1.
Defined.*)

Ltac elem :=
  intros; unfold singleton' in *; cbn in *; subst; repeat
match goal with
    | |- elem ?x (node ?x _ _) => constructor
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ empty empty) |- _ => inv H
    | H : elem _ _ /\ elem _ _ |- _ => destruct H
    | H : elem _ _ \/ elem _ _ |- _ => destruct H
end; auto.

(*Theorem singleton_spec :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  split; elem.
Qed.*)

Definition balance {A : Type} (v : A) (l r : RSTree A) : RSTree A :=
  if right_spine r <=? right_spine l
  then node (S (right_spine r)) v l r
  else node (S (right_spine l)) v r l.

Ltac balance := unfold balance in *;
match goal with
    | H : context [right_spine ?r <=? right_spine ?l] |- _ =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
    | |- context [right_spine ?r <=? right_spine ?l] =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
end.

Fixpoint size {A : Type} (t : RSTree A) : nat :=
match t with
    | empty => 0
    | node _ _ l r => S (size l + size r)
end.

Lemma size_swap :
  forall (A : Type) (n : nat) (v : A) (l r : RSTree A),
    size (node n v r l) = size (node n v l r).
Proof.
  intros. cbn. omega.
Qed.

Lemma balance_size:
  forall (A : Type) (n : nat) (v : A) (l r : RSTree A),
    size (balance v l r) = size (node n v l r).
Proof.
  intros. balance.
    trivial.
    cbn. omega.
Qed.

Lemma balance_elem :
  forall (A : Type) (n : nat) (x v : A) (l r : RSTree A),
    elem x (balance v l r) <-> elem x (node n v l r).
Proof.
  intros. balance; split; intro; inv H.
Qed.

Theorem balance_is_heap :
  forall (A : LinDec) (n : nat) (v : A) (l r : RSTree A),
    (forall x : A, elem x l -> v ≤ x) ->
    (forall x : A, elem x r -> v ≤ x) ->
      is_heap l -> is_heap r -> is_heap (balance v l r).
Proof.
  intros; balance; constructor; elem.
Qed.

Theorem balance_left_biased :
  forall (A : LinDec) (n : nat) (v : A) (l r : RSTree A),
    left_biased l -> left_biased r ->
      left_biased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; dec.
Qed.

Require Import Recdef.

Definition sum_of_sizes {A : Type} (p : RSTree A * RSTree A) : nat :=
  size (fst p) + size (snd p).

Function merge' {A : LinDec} (p : RSTree A * RSTree A)
  {measure sum_of_sizes p} : RSTree A :=
match p with
    | (empty, t2) => t2
    | (t1, empty) => t1
    | (node _ v l r as t1, node _ v' l' r' as t2) =>
        if v <=? v'
        then balance v l (merge' (r, t2))
        else balance v' l' (merge' (t1, r'))
end.
Proof.
  1-2: intros; cbn; omega.
Defined.

Arguments merge' [x] _.

Lemma elem_merge' :
  forall (A : LinDec) (x : A) (t1 t2 : RSTree A),
    elem x (merge' (t1, t2)) -> elem x t1 \/ elem x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp; auto.
    rewrite balance_elem in H. inv H. edestruct IHr; eauto.
    rewrite balance_elem in H. inv H. edestruct IHr; eauto.
    Unshelve. all: auto.
Qed.

Lemma elem_merge'_v2 :
  forall (A : LinDec) (x : A) (t1 t2 : RSTree A),
    elem x t1 \/ elem x t2 -> elem x (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp;
  elem; rewrite balance_elem.
    inv H. apply elem_right.
      eapply IHr; try ((left + right); eauto); reflexivity.
    apply elem_right.
      eapply IHr; try ((left + right); eauto); reflexivity.
    apply elem_right.
      eapply IHr; try ((left + right); eauto); reflexivity.
    inv H. apply elem_right.
      eapply IHr; try ((left + right); eauto); reflexivity.
    Unshelve. all: auto.
Qed.

Theorem merge'_spec :
  forall (A : LinDec) (x : A) (t1 t2 : RSTree A),
    elem x (merge' (t1, t2)) <-> elem x t1 \/ elem x t2.
Proof.
  split; intros. elem.
    apply elem_merge'. assumption.
    apply elem_merge'_v2. assumption.
Qed.

Arguments elem_merge' [A x t1 t2] _.

Theorem merge'_size:
  forall (A : LinDec) (t1 t2 : RSTree A),
    size (merge' (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp.
    erewrite balance_size. cbn. rewrite (IHr r (node _ v' l' r') eq_refl).
      cbn. omega.
    erewrite balance_size. cbn. rewrite (IHr (node _ v l r) r' eq_refl).
      cbn. omega.
    Unshelve. all: auto.
Qed.

Theorem merge'_is_heap :
  forall (A : LinDec) (t1 t2 : RSTree A),
    is_heap t1 -> is_heap t2 -> is_heap (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp;
  inv H; inv H0; apply balance_is_heap; elem.
    destruct (leqb_spec v v'); inv e0. destruct (elem_merge' H1); auto.
      eapply leq_trans with v'. auto. inv H2.
    apply (IHr _ _ H8 H0 eq_refl).
    destruct (leqb_spec v v'), (elem_merge' H1); inv e0.
      eapply leq_trans with v. dec. inv H2.
    apply (IHr _ _ H H12 eq_refl).
Qed.

Theorem merge'_left_biased :
  forall (A : LinDec) (t1 t2 : RSTree A),
    left_biased t1 -> left_biased t2 -> left_biased (merge' (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge' A p; inv Heqp; clear Heqp;
  inv H; inv H0; cbn in *; apply balance_left_biased; auto.
    exact 0.
    apply (IHr _ _ H7 H0 eq_refl).
    exact 0.
    apply (IHr _ _ H H10 eq_refl).
Qed.

(*Definition merge {A : LinDec} (h1 h2 : LeftistHeap A)
  : LeftistHeap A.
Proof.
  destruct h1 as [t1 H11 H12], h2 as [t2 H21 H22].
  split with (tree := @merge' A (t1, t2)).
  apply merge'_is_heap; assumption.
  apply merge'_left_biased; assumption.
Defined.*)

Definition insert' {A : LinDec} (x : A) (t : RSTree A) : RSTree A :=
  merge' ((singleton' x), t).

(* TODO *)
(*Definition insert {A : LinDec} (x : A) (h : LeftistHeap A)
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
    destruct H; subst; apply elem_merge'_v2; elem.
Qed.*)

Definition deleteMin {A : LinDec} (t : RSTree A)
  : option A * RSTree A :=
match t with
    | empty => (None, empty)
    | node _ v l r => (Some v, merge' (l, r))
end.

Theorem deleteMin_spec :
  forall (A : LinDec) (m : A) (t t' : RSTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst; cbn.
  intros. destruct (elem_merge' H0); auto.
Qed.

Theorem deleteMin_size:
  forall (A : LinDec) (m : A) (t t' : RSTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite merge'_size. trivial.
Qed.

Theorem deleteMin_elem :
  forall (A : LinDec) (m : A) (t t' : RSTree A),
    deleteMin t = (Some m, t') -> elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Theorem deleteMin_is_heap :
  forall (A : LinDec) (m : A) (t t' : RSTree A),
    is_heap t -> deleteMin t = (Some m, t') ->
      is_heap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply merge'_is_heap; assumption.
Qed.

Theorem deleteMin_left_biased :
  forall (A : LinDec) (m : A) (t t' : RSTree A),
    left_biased t -> deleteMin t = (Some m, t') ->
      left_biased t'.
Proof.
  destruct t; cbn; do 2 inversion 1; subst.
  apply merge'_left_biased; assumption.
Qed.

(* Leftist heapsort *)
Function fromList {A : LinDec} (l : list A) : RSTree A :=
match l with
    | [] => empty
    | h :: t => insert' h (fromList t)
end.

Function toList {A : LinDec} (t : RSTree A)
  {measure size t} : list A :=
match deleteMin t with
    | (None, _) => []
    | (Some m, t') => m :: toList t'
end.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  rewrite merge'_size. omega.
Defined.

Arguments toList [x] _.

Definition leftistHeapsort (A : LinDec) (l : list A)
  : list A := toList (fromList l).

Require Import ListLemmas.

Time Compute leftistHeapsort natle (cycle 25 testl).