Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Import BST.

Require Export LinDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

(* TODO: refactor *) Fixpoint right_spine {A : Type} (t : BTree A) : nat :=
match t with
    | empty => 0
    | node _ _ r => S (right_spine r)
end.

Inductive leftBiased {A : LinDec} : BTree A -> Prop :=
    | leftBiased_empty : leftBiased empty
    | leftBiased_node :
        forall (v : A) (l r : BTree A),
          right_spine r <= right_spine l ->
          leftBiased l -> leftBiased r ->
            leftBiased (node v l r).

Hint Constructors BTree leftBiased.

Definition balance {A : Type} (v : A) (l r : BTree A) : BTree A :=
  if right_spine r <=? right_spine l
  then node v l r
  else node v r l.

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

Definition deleteMin {A : LinDec} (t : BTree A) : option A * BTree A :=
match t with
    | empty => (None, empty)
    | node v l r => (Some v, merge (l, r))
end.

Definition unNode
  {A : LinDec} (t : BTree A) : option (A * BTree A) :=
match t with
    | empty => None
    | node v l r => Some (v, merge (l, r))
end.

Ltac balance := unfold balance in *;
match goal with
    | H : context [right_spine ?r <=? right_spine ?l] |- _ =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
    | |- context [right_spine ?r <=? right_spine ?l] =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
end.

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : LinDec) (v : A) (l r : BTree A),
    isEmpty (balance v l r) = false.
Proof.
  intros. unfold balance.
  match goal with
      | |- context [if ?x then _ else _] => destruct x
  end;
  cbn; reflexivity.
Qed.

Lemma isEmpty_merge :
  forall (A : LinDec) (t1 t2 : BTree A),
    isEmpty (merge (t1, t2)) = isEmpty t1 && isEmpty t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp.
    destruct t1; cbn; reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
Qed.

Lemma isEmpty_merge' :
  forall (A : LinDec) (t1 t2 : BTree A),
    isEmpty (merge (t1, t2)) = true <->
    isEmpty t1 = true /\ isEmpty t2 = true.
Proof.
  intros. remember (t1, t2) as p. split; intros.
    functional induction @merge A p; inv Heqp;
      rewrite isEmpty_balance in H; congruence.
    functional induction @merge A p; inv Heqp; cbn in *;
      destruct H; congruence.
Qed.

Lemma isEmpty_insert :
  forall (A : LinDec) (x : A) (t : BTree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_merge. cbn. reflexivity.
Qed.

Lemma isEmpty_unNode_false :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true <-> unNode t = None.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_unNode_true :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = false <->
    exists (m : A) (t' : BTree A), unNode t = Some (m, t').
Proof.
  split; destruct t; cbn; intros; try congruence.
    eauto.
    firstorder congruence.
Qed.

Lemma isEmpty_leftBiased :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true -> leftBiased t.
Proof.
  destruct t; firstorder.
Qed.

(** Properties of [singleton]. *)

Lemma singleton_leftBiased :
  forall (A : LinDec) (x : A),
    leftBiased (singleton x).
Proof.
  intros. unfold singleton. auto.
Qed.

(** Properties of [balance]. *)

Lemma balance_elem :
  forall (A : Type) (x v : A) (l r : BTree A),
    elem x (balance v l r) <-> elem x (node v l r).
Proof.
  intros. balance.
    firstorder.
    split; inv 1.
Qed.

Lemma balance_isHeap :
  forall (A : LinDec) (v : A) (l r : BTree A),
    (forall x : A, elem x l -> v ≤ x) ->
    (forall x : A, elem x r -> v ≤ x) ->
    isHeap l -> isHeap r -> isHeap (balance v l r).
Proof.
  intros. balance; constructor; elem.
Qed.

Lemma balance_leftBiased :
  forall (A : LinDec) (v : A) (l r : BTree A),
    leftBiased l -> leftBiased r ->
      leftBiased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; dec.
Qed.

Lemma balance_size :
  forall (A : Type) (v : A) (l r : BTree A),
    size (balance v l r) = size (node v l r).
Proof.
  intros. balance.
    trivial.
    apply size_swap.
Qed.

Lemma balance_count_BTree :
  forall (A : LinDec) (x v : A) (l r : BTree A),
    count_BTree x (balance v l r) = count_BTree x (node v l r).
Proof.
  intros. balance; dec.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem_lr :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x (merge (t1, t2)) -> elem x t1 \/ elem x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; try clear Heqp; auto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
    rewrite balance_elem in H. inv H. edestruct IHb; eauto.
Qed.

Lemma merge_elem_rl :
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

Lemma merge_elem :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    elem x (merge (t1, t2)) <-> elem x t1 \/ elem x t2.
Proof.
  split; intros; remember (t1, t2) as p;
    functional induction @merge A p; inv Heqp; elem;
      rewrite balance_elem in *; inv H; eauto; edestruct IHb; eauto.
Qed.

Arguments merge_elem_lr {A x t1 t2}.

Lemma merge_isHeap :
  forall (A : LinDec) (t1 t2 : BTree A),
    isHeap t1 -> isHeap t2 -> isHeap (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; inv H; inv H0;
  apply balance_isHeap; intros; try rewrite merge_elem in H; elem.
    2, 4: eapply (IHb _ _ _ _ eq_refl).
    all: destruct (leqb_spec v v'); inv e0.
      eapply leq_trans with v'; inv H.
      eapply leq_trans with v; inv H.
Unshelve.
  all: auto.
Qed.

Lemma merge_leftBiased :
  forall (A : LinDec) (t1 t2 : BTree A),
    leftBiased t1 -> leftBiased t2 -> leftBiased (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp; inv H; inv H0;
  cbn in *; apply balance_leftBiased; auto.
    all: eapply (IHb _ _ _ _ eq_refl).
Unshelve.
  all: eauto.
Qed.

Lemma merge_size :
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

Lemma merge_count_BTree :
  forall (A : LinDec) (x : A) (t1 t2 : BTree A),
    count_BTree x (merge (t1, t2)) = count_BTree x t1 + count_BTree x t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp.
    rewrite balance_count_BTree. specialize (IHb x _ _ eq_refl).
      cbn in *. dec.
    rewrite balance_count_BTree. specialize (IHb x _ _ eq_refl).
      cbn in *. dec.
Qed.

Lemma findMin_spec :
  forall (A : LinDec) (h : BTree A) (m : A),
    isHeap h -> findMin h = Some m -> forall x : A, elem x h -> m ≤ x.
Proof.
  destruct h; cbn; do 3 inv 1.
Qed.

(** Properties of [insert]. *)

Lemma insert_elem :
  forall (A : LinDec) (x y : A) (h : BTree A),
    isHeap h -> elem x (insert y h) <-> x = y \/ elem x h.
Proof.
  intros. unfold insert. rewrite merge_elem. split; inv 1.
    inv H1; inv H2.
Qed.

Lemma insert_isHeap :
  forall (A : LinDec) (x : A) (t : BTree A),
    isHeap t -> isHeap (insert x t).
Proof.
  intros. unfold insert. apply merge_isHeap.
    constructor; auto; inv 1.
    assumption.
Qed.

Lemma insert_leftBiased :
  forall (A : LinDec) (x : A) (t : BTree A),
    leftBiased t -> leftBiased (insert x t).
Proof.
  intros. unfold insert. apply merge_leftBiased; auto.
Qed.

Lemma insert_size :
  forall (A : LinDec) (x : A) (t : BTree A),
    size (insert x t) = 1 + size t.
Proof.
  intros. unfold insert. rewrite merge_size. cbn. reflexivity.
Qed.

Lemma insert_count_BTree :
  forall (A : LinDec) (x y : A) (t : BTree A),
    count_BTree x (insert y t) =
    (if x =? y then S else id) (count_BTree x t).
Proof.
  intros. unfold insert. rewrite merge_count_BTree. dec.
Qed.

(** Properties of [findMin], [deleteMin] and [unNode]. *)

Lemma deleteMin_elem :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Lemma deleteMin_isHeap :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply merge_isHeap; assumption.
Qed.

Lemma deleteMin_leftBiased :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    leftBiased t -> deleteMin t = (Some m, t') ->
      leftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_leftBiased; assumption.
Qed.

Lemma deleteMin_size :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite merge_size. trivial.
Qed.

Lemma deleteMin_count_BTree :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    deleteMin t = (Some m, t') ->
      count_BTree x t = (if x =? m then S else id) (count_BTree x t').
Proof.
  destruct t; cbn; intros; inv H.
  dec; rewrite merge_count_BTree; reflexivity.
Qed.

Lemma deleteMin_spec :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (merge_elem_lr H); auto.
Qed.

(** Properties of [unNode]. *)

Lemma unNode_elem :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    unNode t = Some (m, t') -> elem m t.
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma unNode_isHeap :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    isHeap t -> unNode t = Some (m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_isHeap; assumption.
Qed.

Lemma unNode_leftBiased :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    leftBiased t -> unNode t = Some (m, t') ->
      leftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_leftBiased; assumption.
Qed.

Lemma unNode_size :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    unNode t = Some (m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inv 1. rewrite merge_size. reflexivity.
Qed.

Lemma unNode_count_BTree :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    unNode t = Some (m, t') ->
      count_BTree x t = (if x =? m then S else id) (count_BTree x t').
Proof.
  destruct t; cbn; intros; inv H.
  dec; rewrite merge_count_BTree; reflexivity.
Qed.

Lemma unNode_spec :
  forall (A : LinDec) (m : A) (t t' : BTree A),
    isHeap t -> unNode t = Some (m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (merge_elem_lr H); auto.
Qed.

(** Leftist heapsort. *)

Fixpoint fromList {A : LinDec} (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert h (fromList t)
end.

Function toList {A : LinDec} (t : BTree A) {measure size t} : list A :=
match unNode t with
    | None => []
    | Some (m, t') => m :: toList t'
end.
Proof.
  intros. destruct t; cbn; inv teq.
  rewrite merge_size. auto.
Defined.

Arguments toList {x} _.

Definition leftistHeapsort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Lemma toList_sorted :
  forall (A : LinDec) (t : BTree A),
    isHeap t -> sorted A (toList t).
Proof.
  intros. functional induction @toList A t.
    constructor.
    rewrite toList_equation in *. destruct t'; cbn in *; constructor.
      eapply unNode_spec; eauto.
      eapply IHl, unNode_isHeap; eauto.
Qed.

Lemma fromList_isHeap :
  forall (A : LinDec) (l : list A),
    isHeap (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply insert_isHeap. assumption.
Qed.

Lemma leftistHeapsort_sorted :
  forall (A : LinDec) (l : list A),
    sorted A (leftistHeapsort A l).
Proof.
  intros. unfold leftistHeapsort. apply toList_sorted, fromList_isHeap.
Qed.

Lemma fromList_count_BTree :
  forall (A : LinDec) (x : A) (l : list A),
    count_BTree x (fromList l) = count A x l.
Proof.
  induction l as [| h t]; cbn; dec;
  rewrite insert_count_BTree; dec.
Qed.

Lemma toList_count_BTree :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (toList t) = count_BTree x t.
Proof.
  intros. functional induction @toList A t.
    destruct t; inv e.
    destruct t; inv e. cbn. dec;
      rewrite IHl, merge_count_BTree; reflexivity.
Qed.

Lemma leftistHeapsort_perm :
  forall (A : LinDec) (l : list A),
    perm A l (leftistHeapsort A l).
Proof.
  unfold perm, leftistHeapsort. intros.
  rewrite toList_count_BTree, fromList_count_BTree. reflexivity.
Qed.

Instance Sort_leftistHeapsort (A : LinDec) : Sort A :=
{
    sort := @leftistHeapsort A;
}.
Proof.
  all: intros.
    apply leftistHeapsort_sorted.
    apply leftistHeapsort_perm.
Defined.