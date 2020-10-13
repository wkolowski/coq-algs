Require Export LinDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | N : nat -> A -> Tree A -> Tree A -> Tree A.

Arguments E {A}.
Arguments N {A} _ _ _ _.

Definition right_spine {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N r _ _ _ => r
end.

Definition balance
  {A : Type} (v : A) (l r : Tree A) : Tree A :=
    if right_spine r <=? right_spine l
    then N (1 + right_spine r) v l r
    else N (1 + right_spine l) v r l.

Require Import Recdef.

Fixpoint size
  {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N _ _ l r => 1 + size l + size r
end.

Definition sum_of_sizes
  {A : Type} (p : Tree A * Tree A) : nat :=
    size (fst p) + size (snd p).

Function merge
  {A : LinDec} (p : Tree A * Tree A) {measure sum_of_sizes p} : Tree A :=
match p with
    | (E, t2) => t2
    | (t1, E) => t1
    | (N _ v l r as t1, N _ v' l' r' as t2) =>
        if v <=? v'
        then balance v l (merge (r, t2))
        else balance v' l' (merge (t1, r'))
end.
Proof.
  1-2: intros; cbn; lia.
Defined.

Arguments merge [x] _.

Definition empty {A : LinDec} (x : A) : Tree A := E.

Definition isEmpty {A : Type} (t : Tree A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition singleton {A : Type} (x : A) : Tree A := N 1 x E E.

Definition insert {A : LinDec} (x : A) (t : Tree A) : Tree A :=
  merge (singleton x, t).

Definition findMin {A : Type} (t : Tree A) : option A :=
match t with
    | E => None
    | N _ v _ _ => Some v
end.

Definition deleteMin {A : LinDec} (t : Tree A) : option A * Tree A :=
match t with
    | E => (None, E)
    | N _ v l r => (Some v, merge (l, r))
end.

Definition unNode
  {A : LinDec} (t : Tree A) : option (A * Tree A) :=
match t with
    | E => None
    | N _ v l r => Some (v, merge (l, r))
end.

Inductive leftBiased {A : Type} : Tree A -> Prop :=
    | leftBiased_E : leftBiased E
    | leftBiased_N :
        forall (v : A) (l r : Tree A),
          right_spine r <= right_spine l ->
          leftBiased l -> leftBiased r ->
            leftBiased (N (1 + right_spine r) v l r).

Inductive elem {A : Type} (x : A) : Tree A -> Prop :=
    | elem_root :
        forall (n : nat) (l r : Tree A), elem x (N n x l r)
    | elem_l :
        forall (n : nat) (v : A) (l r : Tree A),
          elem x l -> elem x (N n v l r)
    | elem_r :
        forall (n : nat) (v : A) (l r : Tree A),
          elem x r -> elem x (N n v l r).

Inductive isHeap {A : LinDec} : Tree A -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall (v : A) (l r : Tree A),
          (forall x : A, elem x l -> v ≤ x) ->
          isHeap l ->
          (forall x : A, elem x r -> v ≤ x) ->
          isHeap r ->
            isHeap (N (1 + right_spine r) v l r).

Hint Constructors Tree leftBiased elem isHeap.

Ltac balance := unfold balance, id in *; intros;
match goal with
    | H : context [right_spine ?r <=? right_spine ?l] |- _ =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
    | |- context [right_spine ?r <=? right_spine ?l] =>
        destruct (@leqb_spec natle (right_spine r) (right_spine l))
end; cbn; try reflexivity.

Ltac elem :=
  intros **; unfold singleton, id in *; cbn in *; subst;
repeat
match goal with
    | |- elem ?x (N _ ?x _ _) => constructor
    | H:elem _ E |- _ => inv H
    | H:elem _ (N _ _ empty empty) |- _ => inv H
    | H:elem _ _ /\ elem _ _ |- _ => destruct H
    | H:elem _ _ \/ elem _ _ |- _ => destruct H
end; auto.

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : LinDec) (v : A) (l r : Tree A),
    isEmpty (balance v l r) = false.
Proof. balance. Qed.

Lemma isEmpty_merge :
  forall (A : LinDec) (t1 t2 : Tree A),
    isEmpty (merge (t1, t2)) = isEmpty t1 && isEmpty t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp.
    destruct t1; cbn; reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
Qed.

Lemma isEmpty_merge' :
  forall (A : LinDec) (t1 t2 : Tree A),
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
  forall (A : LinDec) (x : A) (t : Tree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_merge. cbn. reflexivity.
Qed.

Lemma isEmpty_unNode_false :
  forall (A : LinDec) (t : Tree A),
    isEmpty t = true <-> unNode t = None.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_unNode_true :
  forall (A : LinDec) (t : Tree A),
    isEmpty t = false <->
    exists (m : A) (t' : Tree A), unNode t = Some (m, t').
Proof.
  split; destruct t; cbn; intros; try congruence.
    eauto.
    firstorder congruence.
Qed.

Lemma isEmpty_leftBiased :
  forall (A : LinDec) (t : Tree A),
    isEmpty t = true -> leftBiased t.
Proof.
  destruct t; intro.
    constructor.
    cbn in H. congruence.
Qed.

(** Properties of [singleton]. *)

Lemma singleton_leftBiased :
  forall (A : LinDec) (x : A),
    leftBiased (singleton x).
Proof.
  intros. unfold singleton.
  apply (@leftBiased_N A x E E); auto.
Qed.

Lemma singleton_isHeap :
  forall (A : LinDec) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton. apply (@isHeap_N A x E E); auto; inv 1.
Defined.

(** Properties of [balance]. *)

Lemma balance_elem :
  forall (A : Type) (x v : A) (l r : Tree A),
    elem x (balance v l r) <-> elem x (N (1 + right_spine r) v l r).
Proof.
  intros. balance. firstorder (inv H).
Qed.

Lemma balance_isHeap :
  forall (A : LinDec) (v : A) (l r : Tree A),
    (forall x : A, elem x l -> v ≤ x) ->
    (forall x : A, elem x r -> v ≤ x) ->
    isHeap l -> isHeap r -> isHeap (balance v l r).
Proof.
  intros. balance; constructor; elem.
Qed.

Lemma balance_leftBiased :
  forall (A : LinDec) (v : A) (l r : Tree A),
    leftBiased l -> leftBiased r ->
      leftBiased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; dec.
Qed.

Lemma balance_size :
  forall (A : Type) (k : nat) (v : A) (l r : Tree A),
    size (balance v l r) = size (N k v l r).
Proof.
  intros. balance. rewrite plus_comm. reflexivity.
Qed.

Fixpoint count_Tree {A : Type} (p : A -> bool) (t : Tree A) : nat :=
match t with
    | E => 0
    | N _ v l r =>
        (if p v then S else id) (count_Tree p l + count_Tree p r)
end.

Lemma balance_count_Tree :
  forall (A : Type) (p : A -> bool) (k : nat) (v : A) (l r : Tree A),
    count_Tree p (balance v l r) = count_Tree p (N k v l r).
Proof.
  intros. balance; dec. rewrite plus_comm. reflexivity.
Qed.

(** Properties of [merge]. *)

Lemma merge_elem_lr :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    elem x (merge (t1, t2)) -> elem x t1 \/ elem x t2.
Proof.
  intros. remember (t1, t2) as p. revert x t1 t2 Heqp H.
  functional induction @merge A p; inv 1; intros.
    rewrite balance_elem in H. inv H. edestruct IHt; eauto.
    rewrite balance_elem in H. inv H. edestruct IHt; eauto.
Qed.

Lemma merge_elem_rl :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    elem x t1 \/ elem x t2 -> elem x (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert x t1 t2 Heqp H.
  functional induction @merge A p; inv 1; elem; rewrite balance_elem.
    inv H. apply elem_r.
      eapply IHt; try ((left + right); eauto); reflexivity.
    apply elem_r.
      eapply IHt; try ((left + right); eauto); reflexivity.
    apply elem_r.
      eapply IHt; try ((left + right); eauto); reflexivity.
    inv H. apply elem_r.
      eapply IHt; try ((left + right); eauto); reflexivity.
Qed.

Lemma merge_elem :
  forall (A : LinDec) (x : A) (t1 t2 : Tree A),
    elem x (merge (t1, t2)) <-> elem x t1 \/ elem x t2.
Proof.
  split; intros; remember (t1, t2) as p; revert x t1 t2 Heqp H;
    functional induction @merge A p; inv 1; elem;
      rewrite balance_elem in *; inv H; eauto; edestruct IHt; eauto.
Qed.

Arguments merge_elem_lr {A x t1 t2}.

Lemma merge_isHeap :
  forall (A : LinDec) (t1 t2 : Tree A),
    isHeap t1 -> isHeap t2 -> isHeap (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction @merge A p; do 3 inv 1;
  apply balance_isHeap; intros; try rewrite merge_elem in H; elem.
    2, 4: eapply (IHt _ _ eq_refl).
    all: destruct (leqb_spec v v'); inv e0.
      eapply leq_trans with v'; inv H.
      eapply leq_trans with v; inv H.
Qed.

Lemma merge_leftBiased :
  forall (A : LinDec) (t1 t2 : Tree A),
    leftBiased t1 -> leftBiased t2 -> leftBiased (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction @merge A p; inv 1; inv 1; inv 1;
  cbn in *; apply balance_leftBiased; auto.
    all: eapply (IHt _ _ eq_refl); eauto.
Qed.

Lemma merge_size :
  forall (A : LinDec) (t1 t2 : Tree A),
    size (merge (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    erewrite balance_size. cbn. rewrite (IHt r (N _ v' l' r') eq_refl).
      cbn. lia.
    erewrite balance_size. cbn. rewrite (IHt (N _ v l r) r' eq_refl).
      cbn. lia.
Unshelve.
  all: exact 0.
Qed.

Lemma merge_count_Tree :
  forall (A : LinDec) (f : A -> bool) (t1 t2 : Tree A),
    count_Tree f (merge (t1, t2)) = count_Tree f t1 + count_Tree f t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    erewrite balance_count_Tree. specialize (IHt _ _ eq_refl).
      cbn in *. rewrite IHt. unfold id. destruct (f v), (f v'); lia.
    erewrite balance_count_Tree. specialize (IHt _ _ eq_refl).
      cbn in *. rewrite IHt. unfold id. destruct (f v), (f v'); lia.
Unshelve.
  1-2: exact 0.
Qed.

Lemma findMin_spec :
  forall (A : LinDec) (h : Tree A) (m : A),
    isHeap h -> findMin h = Some m -> forall x : A, elem x h -> m ≤ x.
Proof.
  destruct h; cbn; do 3 inv 1.
Qed.

(** Properties of [insert]. *)

Lemma insert_elem :
  forall (A : LinDec) (x y : A) (h : Tree A),
    isHeap h -> elem x (insert y h) <-> x = y \/ elem x h.
Proof.
  intros. unfold insert. rewrite merge_elem. split; inv 1.
    inv H1; inv H2.
    left. compute. auto.
Qed.

Lemma insert_isHeap :
  forall (A : LinDec) (x : A) (t : Tree A),
    isHeap t -> isHeap (insert x t).
Proof.
  intros. unfold insert. apply merge_isHeap.
    apply singleton_isHeap.
    assumption.
Qed.

Lemma insert_leftBiased :
  forall (A : LinDec) (x : A) (t : Tree A),
    leftBiased t -> leftBiased (insert x t).
Proof.
  intros. unfold insert. apply merge_leftBiased; auto.
  apply singleton_leftBiased.
Qed.

Lemma insert_size :
  forall (A : LinDec) (x : A) (t : Tree A),
    size (insert x t) = 1 + size t.
Proof.
  intros. unfold insert. rewrite merge_size. cbn. reflexivity.
Qed.

Lemma insert_count_Tree :
  forall (A : LinDec) (p : A -> bool) (x : A) (t : Tree A),
    count_Tree p (insert x t) =
    (if p x then S else id) (count_Tree p t).
Proof.
  intros. unfold insert. rewrite merge_count_Tree. cbn.
  destruct (p x); reflexivity.
Qed.

(** Properties of [findMin], [deleteMin] and [unNode]. *)

Lemma deleteMin_elem :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    deleteMin t = (Some m, t') -> elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Lemma deleteMin_isHeap :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply merge_isHeap; assumption.
Qed.

Lemma deleteMin_leftBiased :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    leftBiased t -> deleteMin t = (Some m, t') ->
      leftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_leftBiased; assumption.
Qed.

Lemma deleteMin_size :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite merge_size. trivial.
Qed.

Lemma deleteMin_count_Tree :
  forall (A : LinDec) (p : A -> bool) (m : A) (t t' : Tree A),
    deleteMin t = (Some m, t') ->
      count_Tree p t = (if p m then S else id) (count_Tree p t').
Proof.
  destruct t; cbn; intros; inv H.
  dec; rewrite merge_count_Tree; reflexivity.
Qed.

Lemma deleteMin_spec :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (merge_elem_lr H); auto.
Qed.

(** Properties of [unNode]. *)

Lemma unNode_elem :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    unNode t = Some (m, t') -> elem m t.
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma unNode_isHeap :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    isHeap t -> unNode t = Some (m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_isHeap; assumption.
Qed.

Lemma unNode_leftBiased :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    leftBiased t -> unNode t = Some (m, t') ->
      leftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply merge_leftBiased; assumption.
Qed.

Lemma unNode_size :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    unNode t = Some (m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inv 1. rewrite merge_size. reflexivity.
Qed.

Lemma unNode_count_Tree :
  forall (A : LinDec) (p : A -> bool) (m : A) (t t' : Tree A),
    unNode t = Some (m, t') ->
      count_Tree p t = (if p m then S else id) (count_Tree p t').
Proof.
  destruct t; cbn; intros; inv H.
  dec; rewrite merge_count_Tree; reflexivity.
Qed.

Lemma unNode_spec :
  forall (A : LinDec) (m : A) (t t' : Tree A),
    isHeap t -> unNode t = Some (m, t') ->
      forall x : A, elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (merge_elem_lr H); auto.
Qed.

(** Leftist heapsort. *)

Fixpoint fromList {A : LinDec} (l : list A) : Tree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Function toList {A : LinDec} (t : Tree A) {measure size t} : list A :=
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

Lemma Sorted_toList :
  forall (A : LinDec) (t : Tree A),
    isHeap t -> Sorted A (toList t).
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

Lemma Sorted_leftistHeapsort :
  forall (A : LinDec) (l : list A),
    Sorted A (leftistHeapsort A l).
Proof.
  intros. unfold leftistHeapsort. apply Sorted_toList, fromList_isHeap.
Qed.

Lemma fromList_count_Tree :
  forall (A : LinDec) (p : A -> bool) (l : list A),
    count_Tree p (fromList l) = count p l.
Proof.
  induction l as [| h t]; cbn; dec;
  rewrite insert_count_Tree, IHt.
  destruct (p h); reflexivity.
Qed.

Lemma toList_count_Tree :
  forall (A : LinDec) (p : A -> bool) (t : Tree A),
    count p (toList t) = count_Tree p t.
Proof.
  intros. functional induction @toList A t.
    destruct t; inv e.
    destruct t; inv e. cbn.
      rewrite IHl, merge_count_Tree. destruct (p m); reflexivity.
Qed.

Lemma leftistHeapsort_perm :
  forall (A : LinDec) (l : list A),
    perm l (leftistHeapsort A l).
Proof.
  unfold perm, leftistHeapsort. intros.
  rewrite toList_count_Tree, fromList_count_Tree. reflexivity.
Qed.

Lemma Permutation_leftistHeapsort :
  forall (A : LinDec) (l : list A),
    Permutation (leftistHeapsort A l) l.
Proof.
  intros. apply perm_Permutation. rewrite <- leftistHeapsort_perm.
  reflexivity.
Qed.

#[refine]
Instance Sort_leftistHeapsort (A : LinDec) : Sort A :=
{
    sort := @leftistHeapsort A;
}.
Proof.
  all: intros.
    apply Sorted_leftistHeapsort.
    apply Permutation_leftistHeapsort.
Defined.

Definition leftistHeapsort3 (A : LinDec) (l : list A) : list A :=
  leftistHeapsort A l.