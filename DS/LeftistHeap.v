Require Export TrichDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

Inductive LTree (A : Type) : Type :=
    | E : LTree A
    | N : nat -> A -> LTree A -> LTree A -> LTree A.

Arguments E {A}.
Arguments N {A} _ _ _ _.

Definition right_spine {A : Type} (t : LTree A) : nat :=
match t with
    | E => 0
    | N r _ _ _ => r
end.

Definition balance
  {A : Type} (v : A) (l r : LTree A) : LTree A :=
    if right_spine r ≤? right_spine l
    then N (1 + right_spine r) v l r
    else N (1 + right_spine l) v r l.

Require Import Recdef.

Fixpoint size
  {A : Type} (t : LTree A) : nat :=
match t with
    | E => 0
    | N _ _ l r => 1 + size l + size r
end.

Definition sum_of_sizes
  {A : Type} (p : LTree A * LTree A) : nat :=
    size (fst p) + size (snd p).

Function merge
  {A : TrichDec} (p : LTree A * LTree A) {measure sum_of_sizes p} : LTree A :=
match p with
    | (E, t2) => t2
    | (t1, E) => t1
    | (N _ v l r as t1, N _ v' l' r' as t2) =>
        if v ≤? v'
        then balance v l (merge (r, t2))
        else balance v' l' (merge (t1, r'))
end.
Proof.
  1-2: intros; cbn; lia.
Defined.

Arguments merge [x] _.

Definition empty {A : TrichDec} (x : A) : LTree A := E.

Definition isEmpty {A : Type} (t : LTree A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition singleton {A : Type} (x : A) : LTree A := N 1 x E E.

Definition insert {A : TrichDec} (x : A) (t : LTree A) : LTree A :=
  merge (singleton x, t).

Definition findMin {A : Type} (t : LTree A) : option A :=
match t with
    | E => None
    | N _ v _ _ => Some v
end.

Definition deleteMin {A : TrichDec} (t : LTree A) : option A * LTree A :=
match t with
    | E => (None, E)
    | N _ v l r => (Some v, merge (l, r))
end.

Definition extractMin
  {A : TrichDec} (t : LTree A) : option (A * LTree A) :=
match t with
    | E => None
    | N _ v l r => Some (v, merge (l, r))
end.

Inductive LeftBiased {A : Type} : LTree A -> Prop :=
    | LeftBiased_E : LeftBiased E
    | LeftBiased_N :
        forall (v : A) (l r : LTree A),
          right_spine r <= right_spine l ->
          LeftBiased l -> LeftBiased r ->
            LeftBiased (N (1 + right_spine r) v l r).

Inductive Elem {A : Type} (x : A) : LTree A -> Prop :=
    | Elem_root :
        forall (n : nat) (l r : LTree A), Elem x (N n x l r)
    | Elem_l :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x l -> Elem x (N n v l r)
    | Elem_r :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x r -> Elem x (N n v l r).

Inductive isHeap {A : TrichDec} : LTree A -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall (v : A) (l r : LTree A),
          (forall x : A, Elem x l -> v ≤ x) ->
          isHeap l ->
          (forall x : A, Elem x r -> v ≤ x) ->
          isHeap r ->
            isHeap (N (1 + right_spine r) v l r).

Hint Constructors LTree LeftBiased Elem isHeap : core.

Ltac balance := unfold balance, id in *; intros;
match goal with
    | H : context [right_spine ?r ≤? right_spine ?l] |- _ =>
        destruct (@trich_leb_spec natlt (right_spine r) (right_spine l))
    | |- context [right_spine ?r ≤? right_spine ?l] =>
        destruct (@trich_leb_spec natlt (right_spine r) (right_spine l))
end; cbn; try reflexivity.

Ltac elem :=
  intros **; unfold singleton, id in *; cbn in *; subst;
repeat
match goal with
    | |- Elem ?x (N _ ?x _ _) => constructor
    | H : Elem _ E |- _ => inv H
    | H : Elem _ (N _ _ empty empty) |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : Elem _ _ \/ Elem _ _ |- _ => destruct H
    | H1 : forall _, Elem _ _ -> _,
      H2 : Elem _ _ |- _ => specialize (H1 _ H2)
end; auto.

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : TrichDec) (v : A) (l r : LTree A),
    isEmpty (balance v l r) = false.
Proof. balance. Qed.

Lemma isEmpty_merge :
  forall (A : TrichDec) (t1 t2 : LTree A),
    isEmpty (merge (t1, t2)) = isEmpty t1 && isEmpty t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp.
    destruct t1; cbn; reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
Qed.

Lemma isEmpty_merge' :
  forall (A : TrichDec) (t1 t2 : LTree A),
    isEmpty (merge (t1, t2)) = true
      <->
    isEmpty t1 = true /\ isEmpty t2 = true.
Proof.
  intros. remember (t1, t2) as p. split; intros.
    functional induction @merge A p; inv Heqp;
      rewrite isEmpty_balance in H; congruence.
    functional induction @merge A p; inv Heqp; cbn in *;
      destruct H; congruence.
Qed.

Lemma isEmpty_insert :
  forall (A : TrichDec) (x : A) (t : LTree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_merge. cbn. reflexivity.
Qed.

Lemma isEmpty_extractMin_false :
  forall (A : TrichDec) (t : LTree A),
    isEmpty t = true <-> extractMin t = None.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_extractMin_true :
  forall (A : TrichDec) (t : LTree A),
    isEmpty t = false <->
    exists (m : A) (t' : LTree A), extractMin t = Some (m, t').
Proof.
  split; destruct t; cbn; intros; try congruence.
    eauto.
    firstorder congruence.
Qed.

Lemma LeftBiased_isEmpty :
  forall (A : TrichDec) (t : LTree A),
    isEmpty t = true -> LeftBiased t.
Proof.
  destruct t; intro.
    constructor.
    cbn in H. congruence.
Qed.

(** Properties of [singleton]. *)

Lemma LeftBiased_singleton :
  forall (A : TrichDec) (x : A),
    LeftBiased (singleton x).
Proof.
  intros. unfold singleton.
  apply (@LeftBiased_N A x E E); auto.
Qed.

Lemma isHeap_singleton :
  forall (A : TrichDec) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton. apply (@isHeap_N A x E E); auto; inv 1.
Defined.

(** Properties of [balance]. *)

Lemma Elem_N :
  forall {A : Type} (x : A) (n : nat) (v : A) (l r : LTree A),
    Elem x (N n v l r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  intros. split; inv 1. inv H0.
Qed.

Lemma Elem_balance :
  forall (A : Type) (x v : A) (l r : LTree A),
    Elem x (balance v l r) <-> Elem x (N (1 + right_spine r) v l r).
Proof.
  intros. balance. rewrite ?Elem_N. firstorder.
Qed.

Lemma isHeap_balance :
  forall (A : TrichDec) (v : A) (l r : LTree A),
    (forall x : A, Elem x l -> v ≤ x) ->
    (forall x : A, Elem x r -> v ≤ x) ->
    isHeap l -> isHeap r -> isHeap (balance v l r).
Proof.
  intros. balance; constructor; elem.
Qed.

Lemma LeftBiased_balance :
  forall (A : TrichDec) (v : A) (l r : LTree A),
    LeftBiased l -> LeftBiased r ->
      LeftBiased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; trich.
    rewrite <- trich_le_nf in H1. destruct H1; cbn in *; lia.
    cbn in H1. lia.
Qed.

Lemma size_balance :
  forall (A : Type) (k : nat) (v : A) (l r : LTree A),
    size (balance v l r) = size (N k v l r).
Proof.
  intros. balance. rewrite plus_comm. reflexivity.
Qed.

Fixpoint countLT {A : Type} (p : A -> bool) (t : LTree A) : nat :=
match t with
    | E => 0
    | N _ v l r =>
        (if p v then S else id) (countLT p l + countLT p r)
end.

Lemma countLT_balance :
  forall (A : Type) (p : A -> bool) (k : nat) (v : A) (l r : LTree A),
    countLT p (balance v l r) = countLT p (N k v l r).
Proof.
  intros. balance; trich. rewrite plus_comm. reflexivity.
Qed.

(** Properties of [merge]. *)

Lemma Elem_merge_conv :
  forall (A : TrichDec) (x : A) (t1 t2 : LTree A),
    Elem x (merge (t1, t2)) -> Elem x t1 \/ Elem x t2.
Proof.
  intros. remember (t1, t2) as p. revert x t1 t2 Heqp H.
  functional induction @merge A p; inv 1; intros.
    rewrite Elem_balance in H. inv H. edestruct IHl; eauto.
    rewrite Elem_balance in H. inv H. edestruct IHl; eauto.
Qed.

Lemma Elem_merge :
  forall (A : TrichDec) (x : A) (t1 t2 : LTree A),
    Elem x t1 \/ Elem x t2 -> Elem x (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert x t1 t2 Heqp H.
  functional induction @merge A p; inv 1; elem; rewrite Elem_balance.
    inv H. apply Elem_r.
      eapply IHl; try ((left + right); eauto); reflexivity.
    apply Elem_r.
      eapply IHl; try ((left + right); eauto); reflexivity.
    apply Elem_r.
      eapply IHl; try ((left + right); eauto); reflexivity.
    inv H. apply Elem_r.
      eapply IHl; try ((left + right); eauto); reflexivity.
Qed.

Lemma Elem_merge' :
  forall (A : TrichDec) (x : A) (t1 t2 : LTree A),
    Elem x (merge (t1, t2)) <-> Elem x t1 \/ Elem x t2.
Proof.
  split; intros; remember (t1, t2) as p; revert x t1 t2 Heqp H;
    functional induction @merge A p; inv 1; elem;
      rewrite Elem_balance in *; inv H; eauto; edestruct IHl; eauto.
Qed.

Arguments Elem_merge_conv {A x t1 t2}.

Lemma isHeap_merge :
  forall (A : TrichDec) (t1 t2 : LTree A),
    isHeap t1 -> isHeap t2 -> isHeap (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction merge p;
  do 3 inv 1; apply isHeap_balance;
  intros; rewrite ?Elem_merge' in *; elem; eauto.
    inv H; elem; trich.
    inv H; elem; trich.
Qed.

Lemma LeftBiased_merge :
  forall (A : TrichDec) (t1 t2 : LTree A),
    LeftBiased t1 -> LeftBiased t2 -> LeftBiased (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction @merge A p; inv 1; inv 1; inv 1;
  cbn in *; apply LeftBiased_balance; auto.
    all: eapply (IHl _ _ eq_refl); eauto.
Qed.

Lemma size_merge :
  forall (A : TrichDec) (t1 t2 : LTree A),
    size (merge (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    erewrite size_balance. cbn. rewrite (IHl r (N _ v' l' r') eq_refl).
      cbn. lia.
    erewrite size_balance. cbn. rewrite (IHl (N _ v l r) r' eq_refl).
      cbn. lia.
Unshelve.
  all: exact 0.
Qed.

Lemma countLT_merge :
  forall (A : TrichDec) (f : A -> bool) (t1 t2 : LTree A),
    countLT f (merge (t1, t2)) = countLT f t1 + countLT f t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    erewrite countLT_balance. specialize (IHl _ _ eq_refl).
      cbn in *. rewrite IHl. unfold id. destruct (f v), (f v'); lia.
    erewrite countLT_balance. specialize (IHl _ _ eq_refl).
      cbn in *. rewrite IHl. unfold id. destruct (f v), (f v'); lia.
Unshelve.
  1-2: exact 0.
Qed.

Lemma findMin_spec :
  forall (A : TrichDec) (h : LTree A) (m : A),
    isHeap h -> findMin h = Some m -> forall x : A, Elem x h -> m ≤ x.
Proof.
  destruct h; cbn; do 3 inv 1. trich.
Qed.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall (A : TrichDec) (x y : A) (h : LTree A),
    isHeap h -> Elem x (insert y h) <-> x = y \/ Elem x h.
Proof.
  intros. unfold insert. rewrite Elem_merge'. split; inv 1.
    inv H1; inv H2.
    left. compute. auto.
Qed.

Lemma isHeap_insert :
  forall (A : TrichDec) (x : A) (t : LTree A),
    isHeap t -> isHeap (insert x t).
Proof.
  intros. unfold insert. apply isHeap_merge.
    apply isHeap_singleton.
    assumption.
Qed.

Lemma LeftBiased_insert :
  forall (A : TrichDec) (x : A) (t : LTree A),
    LeftBiased t -> LeftBiased (insert x t).
Proof.
  intros. unfold insert. apply LeftBiased_merge; auto.
  apply LeftBiased_singleton.
Qed.

Lemma size_insert :
  forall (A : TrichDec) (x : A) (t : LTree A),
    size (insert x t) = 1 + size t.
Proof.
  intros. unfold insert. rewrite size_merge. cbn. reflexivity.
Qed.

Lemma insert_countLT :
  forall (A : TrichDec) (p : A -> bool) (x : A) (t : LTree A),
    countLT p (insert x t) =
    (if p x then S else id) (countLT p t).
Proof.
  intros. unfold insert. rewrite countLT_merge. cbn.
  destruct (p x); reflexivity.
Qed.

(** Properties of [findMin], [deleteMin] and [extractMin]. *)

Lemma Elem_deleteMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') -> Elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Lemma isHeap_deleteMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply isHeap_merge; assumption.
Qed.

Lemma deleteMin_LeftBiased :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    LeftBiased t -> deleteMin t = (Some m, t') ->
      LeftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply LeftBiased_merge; assumption.
Qed.

Lemma size_deleteMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite size_merge. trivial.
Qed.

Lemma countLT_deleteMin :
  forall (A : TrichDec) (p : A -> bool) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') ->
      countLT p t = (if p m then S else id) (countLT p t').
Proof.
  destruct t; cbn; intros; inv H.
  trich; rewrite countLT_merge; reflexivity.
Qed.

Lemma deleteMin_spec :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      forall x : A, Elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (Elem_merge_conv H); auto.
Qed.

(** Properties of [extractMin]. *)

Lemma Elem_extractMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') -> Elem m t.
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma isHeap_extractMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    isHeap t -> extractMin t = Some (m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply isHeap_merge; assumption.
Qed.

Lemma LeftBiased_extractMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    LeftBiased t -> extractMin t = Some (m, t') ->
      LeftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply LeftBiased_merge; assumption.
Qed.

Lemma size_extractMin :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inv 1. rewrite size_merge. reflexivity.
Qed.

Lemma countLT_extactMin :
  forall (A : TrichDec) (p : A -> bool) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') ->
      countLT p t = (if p m then S else id) (countLT p t').
Proof.
  destruct t; cbn; intros; inv H.
  trich; rewrite countLT_merge; reflexivity.
Qed.

Lemma extractMin_spec :
  forall (A : TrichDec) (m : A) (t t' : LTree A),
    isHeap t -> extractMin t = Some (m, t') ->
      forall x : A, Elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intros. destruct (Elem_merge_conv H); auto.
Qed.

(** Leftist heapsort. *)

Fixpoint fromList {A : TrichDec} (l : list A) : LTree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Function toList {A : TrichDec} (t : LTree A) {measure size t} : list A :=
match extractMin t with
    | None => []
    | Some (m, t') => m :: toList t'
end.
Proof.
  intros. destruct t; cbn; inv teq.
  rewrite size_merge. auto.
Defined.

Arguments toList {x} _.

Definition leftistHeapsort (A : TrichDec) (l : list A) : list A :=
  toList (fromList l).

Lemma Sorted_toList :
  forall (A : TrichDec) (t : LTree A),
    isHeap t -> Sorted trich_le (toList t).
Proof.
  intros. functional induction @toList A t.
    constructor.
    rewrite toList_equation in *. destruct t'; cbn in *; constructor.
      eapply extractMin_spec; eauto.
      eapply IHl, isHeap_extractMin; eauto.
Qed.

Lemma isHeap_fromList :
  forall (A : TrichDec) (l : list A),
    isHeap (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isHeap_insert. assumption.
Qed.

Lemma Sorted_leftistHeapsort :
  forall (A : TrichDec) (l : list A),
    Sorted trich_le (leftistHeapsort A l).
Proof.
  intros. unfold leftistHeapsort. apply Sorted_toList, isHeap_fromList.
Qed.

Lemma countLT_fromList :
  forall (A : TrichDec) (p : A -> bool) (l : list A),
    countLT p (fromList l) = count p l.
Proof.
  induction l as [| h t]; cbn; trich;
  rewrite insert_countLT, IHt.
  destruct (p h); reflexivity.
Qed.

Lemma countLT_toList :
  forall (A : TrichDec) (p : A -> bool) (t : LTree A),
    count p (toList t) = countLT p t.
Proof.
  intros. functional induction @toList A t.
    destruct t; inv e.
    destruct t; inv e. cbn.
      rewrite IHl, countLT_merge. destruct (p m); reflexivity.
Qed.

Lemma perm_leftistHeapsort :
  forall (A : TrichDec) (l : list A),
    perm l (leftistHeapsort A l).
Proof.
  unfold perm, leftistHeapsort. intros.
  rewrite countLT_toList, countLT_fromList. reflexivity.
Qed.

Lemma Permutation_leftistHeapsort :
  forall (A : TrichDec) (l : list A),
    Permutation (leftistHeapsort A l) l.
Proof.
  intros. apply perm_Permutation. rewrite <- perm_leftistHeapsort.
  reflexivity.
Qed.

#[refine]
Instance Sort_leftistHeapsort (A : TrichDec) : Sort trich_le :=
{
    sort := @leftistHeapsort A;
}.
Proof.
  all: intros.
    apply Sorted_leftistHeapsort.
    apply Permutation_leftistHeapsort.
Defined.