Require Export Ord.
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

Inductive LeftBiased {A : Type} : LTree A -> Prop :=
    | LeftBiased_E : LeftBiased E
    | LeftBiased_N :
        forall (v : A) (l r : LTree A),
          right_spine r <= right_spine l ->
          LeftBiased l -> LeftBiased r ->
            LeftBiased (N (1 + right_spine r) v l r).

Inductive LeftBiased2 {A : Type} : LTree A -> Prop :=
    | LeftBiased2_E : LeftBiased2 E
    | LeftBiased2_N :
        forall (v : A) (l r : LTree A),
          @trich_le natlt (right_spine r) (right_spine l) ->
          LeftBiased2 l -> LeftBiased2 r ->
            LeftBiased2 (N (1 + right_spine r) v l r).

Inductive Elem {A : Type} (x : A) : LTree A -> Prop :=
    | Elem_root :
        forall (n : nat) (l r : LTree A), Elem x (N n x l r)
    | Elem_l :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x l -> Elem x (N n v l r)
    | Elem_r :
        forall (n : nat) (v : A) (l r : LTree A),
          Elem x r -> Elem x (N n v l r).

Inductive isHeap {A : Ord} : LTree A -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall  (n : nat) (v : A) (l r : LTree A),
          (forall x : A, Elem x l -> v ≤ x) -> isHeap l ->
          (forall x : A, Elem x r -> v ≤ x) -> isHeap r ->
            isHeap (N n v l r).

Hint Constructors LTree LeftBiased LeftBiased2 Elem isHeap : core.

Definition balance
  {A : Type} (v : A) (l r : LTree A) : LTree A :=
    if right_spine r ≤? right_spine l
    then N (1 + right_spine r) v l r
    else N (1 + right_spine l) v r l.

Fixpoint size {A : Type} (t : LTree A) : nat :=
match t with
    | E => 0
    | N _ _ l r => 1 + size l + size r
end.

Definition sum_of_sizes
  {A : Type} (p : LTree A * LTree A) : nat :=
    size (fst p) + size (snd p).

Function merge
  {A : Ord} (p : LTree A * LTree A)
  {measure sum_of_sizes p} : LTree A :=
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

Definition empty {A : Ord} (x : A) : LTree A := E.

Definition isEmpty {A : Type} (t : LTree A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition singleton {A : Type} (x : A) : LTree A := N 1 x E E.

Definition insert {A : Ord} (x : A) (t : LTree A) : LTree A :=
  merge (singleton x, t).

Definition findMin {A : Type} (t : LTree A) : option A :=
match t with
    | E => None
    | N _ v _ _ => Some v
end.

Definition deleteMin {A : Ord} (t : LTree A) : option A * LTree A :=
match t with
    | E => (None, E)
    | N _ v l r => (Some v, merge (l, r))
end.

Definition extractMin
  {A : Ord} (t : LTree A) : option (A * LTree A) :=
match t with
    | E => None
    | N _ v l r => Some (v, merge (l, r))
end.

Ltac balance := unfold balance in *; intros;
match goal with
    | H : context [right_spine ?r ≤? right_spine ?l] |- _ =>
        destruct (@trich_leb_spec natlt (right_spine r) (right_spine l))
    | |- context [right_spine ?r ≤? right_spine ?l] =>
        destruct (@trich_leb_spec natlt (right_spine r) (right_spine l))
end; cbn; try reflexivity.

Ltac elem :=
  intros; unfold singleton in *; cbn in *; subst; repeat
match goal with
    | |- Elem ?x (N _ ?x _ _) => constructor
    | H : Elem _ E |- _ => inv H
    | H : Elem _ (N _ _ E E) |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : Elem _ _ \/ Elem _ _ |- _ => destruct H
    | H1 : forall _, Elem _ _ -> _,
      H2 : Elem _ _ |- _ => specialize (H1 _ H2)
end; auto.

Lemma Elem_N :
  forall (A : Type) (n : nat) (x v : A) (l r : LTree A),
    Elem x (N n v l r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  split; inv 1. inv H0.
Qed.

(** * Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : Ord) (v : A) (l r : LTree A),
    isEmpty (balance v l r) = false.
Proof. balance. Qed.

Lemma isEmpty_merge :
  forall (A : Ord) (t1 t2 : LTree A),
    isEmpty (merge (t1, t2)) = isEmpty t1 && isEmpty t2.
Proof.
  intros. remember (t1, t2) as p.
  functional induction @merge A p; inv Heqp.
    destruct t1; cbn; reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
    rewrite isEmpty_balance. cbn. reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : Ord) (x : A) (t : LTree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_merge. cbn. reflexivity.
Qed.

Lemma isEmpty_extractMin_false :
  forall (A : Ord) (t : LTree A),
    isEmpty t = true <-> extractMin t = None.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_extractMin_true :
  forall (A : Ord) (t : LTree A),
    isEmpty t = false <->
    exists (m : A) (t' : LTree A), extractMin t = Some (m, t').
Proof.
  split; destruct t; cbn; intros; try congruence.
    eauto.
    firstorder congruence.
Qed.

Lemma LeftBiased_isEmpty :
  forall (A : Ord) (t : LTree A),
    isEmpty t = true -> LeftBiased t.
Proof.
  destruct t; inv 1.
Qed.

Lemma LeftBiased2_isEmpty :
  forall {A : Ord} {t : LTree A},
    isEmpty t = true -> LeftBiased t.
Proof.
  destruct t; inv 1.
Qed.

(** * Properties of [singleton]. *)

Lemma LeftBiased_singleton :
  forall (A : Ord) (x : A),
    LeftBiased (singleton x).
Proof.
  intros. unfold singleton.
  apply (@LeftBiased_N A x E E); auto.
Qed.

Lemma LeftBiased2_singleton :
  forall {A : Ord} (x : A),
    LeftBiased2 (singleton x).
Proof.
  intros. unfold singleton.
  apply (@LeftBiased2_N A x E E); trich.
Qed.

Lemma Elem_singleton :
  forall {A : Type} (x y : A),
    Elem x (singleton y) <-> x = y.
Proof.
  split.
    inv 1; inv H1.
    inv 1. constructor.
Qed.

Lemma isHeap_singleton :
  forall (A : Ord) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton.
  constructor; auto; inv 1.
Defined.

(** * Properties of [balance]. *)

Lemma LeftBiased_balance :
  forall (A : Ord) (v : A) (l r : LTree A),
    LeftBiased l -> LeftBiased r ->
      LeftBiased (balance v l r).
Proof.
  intros. balance; constructor; cbn in *; trich.
    rewrite <- trich_le_nf in H1. destruct H1; cbn in *; lia.
    cbn in H1. lia.
Qed.

Lemma LeftBiased2_balance :
  forall (A : Ord) (v : A) (l r : LTree A),
    LeftBiased2 l -> LeftBiased2 r ->
      LeftBiased2 (balance v l r).
Proof.
  intros. balance; constructor; trich.
Qed.

Lemma Elem_balance :
  forall (A : Type) (x v : A) (l r : LTree A),
    Elem x (balance v l r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  intros. balance; split; inv 1; inv H1.
Qed.

Lemma isHeap_balance :
  forall (A : Ord) (v : A) (l r : LTree A),
    (forall x : A, Elem x l -> v ≤ x) ->
    (forall x : A, Elem x r -> v ≤ x) ->
    isHeap l -> isHeap r -> isHeap (balance v l r).
Proof.
  intros. balance; constructor; elem.
Qed.

Lemma size_balance:
  forall (A : Type) (v : A) (l r : LTree A),
    size (balance v l r) = 1 + size l + size r.
Proof.
  intros. balance; trich. lia.
Qed.

(** * Properties of [merge]. *)

Lemma LeftBiased_merge :
  forall (A : Ord) (t1 t2 : LTree A),
    LeftBiased t1 -> LeftBiased t2 -> LeftBiased (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction merge p;
  do 3 inv 1; cbn in *;
  apply LeftBiased_balance; try eapply IHl; auto.
Qed.

Lemma LeftBiased2_merge :
  forall (A : Ord) (t1 t2 : LTree A),
    LeftBiased2 t1 -> LeftBiased2 t2 ->
      LeftBiased2 (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction merge p;
  do 3 inv 1; cbn in *;
  apply LeftBiased2_balance; try eapply IHl; auto.
Qed.

Lemma Elem_merge :
  forall (A : Ord) (x : A) (t1 t2 : LTree A),
    Elem x (merge (t1, t2)) <-> Elem x t1 \/ Elem x t2.
Proof.
  intros until t2. revert x.
  remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction merge p;
  inv 1; intro.
    firstorder. inv H.
    firstorder. inv H.
    rewrite Elem_balance, (IHl _ _ eq_refl), !Elem_N.
      split; intro H; decompose [or] H; auto 6.
    rewrite Elem_balance, (IHl _ _ eq_refl), !Elem_N.
      split; intro H; decompose [or] H; auto 6.
Qed.

Lemma isHeap_merge :
  forall (A : Ord) (t1 t2 : LTree A),
    isHeap t1 -> isHeap t2 -> isHeap (merge (t1, t2)).
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp H H0.
  functional induction merge p;
  do 3 inv 1; apply isHeap_balance;
  intros; rewrite ?Elem_merge in *; elem; eauto.
    inv H; elem; trich.
    inv H; elem; trich.
Qed.

Lemma size_merge :
  forall (A : Ord) (t1 t2 : LTree A),
    size (merge (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    rewrite size_balance, (IHl _ _ eq_refl). cbn. lia.
    rewrite size_balance, (IHl _ _ eq_refl). cbn. lia.
Qed.

(** * Properties of [insert]. *)

Lemma LeftBiased_insert :
  forall (A : Ord) (x : A) (t : LTree A),
    LeftBiased t -> LeftBiased (insert x t).
Proof.
  intros. unfold insert. apply LeftBiased_merge; auto.
  apply LeftBiased_singleton.
Qed.

Lemma LeftBiased2_insert :
  forall (A : Ord) (x : A) (t : LTree A),
    LeftBiased2 t -> LeftBiased2 (insert x t).
Proof.
  intros. unfold insert.
  apply LeftBiased2_merge; auto.
  apply LeftBiased2_singleton.
Qed.

Lemma Elem_insert :
  forall (A : Ord) (x y : A) (h : LTree A),
    isHeap h -> Elem x (insert y h) <-> x = y \/ Elem x h.
Proof.
  intros. unfold insert.
  rewrite Elem_merge, Elem_singleton.
  reflexivity.
Qed.

Lemma isHeap_insert :
  forall (A : Ord) (x : A) (t : LTree A),
    isHeap t -> isHeap (insert x t).
Proof.
  intros. unfold insert. apply isHeap_merge.
    apply isHeap_singleton.
    assumption.
Qed.

Lemma size_insert :
  forall (A : Ord) (x : A) (t : LTree A),
    size (insert x t) = 1 + size t.
Proof.
  intros. unfold insert. rewrite size_merge. cbn. reflexivity.
Qed.

(** * Properties of [deleteMin]. *)

Lemma LeftBiased_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    LeftBiased t -> deleteMin t = (Some m, t') ->
      LeftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply LeftBiased_merge; assumption.
Qed.

Lemma LeftBiased2_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    LeftBiased2 t -> deleteMin t = (Some m, t') ->
      LeftBiased2 t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply LeftBiased2_merge; assumption.
Qed.

Lemma Elem_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') -> Elem m t.
Proof.
  destruct t; cbn; inversion 1. constructor.
Qed.

Lemma isHeap_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  apply isHeap_merge; assumption.
Qed.

Lemma deleteMin_spec :
  forall (A : Ord) (m : A) (t t' : LTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      forall x : A, Elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intro. rewrite Elem_merge. inv 1.
Qed.

Lemma size_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite size_merge. reflexivity.
Qed.

(** * Properties of [extractMin]. *)

Lemma LeftBiased_extractMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    LeftBiased t -> extractMin t = Some (m, t') ->
      LeftBiased t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply LeftBiased_merge; assumption.
Qed.

Lemma Elem_extractMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') -> Elem m t.
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma isHeap_extractMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    isHeap t -> extractMin t = Some (m, t') ->
      isHeap t'.
Proof.
  destruct t; cbn; do 2 inv 1.
  apply isHeap_merge; assumption.
Qed.

Lemma size_extractMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inv 1. rewrite size_merge. reflexivity.
Qed.

Lemma extractMin_spec :
  forall (A : Ord) (m : A) (t t' : LTree A),
    isHeap t -> extractMin t = Some (m, t') ->
      forall x : A, Elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; do 2 inv 1.
  intro. rewrite Elem_merge. inv 1.
Qed.

(** * Leftist heapsort. *)

Fixpoint fromList {A : Ord} (l : list A) : LTree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Function toList {A : Ord} (t : LTree A) {measure size t} : list A :=
match extractMin t with
    | None => []
    | Some (m, t') => m :: toList t'
end.
Proof.
  intros. destruct t; cbn; inv teq.
  rewrite size_merge. auto.
Defined.

Arguments toList {x} _.

Definition leftistHeapsort (A : Ord) (l : list A) : list A :=
  toList (fromList l).

(** * Sortedness *)

Lemma isHeap_fromList :
  forall (A : Ord) (l : list A),
    isHeap (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isHeap_insert. assumption.
Qed.

Lemma Sorted_toList :
  forall (A : Ord) (t : LTree A),
    isHeap t -> Sorted trich_le (toList t).
Proof.
  intros. functional induction @toList A t.
    constructor.
    rewrite toList_equation in *. destruct t'; cbn in *; constructor.
      eapply extractMin_spec; eauto.
      eapply IHl, isHeap_extractMin; eauto.
Qed.

Theorem Sorted_leftistHeapsort :
  forall (A : Ord) (l : list A),
    Sorted trich_le (leftistHeapsort A l).
Proof.
  intros. unfold leftistHeapsort. apply Sorted_toList, isHeap_fromList.
Qed.

(** * Permutationness *)

Fixpoint countLT {A : Type} (p : A -> bool) (t : LTree A) : nat :=
match t with
    | E => 0
    | N _ v l r =>
        (if p v then 1 else 0) + countLT p l + countLT p r
end.

Lemma countLT_balance :
  forall (A : Type) (p : A -> bool) (v : A) (l r : LTree A),
    countLT p (balance v l r) =
      (if p v then 1 else 0) + countLT p l + countLT p r.
Proof.
  intros. balance; trich. lia.
Qed.

Lemma countLT_merge :
  forall (A : Ord) (f : A -> bool) (t1 t2 : LTree A),
    countLT f (merge (t1, t2)) = countLT f t1 + countLT f t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction @merge A p; inv 1.
    rewrite countLT_balance. rewrite (IHl _ _ eq_refl). cbn. lia.
    rewrite countLT_balance. rewrite (IHl _ _ eq_refl). cbn. lia.
Qed.

Lemma countLT_insert :
  forall (A : Ord) (p : A -> bool) (x : A) (t : LTree A),
    countLT p (insert x t) =
    (if p x then 1 else 0) + countLT p t.
Proof.
  intros. unfold insert. rewrite countLT_merge. cbn.
  destruct (p x); reflexivity.
Qed.

Lemma countLT_deleteMin :
  forall (A : Ord) (p : A -> bool) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') ->
      countLT p t = (if p m then 1 else 0) + countLT p t'.
Proof.
  destruct t; cbn; intros; inv H.
  trich; rewrite countLT_merge; lia.
Qed.

Lemma countLT_extactMin :
  forall (A : Ord) (p : A -> bool) (m : A) (t t' : LTree A),
    extractMin t = Some (m, t') ->
      countLT p t = (if p m then 1 else 0) + countLT p t'.
Proof.
  destruct t; cbn; intros; inv H.
  trich; rewrite countLT_merge. lia.
Qed.

Lemma countLT_fromList :
  forall (A : Ord) (p : A -> bool) (l : list A),
    countLT p (fromList l) = count p l.
Proof.
  induction l as [| h t]; cbn; trich;
  rewrite countLT_insert, IHt.
  destruct (p h); reflexivity.
Qed.

Lemma countLT_toList :
  forall (A : Ord) (p : A -> bool) (t : LTree A),
    count p (toList t) = countLT p t.
Proof.
  intros. functional induction @toList A t.
    destruct t; inv e.
    destruct t; inv e. cbn.
      rewrite IHl, countLT_merge. destruct (p m); reflexivity.
Qed.

Lemma perm_leftistHeapsort :
  forall (A : Ord) (l : list A),
    perm l (leftistHeapsort A l).
Proof.
  unfold perm, leftistHeapsort. intros.
  rewrite countLT_toList, countLT_fromList. reflexivity.
Qed.

Lemma Permutation_leftistHeapsort :
  forall (A : Ord) (l : list A),
    Permutation (leftistHeapsort A l) l.
Proof.
  intros. apply perm_Permutation. rewrite <- perm_leftistHeapsort.
  reflexivity.
Qed.

#[refine]
Instance Sort_leftistHeapsort (A : Ord) : Sort trich_le :=
{
    sort := @leftistHeapsort A;
}.
Proof.
  all: intros.
    apply Sorted_leftistHeapsort.
    apply Permutation_leftistHeapsort.
Defined.