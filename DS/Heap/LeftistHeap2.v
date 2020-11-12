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
          @trich_le natlt (right_spine r) (right_spine l) ->
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

Inductive isHeap {A : Ord} : LTree A -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_N :
        forall  (n : nat) (v : A) (l r : LTree A),
          (forall x : A, Elem x l -> v ≤ x) -> isHeap l ->
          (forall x : A, Elem x r -> v ≤ x) -> isHeap r ->
            isHeap (N n v l r).

Hint Constructors LTree LeftBiased Elem isHeap : core.

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

(** * Properties of [balance]. *)

Lemma LeftBiased_balance :
  forall (A : Ord) (v : A) (l r : LTree A),
    LeftBiased l -> LeftBiased r ->
      LeftBiased (balance v l r).
Proof.
  intros. balance; constructor; trich.
Qed.

Lemma Elem_balance :
  forall (A : Type) (x v : A) (l r : LTree A),
    Elem x (balance v l r) <-> x = v \/ Elem x l \/ Elem x r. (*  (N n v l r). *)
Proof.
  intros. balance; split; inv 1; inv H1.
Qed.

Lemma isHeap_balance :
  forall (A : Ord) (n : nat) (v : A) (l r : LTree A),
    (forall x : A, Elem x l -> v ≤ x) ->
    (forall x : A, Elem x r -> v ≤ x) ->
      isHeap l -> isHeap r -> isHeap (balance v l r).
Proof.
  intros; balance; constructor; elem.
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
  functional induction @merge A p; do 3 inv 1; cbn in *;
  apply LeftBiased_balance; try eapply IHl; auto.
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
  functional induction merge p; do 3 inv 1; apply isHeap_balance; elem.
    rewrite Elem_merge, Elem_N in H. decompose [or] H; clear H; eauto; trich.
      specialize (H8 _ H0). trich.
      specialize (H10 _ H0). trich.
    eapply IHl; eauto.
    rewrite Elem_merge, Elem_N in H. decompose [or] H; clear H; eauto; trich.
      specialize (H4 _ H0). trich.
      specialize (H6 _ H0). trich.
    eapply IHl; eauto.
Qed.

Lemma size_merge:
  forall (A : Ord) (t1 t2 : LTree A),
    size (merge (t1, t2)) = size t1 + size t2.
Proof.
  intros. remember (t1, t2) as p. revert t1 t2 Heqp.
  functional induction merge p; inv 1.
    rewrite size_balance, (IHl _ _ eq_refl). cbn. lia.
    rewrite size_balance, (IHl _ _ eq_refl). cbn. lia.
Qed.

(** * Properties of [insert]. *)

(** * Properties of [findMin], [deleteMin] and [extractMin]. *)

Lemma LeftBiased_deleteMin :
  forall (A : Ord) (m : A) (t t' : LTree A),
    LeftBiased t -> deleteMin t = (Some m, t') ->
      LeftBiased t'.
Proof.
  destruct t; cbn; do 2 inversion 1; subst.
  apply LeftBiased_merge; assumption.
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

Lemma size_deleteMin:
  forall (A : Ord) (m : A) (t t' : LTree A),
    deleteMin t = (Some m, t') -> size t = S (size t').
Proof.
  destruct t; cbn; inversion 1; subst. rewrite size_merge. trivial.
Qed.

Lemma deleteMin_spec :
  forall (A : Ord) (m : A) (t t' : LTree A),
    isHeap t -> deleteMin t = (Some m, t') ->
      forall x : A, Elem x t' -> m ≤ x.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst; cbn.
  intro. rewrite Elem_merge. inv 1.
Qed.

(** * Properties of [extractMin]. *)

(** * Leftist heapsort *)

Function fromList {A : Ord} (l : list A) : LTree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Function toList {A : Ord} (t : LTree A)
  {measure size t} : list A :=
match deleteMin t with
    | (None, _) => []
    | (Some m, t') => m :: toList t'
end.
Proof.
  destruct t; cbn; inversion 1; inversion 1; subst.
  rewrite size_merge. lia.
Defined.

Arguments toList [x] _.

Definition leftistHeapsort (A : Ord) (l : list A)
  : list A := toList (fromList l).