Require Import Recdef Div2.

Require Import RCCBase.
Require Import Structures.TrichDec.
Require Import Sorting.Sort.
Require Import Sorting.MergeSort.

Require Import CoqMTL.Control.Monad.Lazy.

(** Sortable collections as in chapter 6.4.3 of Okasaki. *)

Module Type Sortable.

Parameter Sortable : TrichDec -> Type.

Parameter empty :
  forall {A : TrichDec}, Sortable A.

Parameter add :
  forall {A : TrichDec}, A -> Sortable A -> Sortable A.

Parameter sort :
  forall {A : TrichDec}, Sortable A -> list A.

Parameter Sorted_sort :
  forall {A : TrichDec} (s : Sortable A),
    Sorted A (sort s).

End Sortable.

Module Sortable_BottomUpMergesortWithSharing.

Definition Sortable (A : TrichDec) : Type :=
  nat * Lazy (list (list A)).

Definition isValid {A : TrichDec} (s : Sortable A) : Prop :=
  Forall (Sorted A) (force (snd s)).

Definition empty {A : TrichDec} : Sortable A :=
  (0, delay []).

Definition merge {A : TrichDec} (l1 l2 : list A) : list A :=
  Sorting.MergeSort.merge A (l1, l2).

Definition lt_Sortable {A : TrichDec} (s1 s2 : Sortable A) : Prop :=
  fst s1 < fst s2.

Lemma lt_Sortable_wf :
  forall A : TrichDec, well_founded (@lt_Sortable A).
Proof.
  intro. red. apply well_founded_lt_compat with fst.
  unfold lt_Sortable. auto.
Defined.

Function addSeg'
  {A : TrichDec} (s : Sortable A) (seg : list A) {measure fst s} : Sortable A :=
match fst s, force (snd s), even (fst s) with
    | _, [], _ => (1, delay [seg])
    | _, seg' :: segs', true => (length seg + fst s, delay (seg :: seg' :: segs'))
    | size, seg' :: segs', false => addSeg' (div2 (fst s), delay segs') (merge seg seg')
end.
Proof.
  destruct s; cbn; intros. apply Nat.lt_div2. cbn. destruct n.
    cbn in teq0. congruence.
    apply Nat.lt_0_succ.
Defined.

Definition addSeg {A} s seg := @addSeg' A seg s.

Arguments addSeg {A} _ _.

Definition add
  {A : TrichDec} (x : A) (s : Sortable A) : Sortable A :=
    addSeg [x] s.

Fixpoint sort_aux
  {A : TrichDec} (seg : list A) (segs : list (list A)) : list A :=
match segs with
    | [] => seg
    | seg' :: segs' => sort_aux (merge seg seg') segs'
end.

Definition sort {A : TrichDec} (s : Sortable A) : list A :=
  let '(_, segs) := s in sort_aux [] (force segs).

Lemma length_merge' :
  forall (A : TrichDec) (p : list A * list A),
    length (merge (fst p) (snd p)) = length (fst p) + length (snd p).
Proof.
  intros. unfold merge.
  functional induction @MergeSort.merge A p; cbn; auto.
    destruct l1; auto.
    rewrite MergeSort.merge_equation. trich.
    rewrite MergeSort.merge_equation. trich. cbn in *. rewrite IHl. lia.
Qed.

Lemma length_merge :
  forall (A : TrichDec) (l1 l2 : list A),
    length (merge l1 l2) = length l1 + length l2.
Proof.
  intros. pose (length_merge' _ (l1, l2)). cbn in e.
  assumption.
Qed.

(** Lemmas for [isValid]. *)

Lemma empty_isValid :
  forall A : TrichDec,
    isValid (@empty A).
Proof.
  intro. compute. constructor.
Qed.

Lemma addSeg_isValid :
  forall (A : TrichDec) (seg : list A) (s : Sortable A),
    Sorted A seg -> isValid s -> isValid (addSeg seg s).
Proof.
  intros. unfold addSeg. functional induction @addSeg' A s seg.
    constructor; auto.
    destruct s as [size segs]; cbn in *. compute. inv H0.
      unfold force in H2. rewrite e0 in H2. inv H2.
      unfold force in H1. rewrite e0 in H1. inv H1.
    apply IHs0.
      apply Sorted_merge; cbn; inv H0.
      inv H0. compute. rewrite e0 in H1. inv H1.
Qed.

Lemma add_isValid :
  forall (A : TrichDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma Sorted_sort_aux :
  forall (A : TrichDec) (seg : list A) (segs : list (list A)),
    Sorted A seg -> Forall (Sorted A) segs ->
      Sorted A (sort_aux seg segs).
Proof.
  intros. gen seg.
  induction segs as [| seg' segs']; cbn; intros.
    assumption.
    apply IHsegs'.
      inv H0.
      apply Sorted_merge; cbn.
        assumption.
        inv H0.
Qed.

Theorem Sorted_sort :
  forall (A : TrichDec) (s : Sortable A),
    isValid s -> Sorted A (sort s).
Proof.
  destruct s. cbn. apply Sorted_sort_aux.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing.


Module Sortable_BottomUpMergesortWithSharing'.

Definition Sortable (A : TrichDec) : Type :=
  nat * list (list A).

Definition isValid {A : TrichDec} (s : Sortable A) : Prop :=
  Forall (Sorted A) (snd s).

Definition empty {A : TrichDec} : Sortable A := (0, []).

Definition merge {A : TrichDec} (l1 l2 : list A) : list A :=
  Sorting.MergeSort.merge A (l1, l2).

Function addSeg
  {A : TrichDec} (seg : list A) (s : Sortable A)
  {measure fst s} : Sortable A :=
match s with
    | (_, []) => (1, [seg])
    | (size, seg' :: segs') =>
        if even size
        then (length seg + size, seg :: seg' :: segs')
        else addSeg (merge seg seg') (div2 size, segs')
end.
Proof.
  destruct s; cbn; intros. inv teq. apply lt_div2.
  destruct size; cbn in *.
    congruence.
    lia.
Defined.

Arguments addSeg {x} _ _.

Definition add
  {A : TrichDec} (x : A) (s : Sortable A) : Sortable A :=
    addSeg [x] s.

Fixpoint sort_aux
  {A : TrichDec} (seg : list A) (segs : list (list A)) : list A :=
match segs with
    | [] => seg
    | seg' :: segs' => sort_aux (merge seg seg') segs'
end.

Definition sort {A : TrichDec} (s : Sortable A) : list A :=
  let '(_, segs) := s in sort_aux [] segs.

Lemma length_merge' :
  forall (A : TrichDec) (p : list A * list A),
    length (merge (fst p) (snd p)) = length (fst p) + length (snd p).
Proof.
  intros. unfold merge.
  functional induction @MergeSort.merge A p; cbn; auto.
    destruct l1; auto.
    rewrite MergeSort.merge_equation. trich.
    rewrite MergeSort.merge_equation. trich. cbn in *. rewrite IHl. lia.
Qed.

Lemma length_merge :
  forall (A : TrichDec) (l1 l2 : list A),
    length (merge l1 l2) = length l1 + length l2.
Proof.
  intros. pose (length_merge' _ (l1, l2)). cbn in e.
  assumption.
Qed.

(** Lemmas for [isValid]. *)

Lemma empty_isValid :
  forall A : TrichDec,
    isValid (@empty A).
Proof.
  intro. compute. constructor.
Qed.

Lemma addSeg_isValid :
  forall (A : TrichDec) (seg : list A) (s : Sortable A),
    Sorted A seg -> isValid s -> isValid (addSeg seg s).
Proof.
  intros. functional induction @addSeg A seg s.
    compute. auto.
    compute. inv H0.
    apply IHs0.
      apply Sorted_merge; cbn; inv H0.
      inv H0.
Qed.

Lemma add_isValid :
  forall (A : TrichDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma Sorted_sort_aux :
  forall (A : TrichDec) (seg : list A) (segs : list (list A)),
    Sorted A seg -> Forall (Sorted A) segs ->
      Sorted A (sort_aux seg segs).
Proof.
  intros. gen seg.
  induction segs as [| seg' segs']; cbn; intros.
    assumption.
    apply IHsegs'.
      inv H0.
      apply Sorted_merge; cbn.
        assumption.
        inv H0.
Qed.

Theorem Sorted_sort :
  forall (A : TrichDec) (s : Sortable A),
    isValid s -> Sorted A (sort s).
Proof.
  destruct s. cbn. apply Sorted_sort_aux.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing'.