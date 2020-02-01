Require Import RCCBase.
Require Import Structures.LinDec.
Require Import Sorting.Sort.

(** Sortable collections as in chapter 6.4.3 of Okasaki. *)

Module Type Sortable.

Parameter Sortable : LinDec -> Type.

Parameter empty :
  forall {A : LinDec}, Sortable A.

Parameter add :
  forall {A : LinDec}, A -> Sortable A -> Sortable A.

Parameter sort :
  forall {A : LinDec}, Sortable A -> list A.

Parameter Sorted_sort :
  forall {A : LinDec} (s : Sortable A),
    Sorted A (sort s).

End Sortable.

(*
Module Sortable_BottomUpMergesortWithSharing.

Definition Sortable (A : LinDec) : Type :=
  nat * Lazy (list (list A)).

Definition isValid {A : LinDec} (s : Sortable A) : Prop :=
  Forall (Sorted A) (force (snd s)).

Definition empty {A : LinDec} : Sortable A :=
  (0, delay []).

Require Import Div2.

Require Import Sorting.MergeSort.

Definition merge {A : LinDec} (l1 l2 : list A) : list A :=
  Sorting.MergeSort.merge A (l1, l2).

(*Function addSeg
  {A : LinDec} (seg : list A) (segs : list (list A)) (size : nat)
  : list (list A) :=
match segs with
    | [] => [seg]
    | seg' :: segs' =>
        if isEven size
        then seg :: segs
        else addSeg (merge seg seg') segs' (div2 size)
end.*)

From Equations Require Import Equations.

Definition lt_Sortable {A : LinDec} (s1 s2 : Sortable A) : Prop :=
  fst s1 < fst s2.

#[refine]
Instance lt_Sortable_wf (A : LinDec) : WellFounded (@lt_Sortable A).
Proof.
  red. apply well_founded_lt_compat with fst.
  unfold lt_Sortable. auto.
Defined.

Equations addSeg'
  {A : LinDec} (s : Sortable A) (seg : list A) : Sortable A
  by wf (fst s) lt :=
addSeg' s seg with (fst s, force (snd s), even (fst s)) => {
  addSeg' s seg (_, [], _) := (1, delay [seg]);
  addSeg' s seg (_, seg' :: segs', true) :=
    (length seg + fst s, delay (seg :: seg' :: segs'));
  addSeg' s seg (size, seg' :: segs', false) :=
    addSeg' (div2 (fst s), delay segs') (merge seg seg')}.
Next Obligation.
  destruct s; cbn; intros. apply Nat.lt_div2. cbn in *.
  destruct n; cbn in *.
Admitted.

Definition addSeg {A} s seg := @addSeg' A seg s.

Arguments addSeg {A} _ _.

Definition add
  {A : LinDec} (x : A) (s : Sortable A) : Sortable A :=
    addSeg [x] s.

Fixpoint sort_aux
  {A : LinDec} (seg : list A) (segs : list (list A)) : list A :=
match segs with
    | [] => seg
    | seg' :: segs' => sort_aux (merge seg seg') segs'
end.

Definition sort {A : LinDec} (s : Sortable A) : list A :=
  let '(_, segs) := s in sort_aux [] (force segs).

Lemma length_merge' :
  forall (A : LinDec) (p : list A * list A),
    length (merge (fst p) (snd p)) = length (fst p) + length (snd p).
Proof.
  intros. unfold merge.
  functional induction @MergeSort.merge A p; cbn; auto.
    destruct l1; auto.
    rewrite MergeSort.merge_equation. dec.
    rewrite MergeSort.merge_equation. dec. cbn in *. rewrite IHl. omega.
Qed.

Lemma length_merge :
  forall (A : LinDec) (l1 l2 : list A),
    length (merge l1 l2) = length l1 + length l2.
Proof.
  intros. pose (length_merge' _ (l1, l2)). cbn in e.
  assumption.
Qed.

(** Lemmas for [isValid]. *)

Lemma empty_isValid :
  forall A : LinDec,
    isValid (@empty A).
Proof.
  intro. compute. constructor.
Qed.

Lemma addSeg_isValid :
  forall (A : LinDec) (seg : list A) (s : Sortable A),
    Sorted A seg -> isValid s -> isValid (addSeg seg s).
Proof.
(*
  intros. functional induction @addSeg A seg s.
    compute. auto.
    destruct s as [size segs]; cbn in *. compute. inv H0.
      unfold force in H2. rewrite e0 in H2. inv H2.
      unfold force in H1. rewrite e0 in H1. inv H1.
    apply IHs0.
      apply Sorted_merge; cbn; inv H0.
      inv H0. compute. rewrite e0 in H1. inv H1.
*)
Restart.
  intros. unfold addSeg. revert H H0.
  funelim (addSeg' s seg); intros.
    constructor; auto.
    destruct s0 as [size segs]; cbn in *. compute. inv H2.
      compute in H4. congruence.
      compute in H3. rewrite <- H3 in H. inv H.
    apply H.
      apply Sorted_merge; cbn; inv H3.
      compute. inv H3. rewrite H0 in H4. inv H4.
Admitted.

Lemma add_isValid :
  forall (A : LinDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma Sorted_sort_aux :
  forall (A : LinDec) (seg : list A) (segs : list (list A)),
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
  forall (A : LinDec) (s : Sortable A),
    isValid s -> Sorted A (sort s).
Proof.
  destruct s. cbn. apply Sorted_sort_aux.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing.
*)

(*
Module Sortable_BottomUpMergesortWithSharing'.

Definition Sortable (A : LinDec) : Type :=
  nat * list (list A).

Definition isValid {A : LinDec} (s : Sortable A) : Prop :=
  Forall (Sorted A) (snd s).

Definition empty {A : LinDec} : Sortable A := (0, []).

Require Import Sorting.MergeSort.

Definition merge {A : LinDec} (l1 l2 : list A) : list A :=
  Sorting.MergeSort.merge A (l1, l2).

Function addSeg
  {A : LinDec} (seg : list A) (s : Sortable A)
  {measure fst s} : Sortable A :=
match s with
    | (_, []) => (1, [seg])
    | (size, seg' :: segs') =>
        if isEven size
        then (length seg + size, seg :: seg' :: segs')
        else addSeg (merge seg seg') (div2 size, segs')
end.
Proof.
  destruct s; cbn; intros. inv teq. apply lt_div2.
  destruct size; cbn in *.
    congruence.
    omega.
Defined.

Arguments addSeg {x} _ _.

Definition add
  {A : LinDec} (x : A) (s : Sortable A) : Sortable A :=
    addSeg [x] s.

Fixpoint sort_aux
  {A : LinDec} (seg : list A) (segs : list (list A)) : list A :=
match segs with
    | [] => seg
    | seg' :: segs' => sort_aux (merge seg seg') segs'
end.

Definition sort {A : LinDec} (s : Sortable A) : list A :=
  let '(_, segs) := s in sort_aux [] segs.

Lemma length_merge' :
  forall (A : LinDec) (p : list A * list A),
    length (merge (fst p) (snd p)) = length (fst p) + length (snd p).
Proof.
  intros. unfold merge.
  functional induction @MergeSort.merge A p; cbn; auto.
    destruct l1; auto.
    rewrite MergeSort.merge_equation. dec.
    rewrite MergeSort.merge_equation. dec. cbn in *. rewrite IHl. omega.
Qed.

Lemma length_merge :
  forall (A : LinDec) (l1 l2 : list A),
    length (merge l1 l2) = length l1 + length l2.
Proof.
  intros. pose (length_merge' _ (l1, l2)). cbn in e.
  assumption.
Qed.

(** Lemmas for [isValid]. *)

Lemma empty_isValid :
  forall A : LinDec,
    isValid (@empty A).
Proof.
  intro. compute. constructor.
Qed.

Lemma addSeg_isValid :
  forall (A : LinDec) (seg : list A) (s : Sortable A),
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
  forall (A : LinDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma Sorted_sort_aux :
  forall (A : LinDec) (seg : list A) (segs : list (list A)),
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
  forall (A : LinDec) (s : Sortable A),
    isValid s -> Sorted A (sort s).
Proof.
  destruct s. cbn. apply Sorted_sort_aux.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing'.
*)