Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.
Require Import Structures.LinDec.
Require Import Sorting.Sort.

Require Import HSLib.Instances.Lazy.

(** Sortable collections as in chapter 6.4.3 of Okasaki. *)

Module Type Sortable.

Parameter Sortable : LinDec -> Type.

Parameter empty :
  forall {A : LinDec}, Sortable A.

Parameter add :
  forall {A : LinDec}, A -> Sortable A -> Sortable A.

Parameter sort :
  forall {A : LinDec}, Sortable A -> list A.

Parameter sort_sorted :
  forall {A : LinDec} (s : Sortable A),
    sorted A (sort s).

End Sortable.

Module Sortable_BottomUpMergesortWithSharing.

Definition Sortable (A : LinDec) : Type :=
  nat * Lazy (list (list A)).

Definition isValid {A : LinDec} (s : Sortable A) : Prop :=
  Forall (sorted A) (force (snd s)).

Definition empty {A : LinDec} : Sortable A :=
  (0, delay []).

Require Import Div2.

Function isEven (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => isEven n'
end.

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

Function addSeg
  {A : LinDec} (seg : list A) (s : Sortable A)
  {measure fst s} : Sortable A :=
match fst s, force (snd s) with
    | _, [] => (1, delay [seg])
    | size, seg' :: segs' =>
        if isEven size
        then (length seg + size, delay (seg :: seg' :: segs'))
        else addSeg (merge seg seg') (div2 size, delay segs')
end.
Proof.
  destruct s; cbn; intros. apply lt_div2.
  destruct n; cbn in *.
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
    sorted A seg -> isValid s -> isValid (addSeg seg s).
Proof.
  intros. functional induction @addSeg A seg s.
    compute. auto.
    destruct s as [size segs]; cbn in *. compute. inv H0.
      unfold force in H2. rewrite e0 in H2. inv H2.
      unfold force in H1. rewrite e0 in H1. inv H1.
    apply IHs0.
      apply merge_sorted; cbn; inv H0.
      inv H0. compute. rewrite e0 in H1. inv H1.
Qed.

Lemma add_isValid :
  forall (A : LinDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma sort_aux_sorted :
  forall (A : LinDec) (seg : list A) (segs : list (list A)),
    sorted A seg -> Forall (sorted A) segs ->
      sorted A (sort_aux seg segs).
Proof.
  intros. gen seg.
  induction segs as [| seg' segs']; cbn; intros.
    assumption.
    apply IHsegs'.
      inv H0.
      apply merge_sorted; cbn.
        assumption.
        inv H0.
Qed.

Theorem sort_sorted :
  forall (A : LinDec) (s : Sortable A),
    isValid s -> sorted A (sort s).
Proof.
  destruct s. cbn. apply sort_aux_sorted.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing.

Module Sortable_BottomUpMergesortWithSharing'.

Definition Sortable (A : LinDec) : Type :=
  nat * list (list A).

Definition isValid {A : LinDec} (s : Sortable A) : Prop :=
  Forall (sorted A) (snd s).

Definition empty {A : LinDec} : Sortable A := (0, []).

Require Import Div2.

Function isEven (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => isEven n'
end.

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
    sorted A seg -> isValid s -> isValid (addSeg seg s).
Proof.
  intros. functional induction @addSeg A seg s.
    compute. auto.
    compute. inv H0.
    apply IHs0.
      apply merge_sorted; cbn; inv H0.
      inv H0.
Qed.

Lemma add_isValid :
  forall (A : LinDec) (x : A) (s : Sortable A),
    isValid s -> isValid (add x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_isValid; auto.
Qed.

Lemma sort_aux_sorted :
  forall (A : LinDec) (seg : list A) (segs : list (list A)),
    sorted A seg -> Forall (sorted A) segs ->
      sorted A (sort_aux seg segs).
Proof.
  intros. gen seg.
  induction segs as [| seg' segs']; cbn; intros.
    assumption.
    apply IHsegs'.
      inv H0.
      apply merge_sorted; cbn.
        assumption.
        inv H0.
Qed.

Theorem sort_sorted :
  forall (A : LinDec) (s : Sortable A),
    isValid s -> sorted A (sort s).
Proof.
  destruct s. cbn. apply sort_aux_sorted.
    constructor.
Qed.

End Sortable_BottomUpMergesortWithSharing'.