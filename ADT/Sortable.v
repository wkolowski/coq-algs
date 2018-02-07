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

Definition empty {A : LinDec} : Sortable A :=
  (0, delay []).

Require Import Div2.

Function isEven (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => isEven n'
end.

Fixpoint merge {A : LinDec} (l1 l2 : list A) : list A :=
match l1 with
    | [] => l2
    | h1 :: t1 =>
        let
          aux := fix aux (l1 l2 : list A) : list A :=
          match l2 with
              | [] => l1
              | h2 :: t2 =>
                  if h1 <=? h2
                  then h1 :: merge t1 l2
                  else h2 :: aux l1 t2
          end
        in aux l1 l2
end.

Fixpoint addSeg_aux
  {A : LinDec} (seg : list A) (segs : list (list A)) (size : nat)
  : list (list A) :=
match segs with
    | [] => [seg]
    | seg' :: segs' =>
        if isEven size
        then seg :: segs
        else addSeg_aux (merge seg seg') segs' (div2 size)
end.

Definition addSeg
  {A : LinDec} (x : A) (s : Sortable A) : Sortable A :=
    let '(size, segs) := s in
      (1 + size, delay (addSeg_aux [x] (force segs) size)).

Fixpoint sort_aux
  {A : LinDec} (seg : list A) (segs : list (list A)) : list A :=
match segs with
    | [] => seg
    | seg' :: segs' => sort_aux (merge seg seg') segs'
end.

Fixpoint sort {A : LinDec} (s : Sortable A) : list A :=
  let '(_, segs) := s in sort_aux [] (force segs).

Lemma addSeg_aux_not_nil :
  forall (A : LinDec) (seg : list A) (segs : list (list A)) (size : nat),
    addSeg_aux seg segs size <> [].
Proof.
  intros A seg segs size; gen size; gen seg.
  induction segs as [| seg' segs']; cbn; intros.
    inv 1.
    destruct (isEven size).
      inv 1.
      apply IHsegs'.
Qed.

Lemma merge_eq :
  forall (A : LinDec) (l1 l2 : list A),
    merge l1 l2 =
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if h1 <=? h2
            then h1 :: merge t1 l2
            else h2 :: merge l1 t2
    end.
Proof.
  destruct l1, l2; reflexivity.
Qed.

Lemma merge_sorted :
  forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 -> sorted A (merge l1 l2).
Proof.
  induction 1; intros.
    cbn. assumption.
    induction H.
      cbn. dec.
      cbn. dec.
      rewrite !merge_eq.
Restart.
  induction l1 as [| h1 t1]; induction l2 as [| h2 t2]; intros.
    1-3: assumption.
    rewrite merge_eq. dec.
      case_eq (merge t1 (h2 :: t2)); intros; auto.
Abort.

Require Import Sorting.MergeSort.