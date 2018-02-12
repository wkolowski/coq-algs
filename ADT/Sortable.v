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

(*Fixpoint merge {A : LinDec} (l1 l2 : list A) : list A :=
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
end.*)

Function addSeg_aux
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

Definition sort {A : LinDec} (s : Sortable A) : list A :=
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

(*Lemma merge_eq :
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
Qed.*)

Lemma merge_sorted :
  forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 -> sorted A (merge l1 l2).
Proof.
  induction 1; intros.
    cbn. assumption.
    induction H.
      cbn. dec.
      cbn. dec.
Abort.

Print addSeg.

Lemma addSeg_aux_isValid :
  forall (A : LinDec) (seg : list A) (segs : list (list A))
    (size : nat),
      sorted A seg -> isValid (size, delay segs) ->
        isValid (length seg + size, delay (addSeg_aux seg segs size)).
Proof.
  intros A seg segs size.
  functional induction @addSeg_aux A seg segs size; cbn; intros.
    red. unfold delay. cbn. auto.
    red. unfold delay. cbn. inv H0.
    

unfold delay in *; cbn in *.
  
Admitted.

Lemma addSeg_isValid :
  forall (A : LinDec) (x : A) (s : Sortable A),
    isValid s -> isValid (addSeg x s).
Proof.
  intros. destruct s. cbn.
  apply addSeg_aux_isValid; auto.
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
    sorted A (sort s).
Proof.
  destruct s. cbn. apply sort_aux_sorted.
    constructor.
Admitted.

End Sortable_BottomUpMergesortWithSharing.