Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import MergeSort.
Require Import InsertionSort.

Set Implicit Arguments.

Theorem ghms_sorted :
  forall (n : nat) (A : LinDec)
    (s : Sort) (split : Split A)
      (l : list A), sorted A (@ghms n A (@sort s A) split l).
Proof.
  intros. functional induction @ghms n A (@sort s A) split l.
    destruct s; cbn in *. apply sort_sorted.
    apply merge_sorted; cbn; assumption.
Qed.

Theorem ghms_perm :
  forall (n : nat) (A : LinDec)
    (s : Sort) (split : Split A)
      (l : list A), perm A l (@ghms n A (@sort s A) split l).
Proof.
  intros. functional induction @ghms n A (@sort s A) split l.
    destruct s; cbn in *. apply sort_perm.
    rewrite perm_split_app. rewrite e0; cbn.
      rewrite <- merge_perm; cbn. apply perm_app; assumption.
Qed.