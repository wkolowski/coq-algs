Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import MergeSort.

Set Implicit Arguments.

(*Functional Scheme merge_ind := Induction for merge Sort Prop.*)

Theorem merge_sorted : forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 -> sorted A (merge A l1 l2).
Proof.
Admitted.

Lemma merge_perm :
  forall (A : LinDec) (l1 l2 : list A),
    perm A (l1 ++ l2) (merge A l1 l2).
Proof.
Admitted.

(*Lemma merge_In :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    In x (merge A l1 l2) <-> In x (l1 ++ l2).
Proof.
Admitted.

Theorem msFun_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (msFun A l) <-> In x l.
Proof.
  split; functional induction msFun A l; auto; clear y; intro.
    apply merge_In in H. apply in_app_or in H. destruct H.
      eapply take_In. apply IHl0. assumption.
      eapply drop_In. apply IHl1. assumption.
    apply merge_In. apply in_or_app.
      rewrite <- (take_drop (Nat.div2 (length l))) in H.
      apply in_app_or in H. destruct H; auto.
Qed.*)

Theorem msFun_sorted :
  forall (A : LinDec) (l : list A), sorted A (msFun A l).
Proof.
  intros. functional induction msFun A l; auto; clear y.
  apply merge_sorted; assumption.
Qed.

Theorem msFun_perm :
  forall (A : LinDec) (l : list A), perm A l (msFun A l).
Proof.
  intros. functional induction msFun A l; auto; clear y.
    rewrite <- (take_drop (Nat.div2 (length l))) at 1.
      rewrite <- merge_perm. apply perm_app; assumption.
Qed.

Instance Sort_msFun : Sort :=
{
    sort := msFun;
    sort_sorted := msFun_sorted;
    sort_perm := msFun_perm;
}.