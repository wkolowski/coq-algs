Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import MergeSort2.

Set Implicit Arguments.

Theorem merge2_sorted :
  forall (A : LinDec) (l : list A * list A),
    sorted A (fst l) -> sorted A (snd l) -> sorted A (merge2 A l).
Proof.
  intros. functional induction merge2 A l; simpl in *; auto;
  rewrite merge2_equation in *.
    destruct t; simpl in *; dec.
    destruct t'; simpl in *; dec.
Qed.

Theorem merge2_perm :
  forall (A : LinDec) (l : list A * list A),
    perm A (fst l ++ snd l) (merge2 A l).
Proof.
  intros. functional induction merge2 A l; simpl; auto; try clear y.
    rewrite app_nil_r. auto.
    eapply perm_trans.
      rewrite app_comm_cons. apply perm_app_comm.
      simpl. apply perm_cons. simpl in IHl0. rewrite <- IHl0.
        apply perm_app_comm.
Qed.

Theorem msFun2_sorted :
  forall (A : LinDec) (l : list A), sorted A (msFun2 A l).
Proof.
  intros. functional induction msFun2 A l; auto; clear y.
  apply merge2_sorted; simpl; assumption.
Qed.

Theorem msFun2_perm :
  forall (A : LinDec) (l : list A), perm A l (msFun2 A l).
Proof.
  intros. functional induction msFun2 A l; auto; clear y.
  rewrite <- merge2_perm, <- (take_drop (Nat.div2 (length l))) at 1; simpl.
  apply perm_app; assumption.
Qed.

Instance Sort_msFun2 : Sort :=
{
    sort := msFun2;
    sort_sorted := msFun2_sorted;
    sort_perm := msFun2_perm;
}.