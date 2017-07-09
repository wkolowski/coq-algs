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
  split; functional induction (msFun A) l; auto; clear y; intro.
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
  intros. functional induction (msFun A) l; auto; clear y.
  apply merge_sorted; assumption.
Qed.

Theorem msFun_perm :
  forall (A : LinDec) (l : list A), perm A l (msFun A l).
Proof.
  intros. functional induction (msFun A) l; auto; clear y.
    rewrite <- (take_drop (Nat.div2 (length l))) at 1.
      rewrite <- merge_perm. apply perm_app; assumption.
Qed.

Instance Sort_msFun : Sort :=
{
    sort := msFun;
    sort_sorted := msFun_sorted;
    sort_perm := msFun_perm;
}.

Definition lenSum {A : Type} (l : list A * list A) : nat :=
  length (fst l) + length (snd l).

Definition lenSumOrd {A : Type} (l1 l2 : list A * list A) : Prop :=
  lenSum l1 < lenSum l2.

Lemma lenSumOrd_wf : forall (A : Type), well_founded (@lenSumOrd A).
Proof.
  intro. apply well_founded_lt_compat with lenSum.
  unfold lenSumOrd. auto.
Qed.

Function merge2 (A : LinDec) (l : list A * list A)
    {measure lenSum l} : list A :=
let (l1, l2) := l in match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h :: t, h' :: t' =>
        if h <=? h'
        then h :: merge2 A (t, l2)
        else h' :: merge2 A (l1, t')
end.
Proof.
  intros. unfold lenSum. simpl. omega.
  intros. unfold lenSum. simpl. omega.
Defined.

Function msFun2 (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
        let n := Nat.div2 (length l') in
        let l1 := take n l' in
        let l2 := drop n l' in
          merge2 A (msFun2 A l1, msFun2 A l2)
end.
Proof.
  intros. apply drop_length_lt. simpl. omega. inversion 1.
  intros. apply take_length_lt. apply lt_div2. simpl. omega.
Defined.

Theorem merge2_sorted :
  forall (A : LinDec) (l : list A * list A),
    sorted A (fst l) -> sorted A (snd l) -> sorted A (merge2 A l).
Proof.
  intros. functional induction (merge2 A) l; simpl in *; auto;
  rewrite merge2_equation in *.
    destruct t; simpl in *; dec.
    destruct t'; simpl in *; dec.
Qed.

Theorem merge2_perm :
  forall (A : LinDec) (l : list A * list A),
    perm A (fst l ++ snd l) (merge2 A l).
Proof.
  intros. functional induction (merge2 A) l; simpl; auto; try clear y.
    rewrite app_nil_r. auto.
    eapply perm_trans.
      rewrite app_comm_cons. apply perm_app_comm.
      simpl. apply perm_cons. simpl in IHl0. rewrite <- IHl0.
        apply perm_app_comm.
Qed.

Theorem msFun2_sorted :
  forall (A : LinDec) (l : list A), sorted A (msFun2 A l).
Proof.
  intros. functional induction (msFun2 A) l; auto.
  apply merge2_sorted; simpl; assumption.
Qed.

Theorem msFun2_perm :
  forall (A : LinDec) (l : list A), perm A l (msFun2 A l).
Proof.
  intros. functional induction (msFun2 A) l; auto; clear y.
  rewrite <- merge2_perm, <- (take_drop (Nat.div2 (length l))) at 1; simpl.
  apply perm_app; assumption.
Qed.

Instance Sort_msFun2 : Sort :=
{
    sort := msFun2;
    sort_sorted := msFun2_sorted;
    sort_perm := msFun2_perm;
}.