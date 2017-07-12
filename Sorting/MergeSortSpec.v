Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import MergeSort.
Require Import InsertionSort.

Set Implicit Arguments.

Theorem merge_sorted :
  forall (A : LinDec) (l : list A * list A),
    sorted A (fst l) -> sorted A (snd l) -> sorted A (merge A l).
Proof.
  intros. functional induction merge A l; simpl in *; auto;
  rewrite merge_equation in *.
    destruct t; simpl in *; dec.
    destruct t'; simpl in *; dec.
Qed.

Theorem merge_perm :
  forall (A : LinDec) (l : list A * list A),
    perm A (fst l ++ snd l) (merge A l).
Proof.
  intros. functional induction merge A l; simpl; auto; try clear y.
    rewrite app_nil_r. auto.
    eapply perm_trans.
      rewrite app_comm_cons. apply perm_app_comm.
      simpl. apply perm_cons. simpl in IHl0. rewrite <- IHl0.
        apply perm_app_comm.
Qed.

Theorem ms_sorted :
  forall (A : LinDec) (l : list A), sorted A (ms A l).
Proof.
  intros. functional induction ms A l; auto; clear y.
  apply merge_sorted; simpl; assumption.
Qed.

Theorem ms_perm :
  forall (A : LinDec) (l : list A), perm A l (ms A l).
Proof.
  intros. functional induction ms A l; auto; clear y.
  rewrite <- merge_perm, <- (take_drop (Nat.div2 (length l))) at 1; simpl.
  apply perm_app; assumption.
Qed.

Instance Sort_ms : Sort :=
{
    sort := ms;
    sort_sorted := ms_sorted;
    sort_perm := ms_perm;
}.

(* Specification of ms2. *)
Theorem ms2_sorted :
  forall (A : LinDec) (l : list A), sorted A (ms2 A l).
Proof.
  intros. functional induction ms2 A l; auto; clear y.
  apply merge_sorted; simpl; assumption.
Qed.

Fixpoint interleave {A : Type} (l1 l2 : list A) : list A :=
match l1, l2 with
    | [], _ => l2
    | _, [] => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: interleave t1 t2
end.

Theorem ms_split_interleave :
  forall (A : Type) (l : list A),
    interleave (fst (ms_split l)) (snd (ms_split l)) = l.
Proof.
  induction l as [| | h h' t] using list_ind2; cbn; auto.
    destruct (ms_split t). cbn in *. rewrite IHt. auto.
Qed.

Theorem interleave_ms_split :
  forall (A : Type) (l1 l2 : list A),
    ms_split (interleave l1 l2) = (l1, l2).
Proof.
  induction l1 as [| h1 t1]. cbn.
Abort.

Lemma count_interleave :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    count A x (interleave l1 l2) = count A x l1 + count A x l2.
Proof.
  induction l1 as [| h1 t1]; cbn; auto.
    destruct l2 as [| h2 t2]; cbn.
      apply plus_n_O.
      dec; rewrite IHt1; omega.
Qed.

Lemma perm_interleave :
  forall (A : LinDec) (l1 l1' l2 l2' : list A),
    perm A l1 l1' -> perm A l2 l2' ->
      perm A (interleave l1 l2) (interleave l1' l2').
Proof.
  unfold perm. intros. rewrite !count_interleave. auto.
Qed.

Lemma merge_perm_interleave :
  forall (A : LinDec) (l : list A * list A),
    perm A (merge A l) (interleave (fst l) (snd l)).
Proof.
  unfold perm; intros. rewrite count_interleave.
  rewrite <- merge_perm. rewrite count_app. auto.
Qed.

Theorem ms2_perm :
  forall (A : LinDec) (l : list A), perm A l (ms2 A l).
Proof.
  intros. functional induction ms2 A l; auto; clear y.
  rewrite merge_perm_interleave. simpl.
    rewrite <- ms_split_interleave at 1. apply perm_interleave.
      rewrite e0. simpl. auto.
      rewrite e0. simpl. auto.
Qed.

Instance Sort_ms2 : Sort :=
{
    sort := ms2;
    sort_sorted := ms2_sorted;
    sort_perm := ms2_perm;
}.

(* Specification of hms. *)
Theorem hms_sorted :
  forall (n : nat) (A : LinDec) (l : list A), sorted A (hms n A l).
Proof.
  intros. functional induction hms n A l; auto.
    apply (@sort_sorted Sort_insertionSort).
    apply merge_sorted; simpl; assumption.
Qed.

Theorem hms_perm :
  forall (n : nat) (A : LinDec) (l : list A), perm A l (hms n A l).
Proof.
  intros. functional induction hms n A l; auto.
    apply (@sort_perm Sort_insertionSort).
    rewrite <- merge_perm, <- (take_drop (Nat.div2 (length l))) at 1; simpl.
      apply perm_app; assumption.
Qed.

Instance Sort_hms (n : nat) : Sort :=
{
    sort := hms n;
    sort_sorted := hms_sorted n;
    sort_perm := hms_perm n;
}.

(* Specification of hms2. *)
Theorem hms2_sorted :
  forall (n : nat) (A : LinDec) (l : list A), sorted A (hms2 n A l).
Proof.
  intros. functional induction hms2 n A l; auto.
    apply (@sort_sorted Sort_insertionSort).
    apply merge_sorted; simpl; assumption.
Qed.

Theorem hms2_perm :
  forall (n : nat) (A : LinDec) (l : list A), perm A l (hms2 n A l).
Proof.
  intros. functional induction hms2 n A l; auto.
    apply (@sort_perm Sort_insertionSort).
    rewrite merge_perm_interleave. simpl.
      rewrite <- ms_split_interleave at 1. apply perm_interleave.
        rewrite e0. simpl. auto.
        rewrite e0. simpl. auto.
Qed.

Instance Sort_hms2 (n : nat) : Sort :=
{
    sort := hms2 n;
    sort_sorted := hms2_sorted n;
    sort_perm := hms2_perm n;
}.

(* TODO *) Lemma ms2_is_ms :
  forall (A : LinDec) (l : list A), ms2 A l = ms A l.
Proof.
  intros. functional induction ms2 A l; auto.
    rewrite ms_equation. destruct l as [| h [| h' t]]; inversion y.
      rewrite IHl0, IHl1.
Abort.