Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import QuickSort.

Require Import InsertionSort.

Set Implicit Arguments.

(*Theorem hqs_perm :
  forall (n : nat) (A : LinDec) (s : Sort A) (l : list A),
    perm A l (hqs n A sort l).
Proof.
  intros. functional induction hqs n A sort l; trivial.
    destruct s; cbn. apply sort_perm.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro.
        rewrite count_app, <- IHl0, <- IHl1.
        rewrite bifilter_spec in e1; inversion_clear e1.
        rewrite <- count_filter. auto.
Qed.

Theorem hqs_In :
  forall (n : nat) (A : LinDec) (s : Sort A) (x : A) (l : list A),
    In x (hqs n A sort l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- hqs_perm; auto. reflexivity.
Qed.

Theorem hqs_sorted :
  forall (n : nat) (A : LinDec) (s : Sort A) (l : list A),
    sorted A (hqs n A sort l).
Proof.
  intros. functional induction hqs n A sort l; trivial.
    destruct s; cbn. apply sort_sorted.
    rewrite bifilter_spec in e1; inversion e1; subst. apply sorted_app_all.
      assumption.
       apply sorted_cons.
        intros. rewrite hqs_In, filter_In in H; auto. destruct H.
          destruct (leqb_spec x h).
            inversion H0.
            apply LinDec_not_leq. assumption.
          assumption.
      intros. rewrite hqs_In, filter_In in H; auto. destruct H.
        destruct (leqb_spec x h); intuition.
Qed.

Instance Sort_hqs (n : nat) (A : LinDec) (s : Sort A) : Sort A :=
{
    sort := hqs n A (@sort A s)
}.
Proof.
  intros. apply hqs_sorted.
  intros. apply hqs_perm.
Defined.*)

(** [uqs] specification *)

Theorem uqs_perm :
  forall
    (A : LinDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A) (l : list A),
      perm A l (uqs adhoc choosePivot partition l).
Proof.
  intros.
  functional induction @uqs A small adhoc choosePivot partition l.
    pose (e' := e). apply small_inl in e'; subst.
      apply adhoc_perm in e. assumption.
    assert (perm A l (pivot :: rest)).
      apply small_inr in e. apply pivot_spec in e0.
        apply Permutation_perm. rewrite e, e0. reflexivity.
      rewrite H. apply perm_symm. eapply perm_trans.
        apply perm_front. apply perm_cons. unfold perm in *. intro.
          rewrite !count_app, <- IHl0, <- IHl1; trivial.
            destruct partition. cbn in *. clear IHl0 IHl1.
              specialize (partition_perm _ _ _ _ _ e1).
              rewrite partition_perm, !count_app. reflexivity.
Qed.

Theorem uqs_In :
  forall
    (A : LinDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A)
    (l : list A) (x : A),
      In x (uqs adhoc choosePivot partition l) <->
      In x l.
Proof.
  intros. rewrite !count_In, <- uqs_perm; auto. reflexivity.
Qed.

Theorem uqs_sorted :
  forall
    (A : LinDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A) (l : list A),
      sorted A (uqs adhoc choosePivot partition l).
Proof.
  intros.
  functional induction @uqs A small adhoc choosePivot partition l.
    pose (e' := e). apply small_inl in e'; subst.
      apply adhoc_sorted in e. assumption.
    apply small_inr in e. apply pivot_spec in e0.
      apply sorted_app_all; auto.
        apply sorted_cons.
          intros. apply in_app_or in H. destruct H.
            erewrite spec_eq; eauto.
            eapply spec_hi; eauto. eapply uqs_In; eauto.
          apply sorted_app; auto.
            assert (forall x : A, In x eq -> x = pivot).
              eapply spec_eq; eauto.
              clear e1. induction eq; auto. destruct eq; auto. constructor.
                rewrite (H a), (H c); cbn; auto.
                apply IHeq. intro. inv 1; apply H; cbn; auto.
            intros. apply uqs_In in H0.
              erewrite (spec_eq pivot) at 1; eauto.
                eapply spec_hi; eauto.
          intros. apply uqs_In in H. eapply spec_lo; eauto.
Qed.

Instance Sort_uqs
  (A : LinDec) (small : Small A) (adhoc : AdHocSort small)
  (choosePivot : Pivot A) (partition : Partition A) : Sort A :=
{
    sort := uqs adhoc choosePivot partition
}.
Proof.
  intros. apply uqs_sorted.
  intros. apply uqs_perm.
Defined.

Instance Sort_qs (A : LinDec) : Sort A :=
{
    sort := qs A
}.
Proof.
  intros. apply uqs_sorted.
  intros. apply uqs_perm.
Defined.

Instance Sort_qs2 (A : LinDec) : Sort A :=
{
    sort := qs2 A
}.
Proof.
  intros. apply uqs_sorted.
  intros. apply uqs_perm.
Defined.

Instance Sort_hqs (A : LinDec) (n : nat) (s : Sort A) : Sort A :=
{
    sort := hqs n s
}.
Proof.
  apply uqs_sorted.
  apply uqs_perm.
Defined.