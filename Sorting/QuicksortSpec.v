Require Import QuickSort.

Set Implicit Arguments.

(** [uqs] specification *)

Lemma uqs_perm :
  forall
    (A : TrichDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A) (l : list A),
      perm l (uqs adhoc choosePivot partition l).
Proof.
  intros.
  functional induction @uqs A small adhoc choosePivot partition l.
    pose (e' := e). apply small_inl in e'; subst.
      apply adhoc_perm in e. assumption.
    assert (perm l (pivot :: rest)).
      apply small_inr in e. apply pivot_spec in e0.
        apply Permutation_perm. rewrite e, e0. reflexivity.
      rewrite H. apply perm_symm. eapply perm_trans.
        apply perm_front. apply perm_cons. unfold perm in *. intro.
          rewrite !count_app, <- IHl0, <- IHl1; trivial.
            destruct partition. cbn in *. clear IHl0 IHl1.
              specialize (partition_perm _ _ _ _ _ e1).
              rewrite partition_perm, !count_app. reflexivity.
Qed.

Lemma Permutation_uqs :
  forall
    (A : TrichDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A) (l : list A),
      Permutation (uqs adhoc choosePivot partition l) l.
Proof.
  intros.
  functional induction @uqs A small adhoc choosePivot partition l.
    pose (e' := e). apply small_inl in e'; subst.
      apply adhoc_perm in e. apply perm_Permutation.
        rewrite <- e. reflexivity.
    assert (Permutation l (pivot :: rest)).
      apply small_inr in e. apply pivot_spec in e0.
        rewrite e, e0. reflexivity.
      rewrite H. eapply Permutation_trans.
        rewrite <- Permutation_middle. reflexivity.
        constructor. apply Permutation_partition in e1. rewrite <- e1.
          apply Permutation_app.
            assumption.
            apply Permutation_app.
              reflexivity.
              assumption.
Qed.

Lemma uqs_In :
  forall
    (A : TrichDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A)
    (l : list A) (x : A),
      In x (uqs adhoc choosePivot partition l) <->
      In x l.
Proof.
  intros.
  split; apply Permutation_in.
    apply Permutation_uqs.
    symmetry. apply Permutation_uqs.
Qed.

Lemma Sorted_uqs :
  forall
    (A : TrichDec) (small : Small A) (adhoc : AdHocSort small)
    (choosePivot : Pivot A) (partition : Partition A) (l : list A),
      Sorted A (uqs adhoc choosePivot partition l).
Proof.
  intros.
  functional induction @uqs A small adhoc choosePivot partition l.
    pose (e' := e). apply small_inl in e'; subst.
      apply Sorted_adhoc in e. assumption.
    apply small_inr in e. apply pivot_spec in e0.
      apply Sorted_app_all; auto.
        apply Sorted_cons.
          intros. apply in_app_or in H. destruct H.
            erewrite spec_eq; eauto.
            eapply spec_hi; eauto. eapply uqs_In; eauto.
          apply Sorted_app; auto.
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

#[refine]
Instance Sort_uqs
  (A : TrichDec) (small : Small A) (adhoc : AdHocSort small)
  (choosePivot : Pivot A) (partition : Partition A) : Sort A :=
{
    sort := uqs adhoc choosePivot partition
}.
Proof.
  intros. apply Sorted_uqs.
  intros. apply perm_Permutation. rewrite <- uqs_perm. reflexivity.
Defined.

#[refine]
Instance Sort_qs (A : TrichDec) : Sort A :=
{
    sort := qs A
}.
Proof.
  intros. apply Sorted_uqs.
  unfold qs. intros. apply perm_Permutation. rewrite <- uqs_perm.
    reflexivity.
Defined.

#[refine]
Instance Sort_qs2 (A : TrichDec) : Sort A :=
{
    sort := qs2 A
}.
Proof.
  intros. apply Sorted_uqs.
  unfold qs2. intros. apply perm_Permutation. rewrite <- uqs_perm.
    reflexivity.
Defined.

#[refine]
Instance Sort_hqs (A : TrichDec) (n : nat) (s : Sort A) : Sort A :=
{
    sort := hqs n A s
}.
Proof.
  apply Sorted_uqs.
  unfold hqs. intros. apply perm_Permutation. rewrite <- uqs_perm.
    reflexivity.
Defined.