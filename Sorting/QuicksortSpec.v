Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import QuickSort.

Set Implicit Arguments.

Theorem qsFun_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (qsFun A l) <-> In x l.
Proof.
  split; generalize dependent l.
    apply (well_founded_ind (@lengthOrder_wf A)
      (fun l : list A => In x (qsFun A l) -> In x l)).
      destruct x0 as [| h t]; intro IH.
        inversion 1.
        intro. rewrite qsFun_equation in H. apply in_app_or in H.
          apply filter_In_app with (fun x : A=> x <=? h).
          destruct H.
            apply in_or_app. simpl. dec.
              left. right. apply IH.
                apply filter_lengthOrder.
                assumption.
              contradiction n. auto.
            inversion H.
              apply in_or_app. left. dec. contradiction n. auto.
              dec.
                right. apply in_or_app. right. apply IH.
                  apply filter_lengthOrder.
                  assumption.
                contradiction n. auto.
    apply (well_founded_ind (@lengthOrder_wf A)
      (fun l : list A => In x l -> In x (qsFun A l))).
      destruct x0 as [| h t]; intro IH.
        inversion 1.
        intro. rewrite qsFun_equation. apply in_or_app.
          destruct (LinDec_eqb_spec _ x h); subst.
            right. left. reflexivity.
            case_eq (x <=? h); intros.
              left. apply IH.
                apply filter_lengthOrder.
                rewrite filter_In. inversion H; subst; intuition.
              right. right. apply IH.
                apply filter_lengthOrder.
                rewrite filter_In. inversion H; subst; intuition.
                  rewrite H0. simpl. trivial.
Restart.
  split; functional induction (qsFun A) l; auto.
    intros H %in_app_or. destruct (LinDec_eqb_spec _ x h); subst.
      left. auto.
      right. apply filter_In_app with (fun x : A=> x <=? h).
        apply in_or_app. destruct H.
          left. apply IHl0. assumption.
          right. apply IHl1. inversion H; subst; intuition.
    intro. apply in_or_app. inversion H; subst.
      right. left. auto.
      case_eq (x <=? h); intros.
        left. apply IHl0, filter_In. auto.
        right. right. apply IHl1, filter_In. rewrite H1. auto.
Qed.

Theorem qsFun_sorted :
  forall (A : LinDec) (l : list A), sorted A (qsFun A l).
Proof.
  intros. functional induction (@qsFun A) l.
    constructor.
    apply sorted_app_all.
      assumption.
      Focus 2. intros. rewrite qsFun_In, filter_In in H. destruct H.
        destruct (leqb_spec x h); intuition.
      apply sorted_cons.
        intros. rewrite qsFun_In, filter_In in H. destruct H.
          destruct (leqb_spec x h).
            inversion H0.
            apply LinDec_not_leq. assumption.
          assumption.
Qed.

Hint Resolve filter_lengthOrder.

Theorem qsFun_perm :
  forall (A : LinDec) (l : list A), perm A l (qsFun A l).
Proof.
  unfold perm. intros A l x. generalize dependent l.
  apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => count A x l = count A x (qsFun A l))).
  destruct x0 as [| h t]; intro IH.
    compute. reflexivity.
    rewrite qsFun_equation. rewrite count_app. simpl. dec.
      repeat rewrite <- IH; auto. rewrite (count_filter A h h). omega.
      repeat rewrite <- IH; auto. erewrite count_filter. reflexivity.
Restart.
  intros A l. functional induction (qsFun A) l.
    auto.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro. rewrite count_app.
        rewrite <- IHl0, <- IHl1. rewrite <- count_filter. auto.
Qed.

Instance Sort_qsFun : Sort :=
{
    sort := qsFun;
    sort_sorted := qsFun_sorted;
    sort_perm := qsFun_perm;
}.