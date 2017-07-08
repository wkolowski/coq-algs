Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import MergeSort.

Set Implicit Arguments.

(* TODO *) Theorem merge_sorted : forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 -> sorted A (merge A l1 l2).
Proof.
  intros A l1 l2 H. generalize dependent l2.
  induction H.
    destruct l2; auto.
    induction 1; simpl in *; dec.
    induction 1.
      simpl. auto.
      specialize (IHsorted _ (sorted1 A x0)). simpl in *. dec.
      simpl.
Restart.
  induction l1 as [| h1 t1].
    destruct l2; simpl; auto.
    destruct l2; simpl; auto.
      dec; intros.
        
    
Abort.

Lemma merge_In :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    In x (merge A l1 l2) <-> In x (l1 ++ l2).
Proof.
Admitted.

Theorem msFun_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (msFun A l) -> In x l.
Proof.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x (msFun A l) -> In x l)).
  destruct x0 as [| h t]; intro IH.
    inversion 1.
    intro. rewrite msFun_equation in H. destruct t.
      assumption.
      apply merge_In in H. apply in_app_or in H. destruct H.
        apply IH in H.
          eapply take_In. eassumption.
          apply take_length_lt. apply lt_div2. simpl. omega.
        apply IH in H.
          eapply drop_In. eassumption.
          apply drop_length_lt; simpl; intuition. inversion H0.
Qed.

Theorem msFun_In_conv :
  forall (A : LinDec) (x : A) (l : list A),
   In x l -> In x (msFun A l).
Proof.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x l -> In x (msFun A l))).
  destruct x0 as [| h t]; intro IH.
    inversion 1.
    intro. rewrite msFun_equation. destruct t.
      assumption.
      rewrite merge_In. apply in_or_app. destruct (LinDec_eqb_spec _ x h).
        left. apply IH.
          apply take_length_lt. apply lt_div2. simpl. omega.
          simpl. auto.
        inversion H; subst.
          contradiction.
          apply IH in H0.
            Focus 2. red; simpl; omega.
            apply msFun_In in H0.
            apply IH in H0. rewrite msFun_equation in H0. destruct t.
              simpl. right. auto.
              rewrite merge_In in H0. apply in_app_or in H0. destruct H0.
                left. apply IH.
                  apply take_length_lt. apply lt_div2. simpl. omega.
Restart.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x l -> In x (msFun A l))).
  destruct x0 as [| h t]; intro IH.
    inversion 1.
    intro. rewrite msFun_equation. destruct t.
      assumption.
      rewrite merge_In. apply in_or_app. inversion H; subst.
        left. apply IH.
          apply take_length_lt. apply lt_div2. simpl; omega.
          simpl. auto.
        inversion H0; subst.
          destruct t using list_ind2; auto.
            right. rewrite msFun_equation. simpl. dec.
            left. apply IH.
              apply take_length_lt. apply lt_div2. simpl; omega.
              simpl. auto.
          apply IH in H1.
            Focus 2. red; simpl; omega.
            rewrite msFun_equation in H1. destruct t using list_ind2.
              Focus 3.
Restart.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x l -> In x (msFun A l))).
  destruct x0 using list_ind2; intro IH; simpl; destruct 1; subst; auto.
    rewrite msFun_equation. rewrite merge_In. apply in_or_app. left.
      apply IH.
        apply take_length_lt. apply lt_div2. simpl; omega.
        simpl. auto.
    destruct H; subst.
      rewrite msFun_equation. rewrite merge_In. apply in_or_app.
        destruct x1 using list_ind2.
          right. simpl. auto.
          right. simpl. rewrite msFun_equation. dec.
          left. apply IH.
            apply take_length_lt. apply lt_div2. simpl; omega.
            simpl. auto.
      rewrite msFun_equation. rewrite merge_In. apply in_or_app.
        destruct x1 using list_ind2.
          inversion H.
          simpl in H. destruct H; inversion H; subst. right. simpl.
            rewrite msFun_equation. dec.
          clear IHx1. apply IH in H.
            Focus 2. red; simpl; omega.
            rewrite msFun_equation, merge_In in H. apply in_app_or in H.
              destruct H.
                simpl in H. apply msFun_In in H. inversion H; subst.
Abort.