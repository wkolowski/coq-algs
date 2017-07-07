Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import QuickSort.

Set Implicit Arguments.
Check qsFun_equation.
(*Lemma filter_complete :
  forall (A : LinDec) (h : A) (t : list A),
    perm A (h :: t) (filter (fun x : A => x <=? h) t ++ h ::
                     filter (fun x : A => negb (x <=? h)) t).
Proof.
  unfold perm. induction t as [| h' t'].
    simpl. reflexivity.
    simpl. dec.
Abort.*)

Lemma filter_In_app :
  forall (A : LinDec) (p : A -> bool) (x : A) (l : list A),
    In x (filter p l ++ filter (fun x => negb (p x)) l) -> In x l.
Proof.
  induction l as [| h t]; simpl.
    auto.
    destruct (p h); simpl.
      destruct 1; auto.
      intro. apply in_app_or in H. destruct H.
        right. apply IHt. apply in_or_app. auto.
        inversion H.
          subst. auto.
          right. apply IHt. apply in_or_app. auto.
Qed.

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
Abort.

Theorem qsFun_sorted :
  forall (A : LinDec) (l : list A), sorted A (qsFun A l).
Proof.
  intros. functional induction (@qsFun A) l.
    constructor.
    apply sorted_app_all.
      assumption.
      Focus 2. intros.
Abort.