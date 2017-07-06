Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import SelectionSort.

Set Implicit Arguments.

Lemma min_split :
  forall (A : LinDec) (h : A) (t : list A),
    exists l1 l2 : list A, h :: t = l1 ++ min_dflt A h t :: l2.
Proof.
  induction t as [| h' t']; intros.
    exists [], []. simpl. reflexivity.
    simpl. dec.
      exists [h], t'. simpl. reflexivity.
      destruct IHt' as [l1 [l2 H]]. destruct l1.
        simpl in *. exists [], (h' :: t'). simpl. inversion H.
          rewrite <- H2; do 2 rewrite <- H1. reflexivity.
        exists (h :: h' :: l1), l2. simpl. do 2 f_equal.
          inversion H. rewrite <- H2. assumption.
Qed.

Lemma min_split' :
  forall (A : LinDec) (h : A) (t : list A),
    exists l1 l2 : list A, h :: t = l1 ++ min_dflt A h t :: l2 /\
      l1 ++ l2 = remove_once (min_dflt A h t) (h :: t).
Proof.
  induction t as [| h' t']; intros.
    exists [], []. simpl. dec.
    simpl. dec; subst; simpl.
      exists [h], t'. simpl. auto.
      rewrite e. exists [], (h' :: t'). simpl. auto.
      exists [h], t'. simpl. auto.
      exists [h], t'. simpl. auto.
      destruct IHt' as [l1 [l2 [H H']]]. destruct l1.
        inversion H. rewrite <- H1 in n. contradiction.
        exists (h :: h' :: l1), l2. simpl. split.
          do 2 f_equal. inversion H. rewrite <- H2. assumption.
          do 2 f_equal. simpl in H'.
            destruct (LinDec_eqb_spec A (min_dflt A h t') h).
              rewrite e in n. contradiction.
              inversion H'. reflexivity.
Qed.

Lemma perm_min_front :
  forall (A : LinDec) (h : A) (t : list A),
    let m := min_dflt A h t in
      perm A (m :: remove_once m (h :: t)) (h :: t).
Proof.
  intros. destruct (min_split' A h t) as [l1 [l2 [H H']]]. fold m in H, H'.
  rewrite H at 2. rewrite <- H'. apply perm_symm. apply perm_front.
Qed.

Theorem ssFun_perm :
  forall (A : LinDec) (l : list A), perm A l (ssFun A l).
Proof.
  intro. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intro IH; rewrite ssFun_equation.
      apply perm_refl.
      destruct (min_split' A h t) as [l1 [l2 [H H']]].
      rewrite <- H', H. eapply perm_trans.
        apply perm_front.
        apply perm_cons. apply IH. rewrite H. unfold lengthOrder.
          do 2 rewrite app_length. simpl. omega.
Qed.

Lemma remove_once_cons:
  forall (A : LinDec) (h : A) (t : list A), min_dflt A h t <> h ->
    lengthOrder (h :: remove_once (min_dflt A h t) t) (h :: t).
Proof.
  intros. replace (h :: remove_once (min_dflt A h t) t) with
    (remove_once (min_dflt A h t) (h :: t)).
    apply remove_once_min_lengthOrder.
    simpl. dec. rewrite e in H. contradiction.
Qed.

Lemma remove_once_In :
  forall (A : LinDec) (x h : A) (t : list A),
    In x t -> min_dflt A h t <> x -> In x (remove_once (min_dflt A h t) t).
Proof.
  induction t as [| h' t']; inversion 1; subst; intros.
    simpl in *. dec. rewrite e in H0. contradiction.
    simpl. dec. right. apply IHt'.
      assumption.
      simpl in *. destruct (leqb_spec h' (min_dflt A h t')).
        contradiction.
        assumption.
Qed.

(* TODO *) Lemma remove_once_In_conv :
  forall (A : LinDec) (x h : A) (t : list A),
    In x (remove_once (min_dflt A h t) t) -> In x t /\ min_dflt A h t <> x.
Proof.
  intros A x h t. generalize dependent h. generalize dependent x.
  induction t as [| h' t'].
    simpl. inversion 1.
    intros. simpl in H. destruct (leqb_spec h' (min_dflt A h t')). simpl.
Abort.

Lemma ssFun_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x l -> In x (ssFun A l).
Proof.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x l -> In x (ssFun A l))).
  destruct x0 as [| h t]; intro IH; inversion 1; subst;
  rewrite ssFun_equation.
    simpl. dec. right. apply IH.
      apply remove_once_cons. assumption.
      constructor. reflexivity.
    simpl. dec.
      right. apply IH.
        red; simpl; omega.
        assumption.
      destruct (LinDec_eqb_spec A x (min_dflt A h t)).
        left. auto.
        right. apply IH.
          apply remove_once_cons. assumption.
          simpl. right. apply remove_once_In; auto.
Qed.

Theorem ssFun_sorted : forall (A : LinDec) (l : list A),
  sorted A (ssFun A l).
Proof.
  intros. functional induction (ssFun A) l.
    constructor.
    case_eq (ssFun A (remove_once (min_dflt A h t) (h :: t))); intros.
      auto.
      constructor.
        Focus 2. rewrite <- H. assumption.
        Check min_In.
Restart.
  intros. functional induction (ssFun A) l.
    constructor.
    rewrite ssFun_equation.
      destruct (remove_once _ (h :: t)).
        auto.
Restart.
  intro. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intro IH.
      compute. constructor.
      rewrite ssFun_equation. 
        case_eq (ssFun A (remove_once (min_dflt A h t) (h :: t))); intros.
          auto.
          constructor.
            Focus 2.
Abort.