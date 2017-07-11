Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import SelectionSort.

Set Implicit Arguments.

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

Lemma ssFun_In_conv :
  forall (A : LinDec) (x : A) (l : list A),
    In x (ssFun A l) -> In x l.
Proof.
  intros A x. apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => In x (ssFun A l) -> In x l)).
  destruct x0 as [| h t]; intro IH.
    inversion 1.
    rewrite ssFun_equation. inversion 1.
      rewrite <- H0. apply min_In.
      destruct (min_split A h t) as [l1 [l2 [H1 H2]]].
        rewrite <- H2 in *. assert (lengthOrder (l1 ++ l2) (h :: t)).
          rewrite H2. apply remove_once_min_lengthOrder.
          pose (wut := IH _ H3 H0). rewrite H1. apply in_or_app.
            destruct (@in_app_or _ _ _ _ wut); [left | do 2 right]; auto.
Qed.

Theorem ssFun_sorted :
  forall (A : LinDec) (l : list A), sorted A (ssFun A l).
Proof.
  intros. functional induction ssFun A l.
    constructor.
    case_eq (ssFun A (remove_once (min_dflt A h t) (h :: t))); intros.
      auto.
      constructor.
        assert (In c (ssFun A (remove_once (min_dflt A h t) (h :: t)))).
          rewrite H. left. reflexivity.
          apply ssFun_In_conv in H0. apply min_spec.
          apply remove_once_In_conv in H0. assumption.
        rewrite <- H. assumption.
Qed.

Theorem ssFun_perm :
  forall (A : LinDec) (l : list A), perm A l (ssFun A l).
Proof.
  intro. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intro IH; rewrite ssFun_equation.
      apply perm_refl.
      destruct (min_split A h t) as [l1 [l2 [H H']]].
      rewrite <- H', H. eapply perm_trans.
        apply perm_front.
        apply perm_cons. apply IH. rewrite H. unfold lengthOrder.
          rewrite 2 app_length. simpl. omega.
Restart.
  intros. functional induction ssFun A l.
    auto.
    destruct (min_split A h t) as [l1 [l2 [H H']]].
      rewrite <- H', H in *. eapply perm_trans.
        apply perm_front.
        apply perm_cons. apply IHl0.
Qed.

Instance Sort_ssFun : Sort :=
{
    sort := ssFun;
    sort_sorted := ssFun_sorted;
    sort_perm := ssFun_perm
}.