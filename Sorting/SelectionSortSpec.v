Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import SelectionSort.

Set Implicit Arguments.

Lemma ss_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (ss A l) <-> In x l.
Proof.
  split; functional induction ss A l; intros; auto.
    destruct H; subst.
      apply min_In.
      destruct (min_split A h t) as [l1 [l2 [H1 H2]]].
        rewrite <- H2 in *.
          pose (wut := IHl0 H). rewrite H1. apply in_or_app.
            destruct (@in_app_or _ _ _ _ wut); [left | do 2 right]; auto.
    cbn in *. destruct H; dec.
      right. apply IHl0. left. auto.
      destruct (LinDec_eqb_spec A x (min_dflt A h t)).
        left. auto.
        right. apply IHl0.
          simpl. right. apply remove_once_In; auto.
Qed.

Theorem ss_sorted :
  forall (A : LinDec) (l : list A), sorted A (ss A l).
Proof.
  intros. functional induction ss A l.
    constructor.
    case_eq (ss A (remove_once (min_dflt A h t) (h :: t))); intros.
      auto.
      constructor.
        assert (In c (ss A (remove_once (min_dflt A h t) (h :: t)))).
          rewrite H. left. reflexivity.
          rewrite ss_In in H0. apply min_spec.
          apply remove_once_In_conv in H0. assumption.
        rewrite <- H. assumption.
Qed.

Theorem ss_perm :
  forall (A : LinDec) (l : list A), perm A l (ss A l).
Proof.
  intros. functional induction ss A l.
    auto.
    destruct (min_split A h t) as [l1 [l2 [H H']]].
      rewrite <- H', H in *. eapply perm_trans.
        apply perm_front.
        apply perm_cons. apply IHl0.
Qed.

Instance Sort_ss : Sort :=
{
    sort := ss;
    sort_sorted := ss_sorted;
    sort_perm := ss_perm
}.