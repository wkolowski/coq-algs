Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import SelectionSort.

Set Implicit Arguments.

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

Lemma ss_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (ss A l) <-> In x l.
Proof.
  intros. rewrite !count_In. rewrite <- ss_perm. reflexivity.
Qed.

Theorem ss_sorted :
  forall (A : LinDec) (l : list A), sorted A (ss A l).
Proof.
  intros. functional induction ss A l.
    constructor.
    case_eq (ss A (removeFirst (min_dflt A h t) (h :: t))); intros.
      auto.
      constructor.
        assert (In c (ss A (removeFirst (min_dflt A h t) (h :: t)))).
          rewrite H. left. reflexivity.
          rewrite ss_In in H0. apply min_spec.
          apply removeFirst_In_conv in H0. assumption.
        rewrite <- H. assumption.
Qed.

Instance Sort_ss (A : LinDec) : Sort A :=
{
    sort := @ss A;
    sort_sorted := ss_sorted A;
    sort_perm := ss_perm A
}.