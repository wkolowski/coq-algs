Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import TrichQuicksort.

Set Implicit Arguments.

(* WUT *)

Theorem htqs_perm :
  forall (n : nat) (A : TrichDec) (s : Sort) (l : list A),
    perm A l (htqs n A sort l).
Proof.
  intros. functional induction htqs n A sort l; trivial.
    destruct s; cbn. apply sort_perm.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro.
        rewrite count_app, <- IHl0, <- IHl1.
        rewrite bifilter_spec in e1; inversion_clear e1.
        rewrite <- count_filter. auto.
Qed.

Theorem htqs_In :
  forall (n : nat) (A : TrichDec) (s : Sort) (x : A) (l : list A),
    In x (htqs n A sort l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- htqs_perm; auto. reflexivity.
Qed.

Theorem htqs_sorted :
  forall (n : nat) (A : TrichDec) (s : Sort) (l : list A),
    sorted A (htqs n A sort l).
Proof.
  intros. functional induction htqs n A sort l; trivial.
    destruct s; cbn. apply sort_sorted.
    rewrite bifilter_spec in e1; inversion e1; subst. apply sorted_app_all.
      assumption.
       apply sorted_cons.
        intros. rewrite htqs_In, filter_In in H; auto. destruct H.
          destruct (leqb_spec x h).
            inversion H0.
            apply TrichDec_not_leq. assumption.
          assumption.
      intros. rewrite htqs_In, filter_In in H; auto. destruct H.
        destruct (leqb_spec x h); intuition.
Qed.

Instance Sort_htqs (n : nat) (s : Sort) : Sort :=
{
    sort := fun A : TrichDec => htqs n A (@sort s A)
}.
Proof.
  intros. apply htqs_sorted.
  intros. apply htqs_perm.
Defined.