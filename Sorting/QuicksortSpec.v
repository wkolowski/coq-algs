Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import QuickSort.

Require Import InsertionSort.

Set Implicit Arguments.

Theorem qs_perm :
  forall (A : LinDec) (l : list A), perm A l (qs A l).
Proof.
  intros. functional induction qs A l.
    auto.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro.
        rewrite count_app, <- IHl0, <- IHl1, <- count_filter. auto.
Qed.

Theorem qs_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (qs A l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- qs_perm. reflexivity.
Qed.

Theorem qs_sorted :
  forall (A : LinDec) (l : list A), sorted A (qs A l).
Proof.
  intros. functional induction qs A l.
    constructor.
    apply sorted_app_all.
      assumption.
      apply sorted_cons.
        intros. rewrite qs_In, filter_In in H. destruct H.
          destruct (leqb_spec x h).
            inversion H0.
            apply LinDec_not_leq. assumption.
          assumption.
      intros. rewrite qs_In, filter_In in H. destruct H.
        destruct (leqb_spec x h); intuition.
Qed.

Instance Sort_qs : Sort :=
{
    sort := qs;
    sort_sorted := qs_sorted;
    sort_perm := qs_perm;
}.

Theorem qs2_is_qs :
  forall (A : LinDec) (l : list A), qs2 A l = qs A l.
Proof.
  intros. functional induction qs2 A l.
    compute. trivial.
    rewrite qs_equation. rewrite bifilter_spec in e0.
      inversion e0. rewrite H0, H1. congruence.
Qed.

Instance Sort_qs2 : Sort :=
{
    sort := qs2
}.
Proof.
  all: intros; rewrite qs2_is_qs.
    apply (@sort_sorted Sort_qs).
    apply (@sort_perm Sort_qs).
Defined.

Theorem hqs_perm :
  forall (n : nat) (A : LinDec) (s : Sort) (l : list A),
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
  forall (n : nat) (A : LinDec) (s : Sort) (x : A) (l : list A),
    In x (hqs n A sort l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- hqs_perm; auto. reflexivity.
Qed.

Theorem hqs_sorted :
  forall (n : nat) (A : LinDec) (s : Sort) (l : list A),
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

Instance Sort_hqs (n : nat) (s : Sort) : Sort :=
{
    sort := fun A : LinDec => hqs n A (@sort s A)
}.
Proof.
  intros. apply hqs_sorted.
  intros. apply hqs_perm.
Defined.

Theorem ghqs_perm :
  forall (n : nat) (A : LinDec) (s : Sort) (p : Partition A) (l : list A),
    perm A l (ghqs n A (@sort s A) p l).
Proof.
  intros. functional induction ghqs n A (@sort s A) p l; trivial.
    destruct s; cbn. apply sort_perm.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro.
        rewrite !count_app, <- IHl0, <- IHl1.
        destruct p. cbn in *.
Admitted.

Theorem ghqs_In :
  forall (n : nat) (A : LinDec) (s : Sort) (p : Partition A)
    (x : A) (l : list A),
      In x (ghqs n A (@sort s A) p l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- ghqs_perm; auto. reflexivity.
Qed.

Theorem ghqs_sorted :
  forall (n : nat) (A : LinDec) (s : Sort) (p : Partition A) (l : list A),
    sorted A (ghqs n A (@sort s A) p l).
Proof.
  intros. functional induction ghqs n A (@sort s A) p l; trivial.
    destruct s; cbn. apply sort_sorted.
    (* TODO *) apply sorted_app_all.
      assumption.
       apply sorted_cons.
        intros.
Abort.
(* rewrite hqs_In, filter_In in H; auto. destruct H.
          destruct (leqb_spec x h).
            inversion H0.
            apply LinDec_not_leq. assumption.
          assumption.
      intros. rewrite hqs_In, filter_In in H; auto. destruct H.
        destruct (leqb_spec x h); intuition.
Qed.*)