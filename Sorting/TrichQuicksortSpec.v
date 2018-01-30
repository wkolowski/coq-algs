Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import TrichQuicksort.
Require Import Sorting.Perm.

Set Implicit Arguments.

Theorem htqs_perm :
  forall (n : nat) (A : TrichDec) (s : Sort) (l : list A),
    perm A l (htqs n A sort l).
Proof.
  intros. functional induction htqs n A (@sort s A) l; trivial.
    destruct s; cbn. apply sort_perm.
    apply perm_symm. eapply perm_trans.
      apply perm_front.
      apply perm_cons. unfold perm in *. intro.
        rewrite !count_app, <- IHl0, <- IHl1.
        apply trifilter_spec' in e1; inv e1.
        red in H. specialize (H x). rewrite count_app in H.
        rewrite plus_assoc, H.
        replace (fun x0 : A => h <? x0) with
                (fun x0 : A => negb (x0 <=? h)).
          rewrite <- !count_filter. trivial.
          ext x0. rewrite ltb_negb_leqb. trivial.
Qed.

Theorem htqs_In :
  forall (n : nat) (A : TrichDec) (s : Sort) (x : A) (l : list A),
    In x (htqs n A sort l) <-> In x l.
Proof.
  intros. rewrite !count_In, <- htqs_perm; auto. reflexivity.
Qed.

Lemma list_ind2 :
  forall (A : Type) (P : list A -> Prop),
    P [] -> (forall x : A, P [x]) ->
    (forall (h1 h2 : A) (t : list A), P t -> P (h1 :: h2 :: t)) ->
      forall l : list A, P l.
Proof.
  fix 6. destruct l as [| h1 [| h2 t]]; auto.
  apply H1. apply list_ind2; auto.
Qed.

Lemma filter_eqb_repeat :
  forall (A : LinDec) (x : A) (l : list A),
    exists n : nat, filter (fun x' : A => x' =? x) l = repeat x n.
Proof.
  induction l as [| h t]; cbn.
    exists 0. reflexivity.
    dec. destruct IHt as [n H]. exists (S n). cbn. rewrite H. reflexivity.
Qed.

Lemma repeat_sorted :
  forall (A : LinDec) (x : A) (n : nat),
    sorted A (repeat x n).
Proof.
  induction n as [| n']; cbn.
    constructor.
    destruct n'; cbn; constructor; auto.
Qed.

Lemma filter_eqb_sorted :
  forall (A : LinDec) (x : A) (l : list A),
    sorted A (filter (fun x' : A => x' =? x) l).
Proof.
  intros. destruct (filter_eqb_repeat A x l) as [n H].
  rewrite H. apply repeat_sorted.
Qed.

Theorem htqs_sorted :
  forall (n : nat) (A : TrichDec) (s : Sort) (l : list A),
    sorted A (htqs n A sort l).
Proof.
  intros. functional induction htqs n A (@sort s A) l; trivial.
    destruct s; cbn. apply sort_sorted.
    rewrite trifilter_spec in e1; inv e1. apply sorted_app_all.
      assumption.
      apply sorted_cons; intros.
        apply in_app_or in H. destruct H.
          rewrite filter_In in H. destruct H. dec.
          rewrite htqs_In, filter_In in H. destruct H.
            unfold TrichDec_ltb in H0. case_eq (h <?> x); intro;
            rewrite H1 in H0; trich.
        apply sorted_app; auto.
          apply filter_eqb_sorted.
          intros. rewrite filter_In in H. destruct H. eapply perm_In in H0.
            Focus 2. rewrite <- htqs_perm. reflexivity.
            apply filter_In in H0. destruct H0.
              unfold TrichDec_ltb in H2; case_eq (h <?> y); intro;
                rewrite H3 in H2; trich.
      intros. eapply perm_In in H.
        Focus 2. rewrite <- htqs_perm. reflexivity.
        apply filter_In in H. destruct H.
          unfold TrichDec_ltb in H0; case_eq (x <?> h); intro;
          rewrite H1 in H0; trich.
Qed.

(*Instance Sort_htqs (n : nat) (s : Sort) : Sort :=
{
    sort := fun A : TrichDec => htqs n A (@sort s A)
}.
Proof.
  intros. apply htqs_sorted.
  intros. apply htqs_perm.
Defined.*)