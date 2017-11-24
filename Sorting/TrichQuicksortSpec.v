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
        Search ((_, _) = (_, _)).
        destruct (filter
          (fun x : @carrier A => @LinDec_eqb (TrichDec_to_LinDec A) x h) t).
          cbn. assumption.
          cbn.
Admitted. (* TODO *)

(* TODO Instance Sort_htqs (n : nat) (s : Sort) : Sort :=
{
    TODO sort := fun A : TrichDec => htqs n A (@sort s A)
}.
Proof.
  intros. apply htqs_sorted.
  intros. apply htqs_perm.
Defined.*)