Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.
Require Export ListLemmas.

Set Implicit Arguments.

(* Properties of sorting *)
Theorem sort_nil :
  forall (A : LinDec) (C : Sort), @sort C A [] = [].
Proof.
  intros. assert (perm A [] (sort [])) by (destruct C; auto).
  red in H. simpl in H. destruct (sort []).
    auto.
    specialize (H c). simpl in H. dec.
Qed.

Theorem sort_cons :
  forall (A : LinDec) (C : Sort) (h : A) (t : list A),
    let m := min_dflt A h t in
      @sort C A (h :: t) = m :: @sort C A (remove_once m (h :: t)).
Proof.
  intros. assert (sorted A (sort (h :: t))) by (destruct C; auto).
  case_eq (sort (h :: t)); intros.
    assert (perm A (h :: t) (sort (h :: t))) by (destruct C; auto).
      rewrite H0 in H1. red in H1; simpl in H1. specialize (H1 h). dec.
    rewrite H0 in H. Check sorted_cons_conv.
      assert (wut := sorted_cons_conv A c l H).
Restart.
  intros A C h. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    intros.
Restart.
  intros A C h. destruct C; cbn in *.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    intros. rename x into t. case_eq (sort A (h :: t)); intros.
      assert (perm A (sort A (h :: t)) []).
        rewrite H0. reflexivity.
        rewrite <- sort_perm in H1. specialize (H1 h). cbn in H1. dec.
      f_equal.
        apply leq_antisym.
          apply sorted_cons_conv' with l.
            rewrite <- H0. apply sort_sorted.
            apply perm_In with (h :: t).
              apply min_In.
              rewrite sort_perm. rewrite H0. reflexivity.
          apply (min_spec A c h t). apply perm_In with (c :: l).
            left. trivial.
            symmetry. rewrite sort_perm, H0. reflexivity.
      dec.
        Focus 2.
Admitted.

Theorem sort_metaspec :
  forall (A : LinDec) (C C' : Sort) (l : list A),
    @sort C A l = @sort C' A l.
Proof.
  intros A C C'. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; cbn; intros.
      rewrite !sort_nil. trivial.
      rewrite !sort_cons. f_equal. apply H; dec.
        red; cbn. omega.
        apply remove_once_cons. assumption.
Qed.