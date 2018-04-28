Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export Sorting.Sort.
Require Export ListLemmas.

Set Implicit Arguments.

(* Properties of sorting *)
Theorem sort_nil :
  forall (A : LinDec) (s : Sort A), s [] = [].
Proof.
  intros. assert (perm A [] (sort [])) by (destruct s; auto).
  red in H. cbn in H. destruct (sort []).
    auto.
    specialize (H c). cbn in H. dec.
Qed.

Theorem sort_cons :
  forall (A : LinDec) (C : Sort A) (h : A) (t : list A),
    let m := min_dflt A h t in
      @sort A C (h :: t) = m :: @sort A C (removeFirst m (h :: t)).
Proof.
  intros.
  assert (sorted A (sort (h :: t))) by (destruct C; auto).
  assert (perm A (h :: t) (sort (h :: t))) by (destruct C; auto).
  case_eq (sort (h :: t)); intros.
    rewrite H1 in H0. red in H0; cbn in H0. specialize (H0 h). dec.
    rewrite H1 in H. assert (min_dflt A h t ≤ c).
      apply min_spec. eapply (perm_In A c (c :: l) (h :: t)).
        cbn. auto.
        rewrite <- H1. auto.
      fold m in H2. assert (c ≤ m).
        eapply sorted_cons_conv'; eauto. rewrite <- H1.
          apply perm_In with (h :: t); auto. apply min_In.
        assert (c = m) by auto; subst. f_equal.
          assert (H4 := perm_min_front A h t). unfold m in H4. fold m in H4.
            assert (perm A (C (h :: t)) (m :: removeFirst m (h :: t))).
              eapply perm_trans.
                rewrite <- H0. reflexivity.
                rewrite H4. reflexivity.
          rewrite H1 in H5. assert (perm A l (removeFirst m (h :: t))).
            red. intros. red in H5. specialize (H5 x). cbn in H5. dec.
Restart.
  intros A C h. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    intros.
Restart.
  intros A C h. destruct C; cbn in *.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    intros. rename x into t. case_eq (sort (h :: t)); intros.
      assert (perm A (sort (h :: t)) []).
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
Admitted. (* TODO *)

Require Import SelectionSort2.

Theorem sort_cons' :
  forall (A : LinDec) (s : Sort A) (l : list A),
    s l =
    match min l with
        | None => []
        | Some m => m :: s (removeFirst m l)
    end.
Proof.
  intros. functional induction min l.
    rewrite sort_nil. reflexivity.
    specialize (IHo s). destruct (min t).
      inv e0.
      destruct s; cbn in *. specialize (sort_perm t).
        rewrite IHo in sort_perm. Search (perm _ _ _).
Abort.

Theorem sort_unique :
  forall (A : LinDec) (C C' : Sort A) (l : list A),
    @sort A C l = @sort A C' l.
Proof.
  intros A C C'. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; cbn; intros.
      rewrite !sort_nil. trivial.
      rewrite !sort_cons. f_equal. apply H; dec.
        red; cbn. omega.
        apply removeFirst_cons. assumption.
Qed.

Lemma min_dflt_Permutation :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    Permutation l1 l2 -> min_dflt A x l1 = min_dflt A x l2.
Proof.
  induction 1; cbn; dec.
    unfold min_dflt in *. rewrite IHPermutation in l0.
      contradiction.
    unfold min_dflt in *. rewrite IHPermutation in n.
      contradiction.
Qed.

Theorem sort_perm :
  forall (A : LinDec) (s : Sort A) (l l' : list A),
    perm A l l' -> s l = s l'.
Proof.
  intros. apply perm_Permutation in H. induction H.
    reflexivity.
    Focus 3. congruence.
    rewrite !sort_cons. assert (min_dflt A x l = min_dflt A x l').
      apply min_dflt_Permutation. assumption.
      rewrite !H0. f_equal. cbn. dec.
Admitted. (* TODO *)

Theorem sort_idempotent :
  forall (A : LinDec) (s : Sort A) (l : list A),
    sort (sort l) = sort l.
Proof.
  intros. apply sort_perm. destruct s; cbn.
  rewrite <- sort_perm0. reflexivity.
Qed.