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

Require Import SelectionSort2.

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

Lemma min_Permutation :
  forall (A : LinDec) (l l' : list A),
    Permutation l l' -> min l = min l'.
Proof.
  induction 1; cbn; rewrite ?IHPermutation.
    reflexivity.
    destruct (min l'); dec.
    destruct (min l); f_equal; dec.
    congruence.
Qed.

Lemma lengthOrder_removeFirst_min :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m -> lengthOrder (removeFirst m l) l.
Proof.
  intros. functional induction min l; inv H; dec; red; cbn; try omega.
    apply lt_n_S. apply IHo. assumption.
Qed.

Lemma Permutation_removeFirst :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    Permutation l1 l2 ->
      Permutation (removeFirst x l1) (removeFirst x l2).
Proof.
  induction 1; cbn; dec.
    constructor.
    eapply Permutation_trans; eauto.
Qed.

Lemma removeFirst_sort :
  forall (A : LinDec) (s : Sort A) (x : A) (l : list A),
    removeFirst x (s l) = s (removeFirst x l).
Proof.
  induction l as [| h t]; cbn; intros.
    rewrite sort_nil. cbn. reflexivity.
    destruct (s (h :: t)) eqn: Heq.
      destruct s. cbn in *. specialize (sort_perm (h :: t)).
        rewrite Heq in sort_perm. apply perm_nil_cons in sort_perm.
          contradiction.
Abort.

Theorem sort_cons' :
  forall (A : LinDec) (s : Sort A) (l : list A),
    s l =
    match min l with
        | None => []
        | Some m => m :: s (removeFirst m l)
    end.
Proof.
  intros A s.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intros.
      cbn. apply sort_nil.
      assert (perm A (s (h :: t)) (h :: t)).
        rewrite <- sort_perm. reflexivity.
        destruct (s (h :: t)) eqn: Heq.
          symmetry in H0. apply perm_nil_cons in H0. contradiction.
          destruct (min (h :: t))  as [m |] eqn: Hm. assert (c = m).
            apply leq_antisym.
              2: admit.
              apply sorted_cons_conv' with l.
                rewrite <- Heq. apply sort_sorted.
                apply perm_In with (h :: t).
                  admit.
                  rewrite sort_perm, Heq. reflexivity.
            f_equal.
              assumption.
              Focus 2. cbn in Hm. destruct (min t); dec.
              subst. rewrite (H (removeFirst m (h :: t))).
                assert (Permutation (removeFirst m (h :: t))
                                    (removeFirst m (m :: l))).
                  apply Permutation_removeFirst. admit.
                  rewrite (min_Permutation _ H1). cbn. dec.
                    assert (l = removeFirst h (s (h :: t))).
                      admit.
Admitted.

Theorem sort_perm :
  forall (A : LinDec) (s : Sort A) (l l' : list A),
    Permutation l l' -> s l = s l'.
Proof.
  intros A s.
  apply (well_founded_ind (@lengthOrder_wf A)
    (fun l : list A => forall l' : list A, Permutation l l' -> s l = s l')).
  destruct x as [| h t]; cbn; intros.
    apply Permutation_nil in H0. rewrite H0. rewrite sort_nil. reflexivity.
    inv H0.
      rewrite !sort_cons'. cbn.
        rewrite <- (min_Permutation A H4). destruct (min t) eqn: Hc; dec.
          rewrite (H t) with l'0.
            reflexivity.
            red. cbn. omega.
            assumption.
          rewrite (H t) with l'0.
            reflexivity.
            red. cbn. omega.
            assumption.
          rewrite (H (h :: removeFirst c t)) with (h :: removeFirst c l'0).
            reflexivity.
            red. cbn. apply lt_n_S, lengthOrder_removeFirst_min.
              assumption.
              constructor. apply Permutation_removeFirst. assumption.
          rewrite (H t) with l'0; auto. red. cbn. omega.
        rewrite !sort_cons'. assert (Permutation (h :: x :: l) (x :: h :: l)).
          constructor.
          rewrite (min_Permutation _ H0). destruct (min (x :: h :: l)) eqn: Hc.
            2: reflexivity.
            f_equal. rewrite (H (removeFirst c (h :: x :: l))) with
                                (removeFirst c (x :: h :: l)).
              reflexivity.
              apply lengthOrder_removeFirst_min.
                rewrite (min_Permutation _ H0). assumption.
              apply Permutation_removeFirst. assumption.
        destruct l' as [| h' t'].
          rewrite H2 in H1. apply Permutation_length in H1. inv H1.
          rewrite !sort_cons'. rewrite H2 in H1.
            rewrite (min_Permutation A H1). destruct (min (h' :: t')) eqn: Hc.
              f_equal. rewrite (H (removeFirst c (h :: t)))
                          with (removeFirst c (h' :: t')).
                reflexivity.
                apply lengthOrder_removeFirst_min.
                  rewrite (min_Permutation _ H1). assumption.
                apply Permutation_removeFirst. assumption.
              reflexivity.
Qed.

Theorem sort_unique :
  forall (A : LinDec) (C C' : Sort A) (l : list A),
    @sort A C l = @sort A C' l.
Proof.
  intros A C C'. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; cbn; intros.
      rewrite !sort_nil. trivial.
      rewrite !sort_cons'. destruct (min (h :: t)) eqn: Hc. f_equal.
        apply H. apply lengthOrder_removeFirst_min. assumption.
        reflexivity.
Qed.

Theorem sort_idempotent :
  forall (A : LinDec) (s : Sort A) (l : list A),
    sort (sort l) = sort l.
Proof.
  intros. apply sort_perm. destruct s; cbn.
  apply perm_Permutation. rewrite <- sort_perm0. reflexivity.
Qed.