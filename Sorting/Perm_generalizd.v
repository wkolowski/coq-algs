Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export LinDec.

Require Export Sorting.ListLemmas.
Require Import TrichDec.

Require Import Classes.RelationClasses.
Require Import Permutation.

Fixpoint count {A : Type} (p : A -> bool) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => if p h then S (count p t) else count p t
end.

Definition perm {A : Type} (l1 l2 : list A) : Prop :=
  forall p : A -> bool, count p l1 = count p l2.

(* Lemmas about [count]. *)

Lemma count_app :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    count p (l1 ++ l2) = count p l1 + count p l2.
Proof.
  induction l1; cbn; intros.
    reflexivity.
    rewrite IHl1. destruct (p a); cbn; reflexivity.
Qed.

Lemma count_app_comm :
  forall (A : Type) (p : A -> bool) (l1 l2 : list A),
    count p (l1 ++ l2) = count p (l2 ++ l1).
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    rewrite app_nil_r. reflexivity.
    rewrite !count_app. cbn. destruct (p h1); omega.
Qed.

Lemma count_last :
  forall (A : Type) (p : A -> bool) (l : list A) (x : A),
    count p (l ++ [x]) = count p l + count p [x].
Proof.
  intros. rewrite count_app. reflexivity.
Qed.

Lemma count_reverse :
  forall (A : Type) (p : A -> bool) (l : list A),
    count p (rev l) = count p l.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite count_app, IHt. cbn. destruct (p h); omega.
Qed.

Lemma count_cons :
  forall (A : Type) (p : A -> bool) (h : A) (t : list A),
    p h = true -> count p (h :: t) = 1 + count p t.
Proof.
  intros. cbn. rewrite H. reflexivity.
Qed.

Lemma count_filter :
  forall (A : Type) (p : A -> bool) (t : list A),
    count p t = count p (filter p t) +
                count p (filter (fun x : A => negb (p x)) t).
Proof.
  induction t as [| h' t']; cbn.
    reflexivity.
    destruct (p h') eqn: H; cbn; rewrite ?H, ?IHt'; reflexivity.
Qed.

Lemma count_In :
  forall (A : Type) (p : A -> bool) (l : list A),
    Exists (fun x => p x = true) l <-> count p l <> 0.
Proof.
  split.
    induction 1; cbn.
      rewrite H. inv 1.
      destruct (p x).
        inv 1.
        assumption.
    induction l as [| h t]; cbn; intros.
      contradiction.
      destruct (p h) eqn: Hph.
        left. assumption.
        right. apply IHt, H.
Qed.

(*Lemma count_0_nil :
  forall (A : Type) (l : list A),
    (forall p : A -> bool, count p l = 0) -> l = [].
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    specialize (H h). dec.
Qed.*)

(* Lemmas about [perm]. *)
Lemma perm_refl :
  forall (A : Type) (l : list A), perm l l.
Proof. unfold perm; auto. Defined.

Lemma perm_sym :
  forall (A : Type) (l1 l2 : list A),
    perm l1 l2 -> perm l2 l1.
Proof. unfold perm; auto. Defined.

Lemma perm_trans :
  forall (A : Type) (l1 l2 l3 : list A),
    perm l1 l2 -> perm l2 l3 -> perm l1 l3.
Proof.
  unfold perm; intros. eapply eq_trans; auto.
Defined.

Hint Resolve perm_refl perm_sym.

Instance Equiv_perm (A : Type) : Equivalence (@perm A).
Proof.
  split; red; intros; eauto. eapply perm_trans; eauto.
Defined.

Lemma perm_cons :
  forall (A : Type) (x : A) (l1 l2 : list A),
    perm l1 l2 -> perm (x :: l1) (x :: l2).
Proof.
  unfold perm. intros. cbn. rewrite H. reflexivity.
Defined.

Lemma perm_nil_cons :
  forall (A : Type) (h : A) (t : list A),
    ~ perm (h :: t) [].
Proof.
  unfold not; intros. red in H.
  specialize (H (fun _ => true)).
  cbn in H. inv H.
Qed.

Lemma perm_swap :
  forall (A : Type) (x y : A) (l1 l2 : list A),
    perm l1 l2 -> perm (x :: y :: l1) (y :: x :: l2).
Proof.
  unfold perm; cbn; intros; destruct (p x), (p y);
  rewrite H; auto.
Defined.

Theorem perm_front :
  forall (A : Type) (x : A) (l1 l2 : list A),
    perm (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    apply perm_refl.
    eapply perm_trans with (h1 :: x :: t1 ++ l2).
      apply perm_cons. apply IHt1.
      apply perm_swap. apply perm_refl.
Qed.

Hint Resolve perm_refl perm_sym perm_cons perm_swap perm_front.

Lemma perm_app_comm :
  forall (A : Type) (l1 l2 : list A),
    perm (l1 ++ l2) (l2 ++ l1).
Proof.
  unfold perm. intros. apply count_app_comm.
Qed.

Lemma perm_app :
  forall (A : Type) (l1 l1' l2 l2' : list A),
    perm l1 l1' -> perm l2 l2' -> perm (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold perm; intros. rewrite 2 count_app, H, H0. auto.
Qed.

Require Import ListLemmas_generalized.

Lemma perm_In :
  forall (A : Type) (P : A -> Prop) (l l' : list A),
    Exists P l -> perm l l' -> Exists P l'.
Proof.
  induction 1; intro.
    destruct l'.
      apply perm_nil_cons in H0. contradiction.
      red in H0. cbn in H0. specialize (H0 p). rewrite H in H0.
          destruct (p a) eqn: Ha.
            left. assumption.
            right.

(* TODO: zostawić count, ale cofnąć perm *)
Abort. (*

rewrite count_In. red in H0. rewrite <- H0.
  rewrite <- count_In. assumption.
Qed.

Lemma perm_singl :
  forall (A : Type) (p : A -> bool) (l : list A),
    perm [x] l -> l = [x].
Proof.
  unfold perm; destruct l as [| h1 [| h2 t]]; cbn; intros.
    specialize (H x). dec.
    specialize (H x). dec.
    assert (H1 := H h1). assert (H2 := H h2). dec.
Qed.

Lemma perm_cons_inv :
  forall (A : Type) (h : A) (t1 t2 : list A),
    perm (h :: t1) (h :: t2) -> perm t1 t2.
Proof.
  unfold perm; intros. specialize (H x). cbn in H. dec.
Qed.

Lemma removeFirst_In_perm :
  forall (A : Type) (p : A -> bool) (l : list A),
    In x l -> perm l (x :: removeFirst x l).
Proof.
  induction l as [| h t]; cbn; inv 1; dec.
    specialize (IHt H0). rewrite <- perm_swap.
      apply perm_cons. exact IHt.
      reflexivity.
Qed.

Lemma perm_In' :
  forall (A : Type) (h : A) (t l : list A),
    perm (h :: t) l -> In h l.
Proof.
  intros. rewrite count_In. rewrite <- H. cbn. dec.
Defined.

Lemma count_removeFirst_neq :
  forall (A : Type) (x y : A) (l : list A),
    x <> y -> count p (removeFirst y l) = count p l.
Proof.
  induction l as [| h t]; cbn; intros; dec; dec.
Qed.

Lemma count_removeFirst_In :
  forall (A : Type) (p : A -> bool) (l : list A),
    In x l -> count p (removeFirst x l) = count p l - 1.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    firstorder (repeat dec).
Qed.

Lemma perm_removeFirst :
  forall (A : Type) (h h' : A) (t t' : list A),
    h <> h' -> perm (h :: t) (h' :: t') ->
      perm (h :: removeFirst h' t) t'.
Proof.
  intros. assert (In h' t).
    symmetry in H0. apply perm_In' in H0. cbn in H0. destruct H0.
      congruence.
      assumption.
    unfold perm. intro. destruct (x =? h) eqn: Heq; dec.
      rewrite count_removeFirst_neq.
        red in H0. specialize (H0 h). cbn in H0. dec.
        assumption.
      destruct (x =? h') eqn: Heq'; dec.
        rewrite count_removeFirst_In.
          red in H0. specialize (H0 h'). cbn in H0. dec.
          assumption.
        rewrite count_removeFirst_neq.
          red in H0. specialize (H0 x). cbn in H0. dec.
          assumption.
Qed.

Lemma perm_front_ex' :
  forall (A : Type) (h : A) (t l : list A),
    perm (h :: t) l -> exists l1 l2 : list A,
      l = l1 ++ h :: l2 /\ perm (l1 ++ l2) t.
Proof.
  intros A h t l. gen t; gen h.
  induction l as [| h' t']; cbn; intros.
    apply perm_nil_cons in H. contradiction.
    destruct (h =? h') eqn: Heq.
      dec. exists [], t'. cbn. split.
        reflexivity.
        apply perm_cons_inv in H. rewrite H. reflexivity.
      dec. assert (perm (h :: removeFirst h' t) t').
        apply perm_removeFirst; assumption.
        destruct (IHt' h (removeFirst h' t) H0) as (l1 & l2 & H1 & H2).
          clear IHt'. subst. exists (h' :: l1), l2. split.
            reflexivity.
            cbn. rewrite (removeFirst_In_perm h' t).
              apply perm_cons. assumption.
              rewrite app_comm_cons, perm_app_comm in H; cbn in H.
                apply perm_cons_inv in H. eapply perm_In.
                  Focus 2. rewrite H. reflexivity.
                  apply in_or_app. right. left. reflexivity.
Qed.

Theorem Permutation_perm :
  forall (A : Type) (l1 l2 : list A),
    Permutation l1 l2 -> perm l1 l2.
Proof.
  induction 1; cbn; intros; dec.
Qed.

Theorem perm_Permutation :
  forall (A : Type) (l1 l2 : list A),
    perm l1 l2 -> Permutation l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    destruct l2; cbn; auto. red in H. cbn in H. specialize (H c). dec.
    apply perm_front_ex' in H. destruct H as (l1 & l3 & H1 & H3). subst.
      rewrite <- Permutation_cons_app.
        reflexivity.
        apply IHt1. symmetry. assumption.
Qed.

(** Moved from ListLemmas to avoid circularity. *)

Lemma perm_min_front :
  forall (A : Type) (h : A) (t : list A),
    let m := min_dflt A h t in
      perm (m :: removeFirst m (h :: t)) (h :: t).
Proof.
  intros. destruct (min_split A h t) as [l1 [l2 [H H']]]. fold m in H, H'.
  rewrite H, <- H' in *. apply perm_symm. apply perm_front.
Qed.

Theorem trifilter_spec' :
  forall (A : TrichDec) (pivot : A) (l lo eq hi : list A),
    trifilter pivot l = (lo, eq, hi) ->
      perm (lo ++ eq) (filter (fun x : A => x <=? pivot) l) /\
      hi = filter (fun x : A => pivot <? x) l.
Proof.
  intros until hi. functional induction trifilter pivot l;
  intros; inv H; cbn in *; trich; edestruct IHp; try split; eauto.
    apply perm_cons; auto.
    rewrite (perm_front A x lo l2). apply perm_cons. auto.
    f_equal. auto.
Qed.*)