Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export LinDec.

Require Import Classes.RelationClasses.
Require Import Permutation.

Fixpoint count (A : LinDec) (x : A) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => if x =? h then S (count A x t) else count A x t
end.

Definition perm (A : LinDec) (l1 l2 : list A) : Prop :=
    forall x : A, count A x l1 = count A x l2.

(* Lemmas about [count]. *)

Lemma count_last :
  forall (A : LinDec) (l : list A) (x y : A),
    count A x (l ++ [y]) = count A x l + count A x [y].
Proof.
  induction l as [| h t]; simpl; intros.
    destruct (x =? y); reflexivity.
    rewrite IHt. simpl. destruct (x =? h), (x =? y); omega.
Qed.

Lemma count_reverse :
  forall (A : LinDec) (l : list A) (x : A),
    count A x (rev l) = count A x l.
Proof.
  induction l as [| h t]; simpl; intros.
    reflexivity.
    rewrite count_last, IHt. simpl. destruct (x =? h); omega.
Qed.

Lemma count_app_comm : forall (A : LinDec) (x : A) (l1 l2 : list A),
    count A x (l1 ++ l2) = count A x (l2 ++ l1).
Proof.
  induction l1 as [| h1 t1].
    simpl; intros. rewrite app_nil_r. reflexivity.
    intros. rewrite <- app_comm_cons at 1.
      replace (l2 ++ h1 :: t1) with ((l2 ++ [h1]) ++ t1).
        rewrite <- IHt1, app_assoc, count_last.
          simpl. destruct (x =? h1); omega.
        rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma count_app :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    count A x (l1 ++ l2) = count A x l1 + count A x l2.
Proof.
  induction l1; dec.
Qed.

Lemma count_cons :
  forall (A : LinDec) (h : A) (t : list A),
    count A h (h :: t) = 1 + count A h t.
Proof.
  intros. dec.
Qed.

Lemma count_filter :
  forall (A : LinDec) (x h : A) (t : list A),
    count A x t = count A x (filter (fun y : A => y <=? h) t) +
                  count A x (filter (fun y : A => negb (y <=? h)) t).
Proof.
  induction t as [| h' t']; simpl; repeat dec.
Qed.

Lemma count_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x l <-> count A x l <> 0.
Proof.
  induction l as [| h t]; cbn; intuition dec.
Qed.

Lemma count_0 :
  forall (A : LinDec) (l : list A),
    (forall x : A, count A x l = 0) -> l = [].
Proof.
  induction l as [| h t]; cbn; intros.
    trivial.
    specialize (H h). dec.
Qed.

(* Lemmas about [perm]. *)
Lemma perm_refl : forall (A : LinDec) (l : list A), perm A l l.
Proof. unfold perm; auto. Defined.

Lemma perm_symm : forall (A : LinDec) (l1 l2 : list A),
    perm A l1 l2 -> perm A l2 l1.
Proof. unfold perm; auto. Defined.

Lemma perm_trans : forall (A : LinDec) (l1 l2 l3 : list A),
    perm A l1 l2 -> perm A l2 l3 -> perm A l1 l3.
Proof.
  unfold perm; intros. eapply eq_trans; auto.
Defined.

Lemma perm_cons : forall (A : LinDec) (x : A) (l1 l2 : list A),
    perm A l1 l2 -> perm A (x :: l1) (x :: l2).
Proof.
  unfold perm. intros. simpl. rewrite H. reflexivity.
Defined.

Lemma perm_nil_cons :
  forall (A : LinDec) (h : A) (t : list A),
    ~ perm A (h :: t) [].
Proof.
  unfold not; intros. red in H. specialize (H h). cbn in H. dec.
Qed.

Lemma perm_swap : forall (A : LinDec) (x y : A) (l1 l2 : list A),
    perm A l1 l2 -> perm A (x :: y :: l1) (y :: x :: l2).
Proof.
  unfold perm; simpl; intros; destruct (x0 =? x), (x0 =? y);
  rewrite H; auto.
Defined.

Theorem perm_front :
  forall (A : LinDec) (x : A) (l1 l2 : list A),
    perm A (l1 ++ x :: l2) (x :: l1 ++ l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    apply perm_refl.
    eapply perm_trans with (h1 :: x :: t1 ++ l2).
      apply perm_cons. apply IHt1.
      apply perm_swap. apply perm_refl.
Qed.

Hint Resolve perm_refl perm_symm perm_cons perm_swap perm_front.

Lemma perm_app_comm :
  forall (A : LinDec) (l1 l2 : list A),
    perm A (l1 ++ l2) (l2 ++ l1).
Proof.
  unfold perm. intros. apply count_app_comm.
Qed.

Lemma perm_app :
  forall (A : LinDec) (l1 l1' l2 l2' : list A),
    perm A l1 l1' -> perm A l2 l2' -> perm A (l1 ++ l2) (l1' ++ l2').
Proof.
  unfold perm; intros. rewrite 2 count_app, H, H0. auto.
Qed.

Lemma perm_In :
  forall (A : LinDec) (x : A) (l l' : list A),
    In x l -> perm A l l' -> In x l'.
Proof.
  intros. rewrite count_In. red in H0. rewrite <- H0.
  rewrite <- count_In. assumption.
Qed.

Instance Equiv_perm (A : LinDec) : Equivalence (perm A).
Proof.
  split; red; intros; eauto. eapply perm_trans; eauto.
Defined.

Theorem bin_rel_list_ind :
  forall (A : Type) (R : list A -> list A -> Prop)
    (H_nil_nil : R [] [])
    (H_cons_nil : forall l : list A, R l [])
    (H_nil_cons : forall l : list A, R [] l)
    (H_cons_cons : forall (h h' : A) (t t' : list A),
      R t t' -> R (h :: t) (h' :: t'))
      (l1 l2 : list A), R l1 l2.
Proof.
  induction l1 as [| h t]; cbn.
    assumption.
    destruct l2 as [| h' t']; cbn.
      apply H_cons_nil.
      apply H_cons_cons. apply IHt.
Qed.

Lemma perm_singl :
  forall (A : LinDec) (x : A) (l : list A),
    perm A [x] l -> l = [x].
Proof.
  unfold perm; destruct l as [| h1 [| h2 t]]; cbn; intros.
    specialize (H x). dec.
    specialize (H x). dec.
    assert (H1 := H h1). assert (H2 := H h2). dec.
Qed.

(* TODO *) Lemma perm_front_ex :
  forall (A : LinDec) (h : A) (t l : list A),
    perm A (h :: t) l -> exists l1 l2 : list A,
      perm A l (l1 ++ h :: l2).
Proof.
Admitted.

Theorem Permutation_perm :
  forall (A : LinDec) (l1 l2 : list A),
    Permutation l1 l2 -> perm A l1 l2.
Proof.
  induction 1; cbn; intros; dec.
Qed.

Lemma perm_cons_inv :
  forall (A : LinDec) (h : A) (t1 t2 : list A),
    perm A (h :: t1) (h :: t2) -> perm A t1 t2.
Proof.
  unfold perm; intros. specialize (H x). cbn in H. dec.
Qed.

(* TODO *) Theorem perm_Permutation :
  forall (A : LinDec) (l1 l2 : list A),
    perm A l1 l2 -> Permutation l1 l2.
Proof.
  induction l1 as [| h1 t1]; cbn; intros.
    destruct l2; cbn; auto. red in H. cbn in H. specialize (H c). dec.
    destruct l2 as [| h2 t2]; cbn.
      red in H. cbn in H. specialize (H h1). dec.
      destruct (perm_front_ex _ _ _ _ H) as [l1' [l2' H']].
        rewrite H' in H. rewrite perm_front in H.
        apply perm_cons_inv in H. specialize (IHt1 (l1' ++ l2') H).
          rewrite IHt1.
Admitted.