Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.

Inductive sorted (A : LinDec) : list A -> Prop :=
    | sorted0 : sorted A []
    | sorted1 : forall x : A, sorted A [x]
    | sorted2 : forall (x y : A) (l : list A),
        x ≤ y -> sorted A (y :: l) -> sorted A (x :: y :: l).

Hint Constructors sorted.

Fixpoint count (A : LinDec) (x : A) (l : list A) : nat :=
match l with
    | [] => 0
    | h :: t => if x =? h then S (count A x t) else count A x t
end.

Definition perm (A : LinDec) (l1 l2 : list A) : Prop :=
    forall x : A, count A x l1 = count A x l2.

Class Sort : Type :=
{
    sort :> forall {A : LinDec}, list A -> list A;
    sort_sorted : forall (A : LinDec) (l : list A),
        sorted A (sort l);
    sort_perm : forall (A : LinDec) (l : list A),
        perm A l (sort l);
}.

Coercion sort : Sort >-> Funclass.

Class Partition (A : Type) : Type :=
{
    partition :> A -> list A -> list A * list A * list A;
    spec_lo : forall (h : A) (t l1 l2 l3 : list A),
      partition h t = (l1, l2, l3) -> length l1 <= length t;
    spec_hi : forall (h : A) (t l1 l2 l3 : list A),
      partition h t = (l1, l2, l3) -> length l3 <= length t
}.

Coercion partition : Partition >-> Funclass.

(* Lemmas about [sorted]. *)

Theorem sorted_tail :
  forall (A : LinDec) (h : A) (t : list A),
    sorted A (h :: t) -> sorted A t.
Proof.
  inversion 1; auto.
Defined.

Theorem sorted_head :
  forall (A : LinDec) (x y : A) (l : list A),
    sorted A (x :: y :: l) -> x ≤ y.
Proof.
  inversion 1. assumption.
Qed.

Lemma sorted_app_all :
  forall (A : LinDec) (l : list A) (h : A) (t : list A),
    sorted A l -> sorted A (h :: t) -> (forall x : A, In x l -> leq x h) ->
      sorted A (l ++ h :: t).
Proof.
  induction l as [| h t]; simpl; intros.
    assumption.
    destruct t as [| h' t'].
      simpl in *. constructor.
        eapply (H1 h); eauto.
        assumption.
      rewrite <- app_comm_cons. constructor.
        eapply sorted_head. eassumption.
        apply IHt.
          apply sorted_tail with h. assumption.
          assumption.
          intros. apply H1. right. assumption.
Qed.

Hint Resolve sorted_head sorted_tail sorted_app_all.

Lemma sorted_cons :
  forall (A : LinDec) (h : A) (t : list A),
    (forall x : A, In x t -> h ≤ x) -> sorted A t -> sorted A (h :: t).
Proof.
  inversion 2; subst.
    auto.
    constructor; auto. apply H. simpl. auto.
    constructor.
      apply H. left. reflexivity.
      constructor; auto.
Qed.

Lemma sorted_mid :
  forall (A : LinDec) (x y : A) (l : list A),
    sorted A (x :: y :: l) -> sorted A (x :: l).
Proof.
  destruct l.
    auto.
    intros. constructor.
      assert (x ≤ y) by (apply sorted_head in H; auto).
        apply sorted_tail in H.
        assert (y ≤ c) by (apply sorted_head in H; auto).
        eapply leq_trans; eauto.
      do 2 eapply sorted_tail. eassumption.
Qed.

Lemma sorted_cons_conv :
  forall (A : LinDec) (h : A) (t : list A),
    sorted A (h :: t) -> forall x : A, In x t -> h ≤ x.
Proof.
  induction t as [| h' t'].
    inversion 2.
    intros. inversion H0; subst.
      apply sorted_head in H. assumption.
      apply IHt'.
        apply sorted_mid in H. assumption.
        assumption.
Qed.

Lemma sorted_cons_conv' :
  forall (A : LinDec) (h : A) (t : list A),
    sorted A (h :: t) -> forall x : A, In x (h :: t) -> h ≤ x.
Proof.
  induction t as [| h' t'].
    inversion 2; subst; dec.
    do 2 inversion 1; subst.
      dec.
      inversion H6; subst.
        assumption.
        apply IHt'.
          eapply sorted_mid; eauto.
          right. assumption.
Qed.

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

Require Import Classes.RelationClasses.

Instance Equiv_perm (A : LinDec) : Equivalence (perm A).
Proof.
  split; red; intros; eauto. eapply perm_trans; eauto.
Defined.

Require Import Permutation.

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

Theorem Permutation_perm :
  forall (A : LinDec) (l1 l2 : list A),
    Permutation l1 l2 -> perm A l1 l2.
Proof.
  induction 1; cbn; intros; dec.
Qed.

Theorem perm_Permutation :
  forall (A : LinDec) (l1 l2 : list A),
    perm A l1 l2 -> Permutation l1 l2.
Proof.
  unfold perm. induction l1 as [| h t]; cbn; intros.
    rewrite count_0; auto.
    induction l2 as [| h' t'].
      specialize (H h). cbn in H. dec.
      assert (H' := H). specialize (H h'); cbn in H'. dec.
        apply perm_skip. apply IHt. intro. specialize (H' x). dec.
Restart.
  intro. apply (bin_rel_list_ind A
  (fun l1 l2 => perm A l1 l2 -> Permutation l1 l2));
  unfold perm; cbn; intros.
    constructor.
    rewrite <- count_0 at 1; eauto.
    rewrite <- count_0 at 1; eauto.
    destruct (LinDec_eqb_spec A h h'); subst.
      constructor. apply H. intro. specialize (H0 x). dec.
Admitted.