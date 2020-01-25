

Require Export RCCBase.

Require Export Sorting.Perm.

Inductive Sorted (A : LinDec) : list A -> Prop :=
    | Sorted0 : Sorted A []
    | Sorted1 : forall x : A, Sorted A [x]
    | Sorted2 : forall (x y : A) (l : list A),
        x ≤ y -> Sorted A (y :: l) -> Sorted A (x :: y :: l).

Hint Constructors Sorted.

Class Sort (A : LinDec) : Type :=
{
    sort :> list A -> list A;
    Sorted_sort :
      forall l : list A, Sorted A (sort l);
(*    sort_perm :
      forall l : list A, perm A l (sort l);*)
    Permutation_sort :
      forall l : list A, Permutation (sort l) l
}.

Coercion sort : Sort >-> Funclass.

Lemma sort_perm :
  forall (A : LinDec) (s : Sort A) (l : list A),
    perm A l (sort l).
Proof.
  intros. apply Permutation_perm. rewrite Permutation_sort. reflexivity.
Qed.

(* Lemmas about [Sorted]. *)

Theorem Sorted_tail :
  forall (A : LinDec) (h : A) (t : list A),
    Sorted A (h :: t) -> Sorted A t.
Proof.
  inversion 1; auto.
Defined.

Theorem Sorted_head :
  forall (A : LinDec) (x y : A) (l : list A),
    Sorted A (x :: y :: l) -> x ≤ y.
Proof.
  inversion 1. assumption.
Qed.

Lemma Sorted_app_all :
  forall (A : LinDec) (l : list A) (h : A) (t : list A),
    Sorted A l -> Sorted A (h :: t) ->
    (forall x : A, In x l -> leq x h) ->
      Sorted A (l ++ h :: t).
Proof.
  induction l as [| h t]; simpl; intros.
    assumption.
    destruct t as [| h' t'].
      simpl in *. constructor.
        eapply (H1 h); eauto.
        assumption.
      rewrite <- app_comm_cons. constructor.
        eapply Sorted_head. eassumption.
        apply IHt.
          apply Sorted_tail with h. assumption.
          assumption.
          intros. apply H1. right. assumption.
Qed.

Lemma Sorted_app :
  forall (A : LinDec) (l1 l2 : list A),
    Sorted A l1 -> Sorted A l2 ->
      (forall x y : A, In x l1 -> In y l2 -> x ≤ y) ->
        Sorted A (l1 ++ l2).
Proof.
  destruct l2 as [| h2 t2]; cbn; intros.
    rewrite app_nil_r. assumption.
    apply Sorted_app_all; auto.
Qed.

Hint Resolve Sorted_head Sorted_tail Sorted_app_all.

Lemma Sorted_cons :
  forall (A : LinDec) (h : A) (t : list A),
    (forall x : A, In x t -> h ≤ x) -> Sorted A t -> Sorted A (h :: t).
Proof.
  inversion 2; subst.
    auto.
    constructor; auto. apply H. simpl. auto.
    constructor.
      apply H. left. reflexivity.
      constructor; auto.
Qed.

Lemma Sorted_mid :
  forall (A : LinDec) (x y : A) (l : list A),
    Sorted A (x :: y :: l) -> Sorted A (x :: l).
Proof.
  destruct l.
    auto.
    intros. constructor.
      assert (x ≤ y) by (apply Sorted_head in H; auto).
        apply Sorted_tail in H.
        assert (y ≤ c) by (apply Sorted_head in H; auto).
        eapply leq_trans; eauto.
      do 2 eapply Sorted_tail. eassumption.
Qed.

Lemma Sorted_cons_conv :
  forall (A : LinDec) (h : A) (t : list A),
    Sorted A (h :: t) -> forall x : A, In x t -> h ≤ x.
Proof.
  induction t as [| h' t'].
    inversion 2.
    intros. inversion H0; subst.
      apply Sorted_head in H. assumption.
      apply IHt'.
        apply Sorted_mid in H. assumption.
        assumption.
Qed.

Lemma Sorted_cons_conv' :
  forall (A : LinDec) (h : A) (t : list A),
    Sorted A (h :: t) -> forall x : A, In x (h :: t) -> h ≤ x.
Proof.
  induction t as [| h' t'].
    inversion 2; subst; dec.
    do 2 inversion 1; subst.
      dec.
      inversion H6; subst.
        assumption.
        apply IHt'.
          eapply Sorted_mid; eauto.
          right. assumption.
Qed.

(* Moved from TrichQuicksortSpec.v *)

Lemma Sorted_repeat :
  forall (A : LinDec) (x : A) (n : nat),
    Sorted A (repeat x n).
Proof.
  induction n as [| n']; cbn.
    constructor.
    destruct n'; cbn; constructor; auto.
Qed.

Lemma Sorted_filter_eqb :
  forall (A : LinDec) (x : A) (l : list A),
    Sorted A (filter (fun x' : A => x' =? x) l).
Proof.
  intros. destruct (filter_eqb_repeat A x l) as [n H].
  rewrite H. apply Sorted_repeat.
Qed.