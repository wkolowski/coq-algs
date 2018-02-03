Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export Sorting.Perm.

Inductive sorted (A : LinDec) : list A -> Prop :=
    | sorted0 : sorted A []
    | sorted1 : forall x : A, sorted A [x]
    | sorted2 : forall (x y : A) (l : list A),
        x ≤ y -> sorted A (y :: l) -> sorted A (x :: y :: l).

Hint Constructors sorted.

Class Sort : Type :=
{
    sort :> forall {A : LinDec}, list A -> list A;
    sort_sorted : forall (A : LinDec) (l : list A),
        sorted A (sort l);
    sort_perm : forall (A : LinDec) (l : list A),
        perm A l (sort l);
}.

Coercion sort : Sort >-> Funclass.

Class Partition (A : LinDec) : Type :=
{
    partition :> A -> list A -> list A * list A * list A;
    spec_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x lo -> x ≤ pivot;
    spec_eq :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x eq -> x = pivot;
    spec_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x hi -> pivot ≤ x /\ pivot <> x;
    len_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length lo <= length l;
    len_eq :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length eq <= length l;
    len_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          length hi <= length l;
    partition_perm :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          perm A l (lo ++ eq ++ hi);
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

Lemma sorted_app :
  forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 ->
      (forall x y : A, In x l1 -> In y l2 -> x ≤ y) ->
        sorted A (l1 ++ l2).
Proof.
  destruct l2 as [| h2 t2]; cbn; intros.
    rewrite app_nil_r. assumption.
    apply sorted_app_all; auto.
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