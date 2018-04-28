Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export Sorting.Perm.

Inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | sorted0 : sorted R []
    | sorted1 : forall x : A, sorted R [x]
    | sorted2 : forall (x y : A) (l : list A),
        R x y -> sorted R (y :: l) -> sorted R (x :: y :: l).

Hint Constructors sorted.

Class Sort (A : Type) (R : A -> A -> Prop) : Type :=
{
    sort :> list A -> list A;
    sort_sorted :
      forall l : list A, sorted R (sort l);
    sort_perm :
      forall l : list A, Permutation l (sort l);
}.

Coercion sort : Sort >-> Funclass.

Class Partition (A : Type) (R : A -> A -> Prop) : Type :=
{
    partition :> A -> list A -> list A * list A * list A;
    spec_lo :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x lo -> R x pivot;
    spec_eq :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x eq -> x = pivot;
    spec_hi :
      forall (pivot : A) (l lo eq hi : list A),
        partition pivot l = (lo, eq, hi) ->
          forall x : A, In x hi -> R pivot x /\ pivot <> x;
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
          Permutation l (lo ++ eq ++ hi);
}.

Coercion partition : Partition >-> Funclass.

(* Lemmas about [sorted]. *)

Theorem sorted_tail :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A),
    sorted R (h :: t) -> sorted R t.
Proof.
  inversion 1; auto.
Defined.

Theorem sorted_head :
  forall (A : Type) (R : A -> A -> Prop) (x y : A) (l : list A),
    sorted R (x :: y :: l) -> R x y.
Proof.
  inversion 1. assumption.
Qed.

Lemma sorted_app_all :
  forall (A : Type) (R : A -> A -> Prop) (l : list A) (h : A) (t : list A),
    sorted R l -> sorted R (h :: t) ->
    (forall x : A, In x l -> R x h) ->
      sorted R (l ++ h :: t).
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
  forall (A : Type) (R : A -> A -> Prop) (l1 l2 : list A),
    sorted R l1 -> sorted R l2 ->
      (forall x y : A, In x l1 -> In y l2 -> R x y) ->
        sorted R (l1 ++ l2).
Proof.
  destruct l2 as [| h2 t2]; cbn; intros.
    rewrite app_nil_r. assumption.
    apply sorted_app_all; auto.
Qed.

Hint Resolve (*sorted_head*) sorted_tail sorted_app_all.

Lemma sorted_cons :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A),
    (forall x : A, In x t -> R h x) -> sorted R t -> sorted R (h :: t).
Proof.
  inversion 2; subst.
    auto.
    constructor; auto. apply H. simpl. auto.
    constructor.
      apply H. left. reflexivity.
      constructor; auto.
Qed.

Lemma sorted_mid :
  forall (A : Type) (R : A -> A -> Prop) (x y : A) (l : list A)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
      sorted R (x :: y :: l) -> sorted R (x :: l).
Proof.
  destruct l.
    auto.
    intros. constructor.
      assert (R x y) by (apply sorted_head in H; auto).
        apply sorted_tail in H.
        assert (R y a) by (apply sorted_head in H; auto).
        eapply R_trans; eauto.
      do 2 eapply sorted_tail. eassumption.
Qed.

Lemma sorted_cons_conv :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
    sorted R (h :: t) -> forall x : A, In x t -> R h x.
Proof.
  induction t as [| h' t']; inv 3.
    apply sorted_head with t'. assumption.
    apply IHt'; try assumption.
      apply sorted_mid with h'; assumption.
Qed.

Lemma sorted_cons_conv' :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A)
    (R_refl : forall x : A, R x x)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
      sorted R (h :: t) -> forall x : A, In x (h :: t) -> R h x.
Proof.
  induction t as [| h' t']; inv 4.
    inv H1.
    inv H1.
      inv H.
      apply IHt'; try assumption.
        apply sorted_mid with h'; assumption.
        right. assumption.
Qed.