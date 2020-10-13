Require Export RCCBase.

Require Export Sorting.Perm.

Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
    | Sorted0 : Sorted R []
    | Sorted1 : forall x : A, Sorted R [x]
    | Sorted2 : forall (x y : A) (l : list A),
        R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

Hint Constructors Sorted.

Class Sort {A : Type} (R : A -> A -> Prop) : Type :=
{
    sort : list A -> list A;
    Sorted_sort :
      forall l : list A, Sorted R (sort l);
    Permutation_sort :
      forall l : list A, Permutation (sort l) l
}.

Coercion sort : Sort >-> Funclass.

Lemma sort_perm :
  forall (A : Type) (R : A -> A -> Prop) (s : Sort R) (l : list A),
    perm l (sort l).
Proof.
  intros. apply Permutation_perm. rewrite Permutation_sort. reflexivity.
Qed.

(*
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
*)

(* Lemmas about [Sorted]. *)

Theorem Sorted_tail :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A),
    Sorted R (h :: t) -> Sorted R t.
Proof.
  inversion 1; auto.
Defined.

Theorem Sorted_head :
  forall (A : Type) (R : A -> A -> Prop) (x y : A) (l : list A),
    Sorted R (x :: y :: l) -> R x y.
Proof.
  inversion 1. assumption.
Qed.

Lemma Sorted_app_all :
  forall (A : Type) (R : A -> A -> Prop) (l : list A) (h : A) (t : list A),
    Sorted R l -> Sorted R (h :: t) ->
    (forall x : A, In x l -> R x h) ->
      Sorted R (l ++ h :: t).
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
  forall (A : Type) (R : A -> A -> Prop) (l1 l2 : list A),
    Sorted R l1 -> Sorted R l2 ->
      (forall x y : A, In x l1 -> In y l2 -> R x y) ->
        Sorted R (l1 ++ l2).
Proof.
  destruct l2 as [| h2 t2]; cbn; intros.
    rewrite app_nil_r. assumption.
    apply Sorted_app_all; auto.
Qed.

Hint Resolve (*Sorted_head*) Sorted_tail Sorted_app_all.

Lemma Sorted_cons :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A),
    (forall x : A, In x t -> R h x) -> Sorted R t -> Sorted R (h :: t).
Proof.
  inversion 2; subst.
    auto.
    constructor; auto. apply H. simpl. auto.
    constructor.
      apply H. left. reflexivity.
      constructor; auto.
Qed.

Lemma Sorted_mid :
  forall (A : Type) (R : A -> A -> Prop) (x y : A) (l : list A)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
      Sorted R (x :: y :: l) -> Sorted R (x :: l).
Proof.
  destruct l.
    auto.
    intros. constructor.
      assert (R x y) by (apply Sorted_head in H; auto).
        apply Sorted_tail in H.
        assert (R y a) by (apply Sorted_head in H; auto).
        eapply R_trans; eauto.
      do 2 eapply Sorted_tail. eassumption.
Qed.

Lemma Sorted_cons_conv :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
    Sorted R (h :: t) -> forall x : A, In x t -> R h x.
Proof.
  induction t as [| h' t']; inv 3.
    apply Sorted_head with t'. assumption.
    apply IHt'; try assumption.
      apply Sorted_mid with h'; assumption.
Qed.

Lemma Sorted_cons_conv' :
  forall (A : Type) (R : A -> A -> Prop) (h : A) (t : list A)
    (R_refl : forall x : A, R x x)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
      Sorted R (h :: t) -> forall x : A, In x (h :: t) -> R h x.
Proof.
  induction t as [| h' t']; inv 4.
    inv H1.
    inv H1.
      inv H.
      apply IHt'; try assumption.
        apply Sorted_mid with h'; assumption.
        right. assumption.
Qed.

(** An alternative characterization of Sortedness *)

Fixpoint nth' {A : Type} (n : nat) (l : list A) {struct l} : option A :=
match l, n with
    | [], _ => None
    | h :: t, 0 => Some h
    | _ :: t, S n' => nth' n' t
end.

Definition Sorted' {A : Type} (R : A -> A -> Prop) (l : list A) : Prop :=
  forall (n1 n2 : nat) (x y : A),
    nth' n1 l = Some x -> nth' n2 l = Some y -> n1 <= n2 -> R x y.

Lemma Sorted'_Sorted_aux :
  forall (A : Type) (R : A -> A -> Prop) (l : list A),
    Sorted' R l -> Sorted R l.
Proof.
  unfold Sorted'. intros.
  induction l as [| x [| y l]]; constructor.
    apply (H 0 1 x y); cbn; auto.
    apply IHl. intros. apply (H (S n1) (S n2)); cbn in *; auto.
      apply le_n_S. assumption.
Qed.

Lemma Sorted_Sorted'_aux :
  forall
    (A : Type) (R : A -> A -> Prop) (l : list A)
    (R_refl : forall x : A, R x x)
    (R_trans : forall x y z : A, R x y -> R y z -> R x z),
      Sorted R l -> Sorted' R l.
Proof.
  induction 3; unfold Sorted' in *; cbn in *; intros.
    inv H.
    destruct n1, n2; inv H; inv H0.
    destruct n1 as [| [| n1']], n2 as [| [| n2']]; inv H1; inv H2.
      apply R_trans with y; auto. apply (IHSorted 0 (S n2')); auto.
        apply le_0_n.
      inv H3.
      apply (IHSorted 0 (S n2') x0 y0); auto. apply le_0_n.
      inv H3.
      inv H3. inv H2.
      apply (IHSorted (S n1') (S n2') x0 y0); auto.
        apply le_S_n. assumption.
Qed.