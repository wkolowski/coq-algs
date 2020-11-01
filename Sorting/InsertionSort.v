Require Export Sorting.Sort.

Set Implicit Arguments.

Fixpoint ins (A : TrichDec) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if x ≤? h then x :: h :: t else h :: (ins A x t)
end.

Definition insertionSort (A : TrichDec) (l : list A)
  : list A := fold_right (ins A) [] l.

Lemma perm_ins :
  forall (A : TrichDec) (x : A) (l : list A),
    perm (x :: l) (ins A x l).
Proof.
  unfold perm; intros. induction l.
    reflexivity.
    unfold ins; destruct (leqb x a); fold ins.
      reflexivity.
      rewrite (perm_swap A x a l l (perm_refl A l)).
        cbn. rewrite <- IHl. reflexivity.
Qed.

Lemma Permutation_ins :
  forall (A : TrichDec) (x : A) (l : list A),
    Permutation (ins A x l) (x :: l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (x ≤? h).
      reflexivity.
      rewrite IHt. constructor.
Qed.

Lemma Sorted_ins :
  forall (A : TrichDec) (x : A) (l : list A),
    Sorted A l -> Sorted A (ins A x l).
Proof.
  induction 1; cbn in *; trich.
Qed.

#[refine]
Instance Sort_insertionSort (A : TrichDec) : Sort A :=
{
    sort := insertionSort A
}.
Proof.
  induction l as [| h t]; cbn; auto.
    apply Sorted_ins. assumption.
  induction l as [| h t]; simpl; auto.
    apply Permutation.perm_trans with (h :: insertionSort A t); auto.
      apply Permutation_ins.
Defined.

(** Better insertion sort. *)

Fixpoint ins'
  {A : Type} (cmp : A -> A -> bool) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if cmp x h then x :: h :: t else h :: (ins' cmp x t)
end.

Definition insertionSort'
  {A : Type} (cmp : A -> A -> bool) (l : list A) : list A :=
    fold_right (ins' cmp) [] l.

Lemma perm_ins' :
  forall (A : TrichDec) (x : A) (l : list A),
    perm (x :: l) (ins' (@leqb A) x l).
Proof.
  unfold perm. induction l; cbn; intros.
    reflexivity.
    unfold ins'; destruct (leqb x a); fold (@ins' A).
      reflexivity.
      trich; rewrite <- IHl; cbn. destruct (p a), (p x); reflexivity.
Qed.

Lemma Permutation_ins' :
  forall (A : TrichDec) (x : A) (l : list A),
    Permutation (ins' (@leqb A) x l) (x :: l).
Proof.
  unfold perm. induction l; cbn; intros.
    reflexivity.
    unfold ins'; destruct (leqb x a); fold (@ins' A).
      reflexivity.
      rewrite Permutation.perm_swap. constructor. assumption.
Qed.

Lemma Sorted_ins' :
  forall (A : TrichDec) (x : A) (l : list A),
    Sorted A l -> Sorted A (ins' (@leqb A) x l).
Proof.
  induction 1; cbn in *; trich.
Qed.

#[refine]
Instance Sort_insertionSort' (A : TrichDec) : Sort A :=
{
    sort := insertionSort' (@leqb A)
}.
Proof.
  induction l as [| h t]; cbn; auto.
    apply Sorted_ins'. assumption.
  induction l as [| h t]; simpl; auto.
  rewrite Permutation_ins'. constructor. assumption.
Defined.