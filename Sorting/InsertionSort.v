Require Export Sorting.Sort.

Set Implicit Arguments.

Fixpoint ins (A : Ord) (x : A) (l : list A) : list A :=
match l with
    | [] => [x]
    | h :: t => if x ≤? h then x :: h :: t else h :: (ins A x t)
end.

Definition insertionSort (A : Ord) (l : list A)
  : list A := fold_right (ins A) [] l.

Lemma perm_ins :
  forall (A : Ord) (x : A) (l : list A),
    perm (x :: l) (ins A x l).
Proof.
  unfold perm; intros. induction l.
    reflexivity.
    unfold ins. destruct (trich_leb_spec x a); fold ins.
      reflexivity.
      rewrite (perm_swap A x a l l (perm_refl A l)).
        cbn. rewrite <- IHl. reflexivity.
Qed.

Lemma Permutation_ins :
  forall (A : Ord) (x : A) (l : list A),
    Permutation (ins A x l) (x :: l).
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    destruct (x ≤? h).
      reflexivity.
      rewrite IHt. constructor.
Qed.

Lemma Sorted_ins :
  forall (A : Ord) (x : A) (l : list A),
    Sorted trich_le l -> Sorted trich_le (ins A x l).
Proof.
  induction 1; cbn in *; trich; constructor; trich. cbn in *.
    inv IHSorted. constructor; trich.
Qed.

#[refine]
Instance Sort_insertionSort (A : Ord) : Sort trich_le :=
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
  forall (A : Ord) (x : A) (l : list A),
    perm (x :: l) (ins' trich_leb x l).
Proof.
  unfold perm. induction l; cbn; intros.
    reflexivity.
    unfold ins'; destruct (trich_leb_spec x a); fold (@ins' A).
      reflexivity.
      trich; rewrite <- IHl; cbn. destruct (p a), (p x); reflexivity.
Qed.

Lemma Permutation_ins' :
  forall (A : Ord) (x : A) (l : list A),
    Permutation (ins' trich_leb x l) (x :: l).
Proof.
  unfold perm. induction l; cbn; intros.
    reflexivity.
    unfold ins'; destruct (trich_leb_spec x a); fold (@ins' A).
      reflexivity.
      rewrite Permutation.perm_swap. constructor. assumption.
Qed.

Lemma Sorted_ins' :
  forall (A : Ord) (x : A) (l : list A),
    Sorted trich_le l -> Sorted trich_le (ins' trich_leb x l).
Proof.
  induction 1; cbn in *; trich; constructor; trich.
    inv IHSorted. constructor; trich.
Qed.

#[refine]
Instance Sort_insertionSort' (A : Ord) : Sort trich_le :=
{
    sort := insertionSort' trich_leb
}.
Proof.
  induction l as [| h t]; cbn; auto.
    apply Sorted_ins'. assumption.
  induction l as [| h t]; simpl; auto.
  rewrite Permutation_ins'. constructor. assumption.
Defined.