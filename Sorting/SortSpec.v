Require Export RCCBase.

Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export Sorting.SelectionSort.

Set Implicit Arguments.

(* Properties of sorting *)
Fixpoint min' {A : TrichDec} (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match min' t with
            | None => Some h
            | Some m => Some (if leqb h m then h else m)
        end
end.

Lemma Permutation_min' :
  forall (A : TrichDec) (l1 l2 : list A),
    Permutation l1 l2 -> min' l1 = min' l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    destruct (min' l); f_equal; trich.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Lemma Sorted_min' :
  forall (A : TrichDec) (l : list A),
    Sorted A l -> min' l = head l.
Proof.
  induction 1; cbn.
    1-2: reflexivity.
    cbn in *. destruct (min' l); trich.
Qed.

Lemma Permutation_Sorted_aux :
  forall (A : TrichDec) (l1 l2 : list A),
    Permutation l1 l2 -> Sorted A l1 -> Sorted A l2 -> l1 = l2.
Proof.
  intros until 2. revert l2 H.
  induction H0; intros.
    apply Permutation_nil in H. subst. reflexivity.
    apply Permutation_length_1_inv in H. subst. reflexivity.
    inv H2.
      apply Permutation_length in H1. inv H1.
      apply Permutation_length in H1. inv H1.
      assert (x = x0).
        apply Permutation_min' in H1. rewrite 2!Sorted_min' in H1.
          cbn in H1. inv H1.
          1-2:auto.
        subst. f_equal. apply IHSorted.
          apply Permutation_cons_inv in H1. assumption.
          assumption.
Qed.

Lemma sort_unique :
  forall (A : TrichDec) (s1 s2 : Sort A) (l : list A),
    s1 l = s2 l.
Proof.
  intros. apply Permutation_Sorted_aux.
    rewrite 2!Permutation_sort. reflexivity.
    1-2: apply Sorted_sort.
Qed.

Lemma sort_idempotent :
  forall {A : TrichDec} (s : Sort A) (l : list A),
    sort (sort l) = sort l.
Proof.
  intros. apply Permutation_Sorted_aux.
    rewrite Permutation_sort. reflexivity.
    1-2: apply Sorted_sort.
Qed.

(** [Permutation] can be decided by sorting. *)

Lemma iff_Permutation_eq_sort :
  forall (A : TrichDec) (s : Sort A) (l1 l2 : list A),
    Permutation l1 l2 <-> sort l1 = sort l2.
Proof.
  split.
    intro. apply Permutation_Sorted_aux.
      rewrite 2!Permutation_sort. assumption.
      1-2: apply Sorted_sort.
    intro. rewrite <- Permutation_sort, H, Permutation_sort. reflexivity.
Qed.