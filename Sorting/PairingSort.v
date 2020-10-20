Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export PairingHeap.

Set Implicit Arguments.

Fixpoint sum (l : list nat) : nat :=
match l with
    | [] => 0
    | n :: ns => n + sum ns
end.

Fixpoint size {A : Type} (h : PairingHeap A) : nat :=
match h with
    | E => 0
    | T _ l => S (sum (map size l))
end.

Lemma size_empty :
  forall A : Type, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma size_singleton :
  forall (A : Type) (x : A), size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma size_merge :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : PairingHeap A),
    size (merge p h1 h2) = size h1 + size h2.
Proof.
  induction h1 using Tree_ind_proper.
    reflexivity.
    destruct h2; cbn; try destruct (p x a); cbn; lia.
Qed.

Lemma size_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : PairingHeap A),
    size (insert p x h) = S (size h).
Proof.
  intros. apply size_merge.
Qed.

Lemma size_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (Tree A)),
    size (mergePairs p l) = sum (map size l).
Proof.
  intros. functional induction mergePairs p l; cbn.
    reflexivity.
    rewrite <- plus_n_O. reflexivity.
    rewrite !size_merge, IHp0, plus_assoc. reflexivity.
Qed.