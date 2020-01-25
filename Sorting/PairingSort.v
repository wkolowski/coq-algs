Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export PairingHeap.

Set Implicit Arguments.

(*Fixpoint sum (l : list nat) : nat :=
match l with
    | [] => 0
    | n :: ns => n + sum ns
end.

Fixpoint size {A : LinDec} (h : PairingHeap A) : nat :=
match h with
    | E => 0
    | T _ l => S (sum (map size l))
end.

Lemma size_empty :
  forall A : LinDec, size empty = 0.
Proof. reflexivity. Qed.

Lemma size_singleton :
  forall (A : LinDec) (x : A), size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma size_merge :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    size (merge h1 h2) = size h1 + size h2.
Proof.
  induction h1 using Tree_ind_proper.
    reflexivity.
    destruct h2; dec.
Qed.

Lemma size_insert :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    size (insert x h) = S (size h).
Proof.
  intros. apply size_merge.
Qed.

Lemma size_mergePairs :
  forall (A : LinDec) (l : list (Tree A)),
    size (mergePairs l) = sum (map size l).
Proof.
  intros. functional induction mergePairs l; cbn.
    trivial.
    rewrite <- plus_n_O. trivial.
    rewrite !size_merge, IHp, plus_assoc. trivial.
Qed.*)