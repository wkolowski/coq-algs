(** This algorithm is taken from the paper
    "Efficiency of Lambda-Encodings in Total Type Theory"
    by Stump and Fu. *)

Require Export Sorting.Sort.
Require Export Sorting.MergeSort.

Inductive Braun (A : Type) : Type :=
    | Leaf : A -> Braun A
    | Node : Braun A -> Braun A -> Braun A.

Arguments Leaf {A} _.
Arguments Node {A} _ _.

Fixpoint braunInsert {A : Type} (x : A) (b : Braun A) : Braun A :=
match b with
    | Leaf a => Node (Leaf x) (Leaf a)
    | Node l r => Node (braunInsert x r) l
end.

Fixpoint fromList {A : Type} (h : A) (t : list A) : Braun A :=
match t with
    | [] => Leaf h
    | h' :: t' => braunInsert h (fromList h' t')
end.

Fixpoint braunMerge {A : LinDec} (b : Braun A) : list A :=
match b with
    | Leaf a => [a]
    | Node l r => merge A (braunMerge l, braunMerge r)
end.

Definition braunSort {A : LinDec} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => braunMerge (fromList h t)
end.

Lemma Sorted_braunMerge :
  forall (A : LinDec) (b : Braun A),
    Sorted A (braunMerge b).
Proof.
  induction b as [a | l Hl r Hr]; cbn.
    constructor.
    apply Sorted_merge; cbn; assumption.
Qed.

Lemma Sorted_braunSort :
  forall (A : LinDec) (l : list A), Sorted A (braunSort l).
Proof.
  destruct l as [| h t]; cbn.
    constructor.
    apply Sorted_braunMerge.
Qed.

Fixpoint braunCount {A : Type} (p : A -> bool) (b : Braun A) : nat :=
match b with
    | Leaf a => if p a then 1 else 0
    | Node l r => braunCount p l + braunCount p r
end.

Lemma braunCount_braunInsert :
  forall (A : Type) (p : A -> bool) (x : A) (b : Braun A),
    braunCount p (braunInsert x b) =
      (if p x then S else id) (braunCount p b).
Proof.
  induction b as [a | l IHl r IHr]; cbn.
    destruct (p x); reflexivity.
    rewrite IHr. destruct (p x); unfold id; omega.
Qed.

Lemma braunCount_fromList :
  forall (A : Type) (p : A -> bool) (t : list A) (h : A),
    braunCount p (fromList h t) = count p (h :: t).
Proof.
  induction t as [| h' t']; cbn; intros.
    reflexivity.
    rewrite braunCount_braunInsert, IHt'. cbn.
      destruct (p h), (p h'); reflexivity.
Qed.

Lemma count_braunMerge :
  forall (A : LinDec) (p : A -> bool) (b : Braun A),
    count p (braunMerge b) = braunCount p b.
Proof.
  induction b as [a | l IHl r IHr]; cbn; intros.
    dec.
    rewrite <- merge_perm. cbn. rewrite count_app, IHl, IHr. reflexivity.
Defined.

Lemma perm_braunSort :
  forall (A : LinDec) (l : list A),
    perm l (braunSort l).
Proof.
  destruct l as [| h t]; intro; cbn.
    reflexivity.
    rewrite count_braunMerge, braunCount_fromList. cbn. reflexivity.
Qed.

#[refine]
Instance Sort_braunSort (A : LinDec) : Sort A :=
{|
    sort := @braunSort A;
|}.
Proof.
  apply Sorted_braunSort.
  intros. apply perm_Permutation. rewrite <- perm_braunSort. reflexivity.
Defined.

Time Compute @braunSort natle (cycle 200 testl).
Time Compute @ums' natle 1 (Small_recdepth natle 5) (braunSort) (HalfSplit natle) (cycle 200 testl).