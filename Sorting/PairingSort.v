Require Export Sorting.Sort.
Require Export ListLemmas.

Require Export PairingHeap.

Set Implicit Arguments.

Fixpoint fromList {A : Type} (cmp : A -> A -> bool) (l : list A) : PairingHeap A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.

Function toList
  {A : Type} (p : A -> A -> bool) (h : PairingHeap A) {measure size h}: list A :=
match extractMin p h with
    | None => []
    | Some (m, h') => m :: toList p h'
end.
Proof.
  destruct h; cbn; intros; subst; inv teq.
    rewrite size_mergePairs. apply le_n.
Defined.

Definition pairingSort (A : Type) (p : A -> A -> bool) (l : list A) : list A :=
  toList p (fromList p l).

(** Properties of [fromList]. *)

Lemma Elem_fromList :
  forall (A : Type) (cmp : A -> A -> bool) (x : A) (l : list A),
    Elem x (fromList cmp l) <-> In x l.
Proof.
  induction l as [| h t].
    split; inv 1.
    simpl. rewrite Elem_insert, IHt. firstorder.
Qed.

Lemma isHeap_fromList :
  forall (A : Ord) (l : list A),
    isHeap cmp (fromList cmp l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isHeap_insert. assumption.
Qed.

Lemma countTree_fromList :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (l : list A),
    countTree p (fromList cmp l) = count p l.
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    cbn. destruct (fromList cmp t) eqn: Heq.
      cbn in *. unfold id. destruct (p h); lia.
      rewrite <- IHt. destruct (cmp h a); cbn; destruct (p h), (p a); unfold id; lia.
Qed.

(** Properties of [toList]. *)

Lemma countTree_toList :
  forall (A : Type) (cmp : A -> A -> comparison) (p : A -> bool) (h : PairingHeap A),
    (*isHeap cmp h ->*) countTree p h = count p (toList cmp h).
Proof.
  intros until h.
  functional induction toList cmp h.
    destruct h; inv e.
    destruct h; inv e. cbn. rewrite <- IHl, countTree_mergePairs. reflexivity.
Qed.

Lemma Sorted_toList :
  forall (A : Ord) (h : PairingHeap A),
    isHeap cmp h -> Sorted cmp (toList cmp h).
Proof.
  intros. functional induction toList cmp h.
    constructor.
    rewrite toList_equation in *. destruct h'; cbn in *; constructor.
      eapply extractMin_spec; eauto. erewrite Elem_extractMin; eauto. cbn. assumption.
      eapply IHl, isHeap_extractMin; eauto.
Qed.

(** Properties of [pairingSort]. *)

Theorem Sorted_pairingSort :
  forall (A : Ord) (l : list A),
    Sorted cmp (pairingSort cmp l).
Proof.
  intros. unfold pairingSort.
  apply Sorted_toList, isHeap_fromList.
Qed.

Lemma perm_pairingSort :
  forall (A : Type) (cmp : A -> A -> comparison) (l : list A),
    perm (pairingSort cmp l) l.
Proof.
  unfold perm, pairingSort. intros.
  rewrite <- countTree_toList, countTree_fromList.
    reflexivity.
Qed.

Theorem Permutation_pairingSort :
  forall (A : Type) (cmp : A -> A -> comparison) (l : list A),
    Permutation (pairingSort cmp l) l.
Proof.
  intros. apply perm_Permutation, perm_pairingSort.
Qed.

Instance Sort_pairingSort (A : Ord) : Sort cmp :=
{
    sort := pairingSort cmp;
    Sorted_sort := Sorted_pairingSort A;
    Permutation_sort := Permutation_pairingSort cmp;
}.