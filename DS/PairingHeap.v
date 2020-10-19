(* Require Export LinDec. *)
Require Export RCCBase.

Set Implicit Arguments.

Require Import Basic.Tree.

Definition PairingHeap (A : Type) : Type := Tree A.

Definition empty {A : Type} : PairingHeap A := E.

Definition singleton {A : Type} (x : A) : PairingHeap A := T x [].

Function merge
  {A : Type} (cmp : A -> A -> bool) (h1 h2 : PairingHeap A) : PairingHeap A :=
match h1, h2 with
    | E, _ => h2
    | _, E => h1
    | T m1 l1, T m2 l2 =>
        if cmp m1 m2
        then T m1 (h2 :: l1)
        else T m2 (h1 :: l2)
end.

Definition insert
  {A : Type} (cmp : A -> A -> bool) (x : A) (h : PairingHeap A) : PairingHeap A :=
    merge cmp (singleton x) h.

Function mergePairs {A : Type} (cmp : A -> A -> bool) (hs : list (PairingHeap A))
  : PairingHeap A :=
match hs with
    | [] => E
    | [h] => h
    | h1 :: h2 :: hs' => merge cmp (merge cmp h1 h2) (mergePairs cmp hs')
end.

Definition unT
  {A : Type} (cmp : A -> A -> bool) (h : PairingHeap A) : option (A * PairingHeap A) :=
match h with
    | E => None
    | T x l => Some (x, mergePairs cmp l)
end.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | T _ ts => 1 + fold_right (fun h t => size h + t) 0 ts
end.

(** Properties of [empty] and [isEmpty]. *)

Lemma empty_Elem :
  forall (A : Type) (x : A), ~ Elem x empty.
Proof. inversion 1. Qed.

Lemma empty_isHeap :
  forall {A : Type} (R : A -> A -> Prop),
    isHeap R empty.
Proof. constructor. Qed.

Lemma isEmpty_empty :
  forall A : Type,
    isEmpty (@empty A) = true.
Proof. reflexivity. Qed.

Lemma isEmpty_singleton :
  forall (A : Type) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma isEmpty_merge :
  forall (A : Type) (cmp : A -> A -> bool) (h1 h2 : PairingHeap A),
    isEmpty (merge cmp h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1, h2; cbn.
    1-3: reflexivity.
    destruct (cmp a a0); cbn; reflexivity.
Qed.

Lemma isEmpty_merge_true :
  forall (A : Type) (cmp : A -> A -> bool) (h1 h2 : PairingHeap A),
    isEmpty (merge cmp h1 h2) = true <->
    isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  split; destruct h1, h2; cbn; inv 1.
  destruct (cmp a a0); cbn; auto.
Qed.

Lemma isEmpty_merge_false :
  forall (A : Type) (cmp : A -> A -> bool) (h1 h2 : PairingHeap A),
    isEmpty (merge cmp h1 h2) = false <->
    isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  split; destruct h1, h2; cbn; inv 1;
  destruct (cmp a a0); cbn; auto.
Qed.

Lemma isEmpty_insert :
  forall (A : Type) (cmp : A -> A -> bool) (x : A) (h : PairingHeap A),
    isEmpty (insert cmp x h) = false.
Proof.
  destruct h; cbn.
    reflexivity.
    destruct (cmp x a); cbn; reflexivity.
Qed.

(** Properties of [singleton]. *)

Lemma Elem_singleton :
  forall (A : Type) (x y : A),
    Elem x (singleton y) <-> x = y.
Proof.
  split; intro; subst.
    inv H.
    constructor.
Qed.

Lemma Elem_singleton' :
  forall (A : Type) (x : A),
    Elem x (singleton x).
Proof.
  intros. rewrite Elem_singleton. reflexivity.
Qed.

Lemma isHeap_singleton :
  forall {A : Type} (R : A -> A -> Prop) (x : A),
    isHeap R (singleton x).
Proof. do 2 constructor. Qed.

Lemma size_singleton :
  forall (A : Type) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

(** Properties of [merge]. *)

Lemma Elem_merge :
  forall (A : Type) (cmp : A -> A -> bool) (x : A) (h1 h2 : PairingHeap A),
    Elem x (merge cmp h1 h2) <-> Elem x h1 \/ Elem x h2.
Proof.
  split; destruct h1, h2; cbn. all: inv 1;
  destruct (cmp a a0); try inv H0; inv H1.
Qed.

Lemma isHeap_merge :
  forall {A : Type} (cmp : A -> A -> bool) (h1 h2 : PairingHeap A)
    (cmp_trans :
      forall x y z : A, cmp x y -> cmp y z -> cmp x z)
    (cmp_antisym :
      forall x y : A, cmp x y = false -> cmp y x = true),
        isHeap cmp h1 -> isHeap cmp h2 -> isHeap cmp (merge cmp h1 h2).
Proof.
  destruct h1, h2; cbn; intros; auto.
  destruct (cmp a a0) eqn: Hcmp; do 2 constructor; try (inv H; inv H0; fail).
    inv H0. clear H4. induction H3; intros.
      inv H0.
      inv H1. inv H4. eauto.
    inv H0. clear H4. induction H3; intros. (*
      inv H0.
        apply cmp_antisym. assumption.
        inv H2.
       inv H1. inv H4. eauto.
*)
Restart.
  intros A cmp h1 h2.
  functional induction (merge cmp h1 h2); cbn;
  inv 3; inv 1; do 2 constructor; auto.
    inv 1.
Admitted.

Lemma size_merge :
  forall (A : Type) (p : A -> A -> bool) (h1 h2 : PairingHeap A),
    size (merge p h1 h2) = size h1 + size h2.
Proof.
  destruct h1, h2; cbn; intros;
  try match goal with
      | |- context [if ?p ?x ?y then _ else _] => destruct (p x y)
  end; cbn; lia.
Qed.

(** Properties of [insert]. *)

Lemma isHeap_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : PairingHeap A),
    isHeap p h -> isHeap p (insert p x h).
Proof.
  intros. unfold insert. apply isHeap_merge.
    admit.
    admit.
    apply isHeap_singleton.
    assumption.
Restart.
  unfold insert. intros A p x h.
  remember (singleton x) as h'. revert x Heqh'.
  functional induction (merge p h' h);
  inv 1; inv 1.
    do 2 constructor.
    repeat constructor; auto. inv 1. induction H3.
      inv H1.
      apply IHForall.
Admitted.

Lemma Elem_insert :
  forall (A : Type) (p : A -> A -> bool) (x y : A) (h : PairingHeap A),
    Elem x h -> Elem x (insert p y h).
Proof.
  unfold insert, merge, singleton.
  destruct h; intro.
    inv H.
    destruct (p y a); inv H.
Qed.

Lemma Elem_insert' :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : PairingHeap A),
    Elem x (insert p x h).
Proof.
  unfold insert, merge, singleton.
  destruct h.
    constructor.
    destruct (p x a); auto.
Qed.

Lemma Elem_insert'' :
  forall (A : Type) (p : A -> A -> bool) (x y : A) (h : PairingHeap A),
    Elem x (insert p y h) <-> x = y \/ Elem x h.
Proof.
  unfold insert, merge, singleton.
  destruct h.
    split; inv 1.
    destruct (p y a); split; inv 1.
      inv H1.
      inv H1. inv H0.
      inv H0.
Restart.
  unfold insert. split; intro.
    apply Elem_merge in H. destruct H.
      left. apply Elem_singleton. assumption.
      right. assumption.
    rewrite Elem_merge, Elem_singleton. assumption.
Qed.

Lemma size_insert :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : PairingHeap A),
    size (insert p x h) = 1 + size h.
Proof.
  destruct h; cbn.
    reflexivity.
    destruct (p x a); cbn; lia.
Qed.

(** Properties of [mergePairs]. *)

Hint Extern 0 =>
match goal with
    | H : Elem _ E |- _ => inv H
    | H : Elem _ empty |- _ => inv H
end
  : core.

Lemma Elem_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list (Tree A)),
    Elem x (mergePairs p l) <-> Exists (Elem x) l.
Proof.
  split; intro.
    functional induction mergePairs p l; auto.
      rewrite ?Elem_merge in H. decompose [or] H; clear H; auto.
    functional induction mergePairs p l;
      rewrite ?Elem_merge; inv H. inv H1.
Qed.

Lemma isHeap_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    Forall (isHeap p) l -> isHeap p (mergePairs p l).
Proof.
  intros. functional induction mergePairs p l.
    constructor.
    inv H.
    inv H. inv H3. apply isHeap_merge.
      1-2: admit.
      apply isHeap_merge; auto. 1-2: admit.
      apply IHp0. assumption.
Admitted.

Lemma isEmpty_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    isEmpty (mergePairs p l) = true <->
    Forall (fun t => isEmpty t = true) l.
Proof.
  split.
    functional induction mergePairs p l; cbn; intros; auto.
      rewrite ?isEmpty_merge_true in H. decompose [and] H. auto.
    functional induction mergePairs p l; cbn; intros; auto.
      inv H.
      rewrite ?isEmpty_merge_true. inv H. inv H3.
Qed.

Lemma size_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    size (mergePairs p l) = fold_right (fun h t => size h + t) 0 l.
Proof.
  intros. functional induction mergePairs p l; cbn; intros; auto.
  rewrite !size_merge, IHp0, plus_assoc. reflexivity.
Qed.

(** Properties of [unT]. *)

Lemma isHeap_unT :
  forall (A : Type) (p : A -> A -> bool) (m : A) (h h' : PairingHeap A),
    isHeap p h -> unT p h = Some (m, h') -> isHeap p h'.
Proof.
  destruct h; cbn; intros; subst; inv H0.
  apply isHeap_mergePairs. inv H.
Qed.

Lemma Elem_unT :
  forall (A : Type) (p : A -> A -> bool) (m : A) (h h' : Tree A),
    unT p h = Some (m, h') -> Elem m h.
Proof.
  destruct h; cbn; intros; inv H.
Qed.

Lemma size_unT :
  forall (A : Type) (p : A -> A -> bool) (m : A) (h h' : PairingHeap A),
    isHeap p h -> unT p h = Some (m, h') -> size h = 1 + size h'.
Proof.
  destruct h; cbn; intros; inv H0.
  rewrite size_mergePairs. reflexivity.
Qed.

Lemma unT_spec :
  forall (A : Type) (p : A -> A -> comparison) (m : A) (h h' : Tree A),
    isHeap p h -> unT p h = Some (m, h') ->
      forall x : A, Elem x h -> p m x.
Proof.
  destruct h; cbn; intros; inv H0; inv H.
  induction H3.
    inv H1. admit.
    inv H4. inv H1. inv H2.
Admitted.

Lemma Elem_unT_eq :
  forall (A : Type) (p : A -> A -> bool) (m x : A) (h h' : Tree A),
    isHeap p h -> unT p h = Some (m, h') ->
      Elem x h <-> x = m \/ Elem x h'.
Proof.
  split.
    destruct h; cbn; intros; inv H0.
      inv H. induction H3; inv H1.
        inv H2.
          right. rewrite Elem_mergePairs. auto.
          inv H4. destruct (IHForall ltac:(auto) H6).
            left. assumption.
            right. rewrite Elem_mergePairs in *. auto.
    destruct 1; subst.
      eapply Elem_unT; eauto.
      destruct h; cbn in *.
        inv H0.
        inv H0. constructor. rewrite Elem_mergePairs in H1. auto.
Qed.

(** [toList] *)

Function toList
  {A : Type} (p : A -> A -> bool) (h : PairingHeap A) {measure size h}: list A :=
match unT p h with
    | None => []
    | Some (m, h') => m :: toList p h'
end.
Proof.
  destruct h; cbn; intros; subst; inv teq.
    rewrite size_mergePairs. apply le_n.
Admitted. (* Defined. breaks *)

(*Lemma Elem_toList_In :
  forall (A : Type) (x : A) (h : PairingHeap A),
    isHeap h -> Elem x h <-> In x (toList h).
Proof.
  split; intros.
    functional induction @toList A h; cbn.
      destruct h; cbn in *.
        inv H.
        inv e.
      assert (x = m \/ Elem x h') by (eapply Elem_unT_eq; eauto).
        destruct H1; auto. apply isHeap_unT in e; auto.
    functional induction @toList A h; cbn.
      inv H0.
      rewrite (@Elem_unT_eq A m x h h'); auto.
        apply isHeap_unT in e; auto. inv H0.
Qed.*)

Require Export Sorting.Sort.

Theorem Sorted_toList :
  forall (A : Type) (cmp : A -> A -> comparison) (h : PairingHeap A),
    isHeap cmp h -> Sorted cmp (toList cmp h).
Proof.
  intros. functional induction toList cmp h.
    constructor.
    rewrite toList_equation in *. destruct h'; cbn in *; constructor.
      eapply unT_spec; eauto. erewrite Elem_unT_eq; eauto. cbn. assumption.
      eapply IHl, isHeap_unT; eauto.
Qed.

(** [countTree] and its properties. *)

Lemma countTree_empty :
  forall (A : Type) (p : A -> bool) (x : A),
    countTree p empty = 0.
Proof. reflexivity. Qed.

Lemma countTree_singleton :
  forall (A : Type) (p : A -> bool) (x : A),
    countTree p (singleton x) = if p x then 1 else 0.
Proof.
  intros. cbn. destruct (p x); reflexivity.
Qed.

Lemma countTree_merge :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (h1 h2 : PairingHeap A),
    countTree p (merge cmp h1 h2) = countTree p h1 + countTree p h2.
Proof.
  destruct h1, h2; cbn; try lia.
  destruct (cmp a a0); cbn; destruct (p a), (p a0); cbn; unfold id; try lia.
Qed.

Lemma countTree_insert :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (x : A) (h : PairingHeap A),
    countTree p (insert cmp x h) =
      (if p x then S else id) (countTree p h).
Proof.
  intros. unfold insert.
  rewrite countTree_merge, countTree_singleton.
  destruct (p x); unfold id; lia.
Qed.

Lemma countTree_mergePairs :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (l : list (PairingHeap A)),
    countTree p (mergePairs cmp l) =
    fold_right (fun h t => countTree p h + t) 0 l.
Proof.
  intros. functional induction mergePairs cmp l; cbn.
    reflexivity.
    rewrite <- plus_n_O. reflexivity.
    rewrite !countTree_merge, IHp0, plus_assoc. reflexivity.
Qed.

Lemma countTree_toList :
  forall (A : Type) (cmp : A -> A -> comparison) (p : A -> bool) (h : PairingHeap A),
    isHeap cmp h -> countTree p h = count p (toList cmp h).
Proof.
  intros until h.
  functional induction toList cmp h;
  destruct h; inv e; cbn; destruct (p m); unfold id; intro.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply isHeap_mergePairs. inv H.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply isHeap_mergePairs. inv H.
Qed.

Fixpoint fromList {A : Type} (p : A -> A -> bool) (l : list A) : PairingHeap A :=
match l with
    | [] => E
    | h :: t => insert p h (fromList p t)
end.

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

Lemma isHeap_fromList :
  forall (A : Type) (p : A -> A -> bool) (l : list A),
    isHeap p (fromList p l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isHeap_insert. assumption.
Qed.

Definition pairingSort (A : Type) (p : A -> A -> bool) (l : list A) : list A :=
  toList p (fromList p l).

Theorem pairingSort_perm :
  forall (A : Type) (cmp : A -> A -> comparison) (l : list A),
    perm (pairingSort cmp l) l.
Proof.
  unfold perm, pairingSort. intros.
  rewrite <- countTree_toList, countTree_fromList.
    reflexivity.
    apply isHeap_fromList.
Qed.

#[refine]
Instance Sort_pairingSort (A : Type) (cmp : A -> A -> comparison) : Sort cmp :=
{
    sort := pairingSort cmp
}.
Proof.
  all: intros.
    unfold pairingSort. apply Sorted_toList, isHeap_fromList.
    apply perm_Permutation. rewrite pairingSort_perm. reflexivity.
Defined.