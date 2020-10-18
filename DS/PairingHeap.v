Require Export LinDec.
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

(* TODO: develop *)
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
  forall (A : LinDec) (x : A), ~ Elem x empty.
Proof. inversion 1. Qed.

Lemma empty_isHeap :
  forall {A : Type} (R : A -> A -> Prop),
    isHeap R empty.
Proof. constructor. Qed.

Lemma isEmpty_empty :
  forall A : LinDec,
    isEmpty (@empty A) = true.
Proof. reflexivity. Qed.

Lemma isEmpty_singleton :
  forall (A : LinDec) (x : A),
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

Lemma insert_isHeap :
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
  forall (A : LinDec) (x : A) (l : list (Tree A)),
    Elem x (mergePairs l) <-> Exists (Elem x) l.
Proof.
  split; intro.
    functional induction @mergePairs A l; auto.
      rewrite ?merge_elem in H. decompose [or] H; clear H; auto.
    functional induction @mergePairs A l;
      rewrite ?merge_elem; inv H. inv H1.
Qed.

Lemma isHeap_mergePairs :
  forall (A : LinDec) (l : list (PairingHeap A)),
    Forall isHeap l -> isHeap (mergePairs l).
Proof.
  intros. functional induction @mergePairs A l.
    constructor.
    inv H.
    inv H. inv H3. apply isHeap_merge.
      apply isHeap_merge; assumption.
      apply IHp. assumption.
Qed.

Lemma isEmpty_mergePairs :
  forall (A : LinDec) (l : list (PairingHeap A)),
    isEmpty (mergePairs l) = true <->
    Forall (fun t => isEmpty t = true) l.
Proof.
  split.
    functional induction @mergePairs A l; cbn; intros; auto.
      rewrite ?isEmpty_merge_true in H. decompose [and] H. auto.
    functional induction @mergePairs A l; cbn; intros; auto.
      inv H.
      rewrite ?isEmpty_merge_true. inv H. inv H3.
Qed.

Lemma size_mergePairs :
  forall (A : LinDec) (l : list (PairingHeap A)),
    size (mergePairs l) = fold_right (fun h t => size h + t) 0 l.
Proof.
  intros. functional induction @mergePairs A l; cbn; intros; auto.
  rewrite !size_merge, IHp, plus_assoc. reflexivity.
Qed.

(** Properties of [unT]. *)

Lemma isHeap_unT :
  forall (A : LinDec) (m : A) (h h' : PairingHeap A),
    isHeap h -> unT h = Some (m, h') -> isHeap h'.
Proof.
  destruct h; cbn; intros; subst; inv H0.
  apply isHeap_mergePairs. inv H.
Qed.

Lemma Elem_unT :
  forall (A : LinDec) (m : A) (h h' : Tree A),
    unT h = Some (m, h') -> Elem m h.
Proof.
  destruct h; cbn; intros; inv H.
Qed.

Lemma size_unT :
  forall (A : LinDec) (m : A) (h h' : PairingHeap A),
    isHeap h -> unT h = Some (m, h') -> size h = 1 + size h'.
Proof.
  destruct h; cbn; intros; inv H0.
  rewrite size_mergePairs. reflexivity.
Qed.

Lemma unT_spec :
  forall (A : LinDec) (m : A) (h h' : Tree A),
    isHeap h -> unT h = Some (m, h') ->
      forall x : A, Elem x h -> m ≤ x.
Proof.
  destruct h; cbn; intros; inv H0.
  inv H. induction H3; inv H1. inv H2. inv H4.
Qed.

Lemma Elem_unT_eq :
  forall (A : LinDec) (m x : A) (h h' : Tree A),
    isHeap h -> unT h = Some (m, h') ->
      Elem x h <-> x = m \/ Elem x h'.
Proof.
  split.
    destruct h; cbn; intros; inv H0.
      inv H. induction H3; inv H1.
        inv H2.
          right. rewrite mergePairs_elem. auto.
          inv H4. destruct (IHForall ltac:(auto) H6).
            left. assumption.
            right. rewrite mergePairs_elem in *. auto.
    destruct 1; subst.
      eapply unT_elem; eauto.
      destruct h; cbn in *.
        inv H0.
        inv H0. constructor. rewrite mergePairs_elem in H1. auto.
Qed.

(** [toList] *)

Function toList
  {A : LinDec} (h : PairingHeap A) {measure size h}: list A :=
match unT h with
    | None => []
    | Some (m, h') => m :: toList h'
end.
Proof.
  destruct h; cbn; intros; subst; inv teq.
    rewrite size_mergePairs. apply le_n.
Defined.

(*Lemma Elem_toList_In :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
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

(*
Theorem Sorted_toList :
  forall (A : LinDec) (h : PairingHeap A),
    isHeap h -> Sorted A (toList h).
Proof.
  intros. functional induction @toList A h.
    constructor.
    rewrite toList_equation in *. destruct h'; cbn in *; constructor.
      eapply unT_spec; eauto. erewrite Elem_unT_eq; eauto.
      eapply IHl, isHeap_unT; eauto.
Qed.
*)

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
  forall (A : Type) (p : A -> bool) (h1 h2 : PairingHeap A),
    countTree p (merge h1 h2) = countTree p h1 + countTree p h2.
Proof.
  destruct h1, h2; cbn; intros; dec; dec; unfold id; lia.
Qed.

Lemma countTree_insert :
  forall (A : LinDec) (x y : A) (h : PairingHeap A),
    countTree x (insert y h) =
      (if x =? y then S else id) (countTree x h).
Proof.
  intros. unfold insert. rewrite countTree_merge, countTree_singleton. dec.
Qed.

Lemma countTree_mergePairs :
  forall (A : LinDec) (x : A) (l : list (PairingHeap A)),
    countTree x (mergePairs l) =
    fold_right (fun h t => countTree x h + t) 0 l.
Proof.
  intros. functional induction @mergePairs A l; cbn.
    reflexivity.
    rewrite <- plus_n_O. reflexivity.
    rewrite !countTree_merge, IHp, plus_assoc. reflexivity.
Qed.

Lemma countTree_toList :
  forall (A : LinDec) (p : A -> bool) (h : PairingHeap A),
    isHeap h -> countTree x h = count p (toList h).
Proof.
  intros. functional induction @toList A h;
  destruct h; inv e; cbn; dec.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply isHeap_mergePairs. inv H.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply isHeap_mergePairs. inv H.
Qed.

Fixpoint fromList {A : LinDec} (l : list A) : PairingHeap A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Lemma countTree_fromList :
  forall (A : LinDec) (x : A) (l : list A),
    countTree x (fromList l) = count A x l.
Proof.
  induction l as [| h t].
    cbn. reflexivity.
    unfold fromList. rewrite countTree_insert. fold fromList.
      rewrite IHt. dec.
Qed.

Lemma isHeap_fromList :
  forall (A : LinDec) (l : list A),
    isHeap (fromList l).
Proof.
  induction l as [| h t].
    cbn. constructor.
    apply insert_isHeap. fold fromList. assumption.
Qed.

Definition pairingSort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Theorem pairingSort_perm :
  forall (A : LinDec) (l : list A),
    perm A (pairingSort A l) l.
Proof.
  unfold perm, pairingSort. intros.
  rewrite <- countTree_toList, countTree_fromList.
    reflexivity.
    apply isHeap_fromList.
Qed.

#[refine]
Instance Sort_pairingSort (A : LinDec) : Sort A :=
{
    sort := @pairingSort A;
}.
Proof.
  all: intros.
    unfold pairingSort. apply Sorted_toList, isHeap_fromList.
    apply perm_Permutation. rewrite pairingSort_perm. reflexivity.
Defined.