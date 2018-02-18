Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Export RCCBase.

Set Implicit Arguments.

Require Import Basic.Tree.

Definition PairingHeap (A : LinDec) : Type := Tree A.

Definition empty {A : LinDec} : PairingHeap A := E.

Definition singleton {A : LinDec} (x : A) : PairingHeap A := T x [].

Definition merge
  {A : LinDec} (h1 h2 : PairingHeap A) : PairingHeap A :=
match h1, h2 with
    | E, _ => h2
    | _, E => h1
    | T m1 l1, T m2 l2 =>
        if m1 <=? m2
        then T m1 (h2 :: l1)
        else T m2 (h1 :: l2)
end.

Definition insert
  {A : LinDec} (x : A) (h : PairingHeap A) : PairingHeap A :=
    merge (singleton x) h.

Function mergePairs {A : LinDec} (hs : list (PairingHeap A))
  : PairingHeap A :=
match hs with
    | [] => E
    | [h] => h
    | h1 :: h2 :: hs' => merge (merge h1 h2) (mergePairs hs')
end.

(* TODO: develop *)
Definition unT
  {A : LinDec} (h : PairingHeap A) : option (A * PairingHeap A) :=
match h with
    | E => None
    | T x l => Some (x, mergePairs l)
end.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | T _ ts => 1 + fold_right (fun h t => size h + t) 0 ts
end.

(** Properties of [empty] and [isEmpty]. *)

Lemma empty_elem :
  forall (A : LinDec) (x : A), ~ elem x empty.
Proof. inversion 1. Qed.

Lemma empty_isHeap :
  forall A : LinDec, isHeap (@empty A).
Proof. constructor. Qed.

Lemma isEmpty_empty :
  forall A : LinDec, isEmpty (@empty A) = true.
Proof. reflexivity. Qed.

Lemma isEmpty_singleton :
  forall (A : LinDec) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma isEmpty_merge :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    isEmpty (merge h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1, h2; cbn; dec.
Qed.

Lemma isEmpty_merge_true :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    isEmpty (merge h1 h2) = true <->
    isEmpty h1 = true /\ isEmpty h2 = true.
Proof.
  split; destruct h1, h2; cbn; intros; destruct H; dec.
Qed.

Lemma isEmpty_merge_false :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    isEmpty (merge h1 h2) = false <->
    isEmpty h1 = false \/ isEmpty h2 = false.
Proof.
  split; destruct h1, h2; cbn; intros; destruct H; dec.
Qed.

Lemma isEmpty_insert :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    isEmpty (insert x h) = false.
Proof.
  destruct h; cbn; dec.
Qed.

(** Properties of [singleton]. *)

Lemma singleton_elem :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  split; intro; subst.
    inv H.
    constructor.
Qed.

Lemma singleton_elem' :
  forall (A : LinDec) (x : A),
    elem x (singleton x).
Proof.
  intros. rewrite singleton_elem. reflexivity.
Qed.

Lemma singleton_isHeap :
  forall (A : LinDec) (x : A),
    isHeap (singleton x).
Proof. do 2 constructor. Qed.

Lemma singleton_size :
  forall (A : LinDec) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

(** Properties of [merge]. *)

Lemma merge_elem :
  forall (A : LinDec) (x : A) (h1 h2 : PairingHeap A),
    elem x (merge h1 h2) <-> elem x h1 \/ elem x h2.
Proof.
  split; destruct h1, h2; cbn; intros; dec; inv H; try inv H0; try inv H1.
Qed.

Lemma merge_isHeap :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    isHeap h1 -> isHeap h2 -> isHeap (merge h1 h2).
Proof.
  destruct h1, h2; cbn; intros; auto.
  dec; do 2 constructor; try (inv H; inv H0; fail).
    inv H0. clear H4. induction H3; intros.
      inv H0.
      inv H1. inv H4. eauto.
    inv H. clear H4. induction H3; intros.
      inv H.
      inv H1. inv H4. eauto.
Qed.

Lemma merge_size :
  forall (A : LinDec) (h1 h2 : PairingHeap A),
    size (merge h1 h2) = size h1 + size h2.
Proof.
  destruct h1, h2; cbn; intros; dec.
Qed.

(** Properties of [insert]. *)

Lemma insert_isHeap :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    isHeap h -> isHeap (insert x h).
Proof.
  intros. unfold insert. apply merge_isHeap.
    apply singleton_isHeap.
    assumption.
Qed.

Lemma insert_elem :
  forall (A : LinDec) (x y : A) (h : PairingHeap A),
    elem x (insert y h) <-> x = y \/ elem x h.
Proof.
  unfold insert. split; intro.
    apply merge_elem in H. destruct H; [left | right].
      rewrite <- singleton_elem. assumption.
      assumption.
    rewrite merge_elem. inv H. left. apply singleton_elem'.
Qed.

Lemma insert_size :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    size (insert x h) = 1 + size h.
Proof.
  destruct h; cbn; dec.
Qed.

(** Properties of [mergePairs]. *)

Hint Extern 0 =>
match goal with
    | H : elem _ E |- _ => inv H
    | H : elem _ empty |- _ => inv H
end.

Lemma mergePairs_elem :
  forall (A : LinDec) (x : A) (l : list (Tree A)),
    elem x (mergePairs l) <-> Exists (elem x) l.
Proof.
  split; intro.
    functional induction @mergePairs A l; auto.
      rewrite ?merge_elem in H. decompose [or] H; clear H; auto.
    functional induction @mergePairs A l;
      rewrite ?merge_elem; inv H. inv H1.
Qed.

Lemma mergePairs_isHeap :
  forall (A : LinDec) (l : list (PairingHeap A)),
    Forall isHeap l -> isHeap (mergePairs l).
Proof.
  intros. functional induction @mergePairs A l.
    constructor.
    inv H.
    inv H. inv H3. apply merge_isHeap.
      apply merge_isHeap; assumption.
      apply IHp. assumption.
Qed.

Lemma mergePairs_isEmpty :
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

Lemma mergePairs_size :
  forall (A : LinDec) (l : list (PairingHeap A)),
    size (mergePairs l) = fold_right (fun h t => size h + t) 0 l.
Proof.
  intros. functional induction @mergePairs A l; cbn; intros; auto.
  rewrite !merge_size, IHp, plus_assoc. reflexivity.
Qed.

(** Properties of [unT]. *)

Lemma unT_isHeap :
  forall (A : LinDec) (m : A) (h h' : PairingHeap A),
    isHeap h -> unT h = Some (m, h') -> isHeap h'.
Proof.
  destruct h; cbn; intros; subst; inv H0.
  apply mergePairs_isHeap. inv H.
Qed.

Lemma unT_elem :
  forall (A : LinDec) (m : A) (h h' : Tree A),
    unT h = Some (m, h') -> elem m h.
Proof.
  destruct h; cbn; intros; inv H.
Qed.

Lemma unT_size :
  forall (A : LinDec) (m : A) (h h' : PairingHeap A),
    isHeap h -> unT h = Some (m, h') -> size h = 1 + size h'.
Proof.
  destruct h; cbn; intros; inv H0.
  rewrite mergePairs_size. reflexivity.
Qed.

Lemma unT_spec :
  forall (A : LinDec) (m : A) (h h' : Tree A),
    isHeap h -> unT h = Some (m, h') ->
      forall x : A, elem x h -> m ≤ x.
Proof.
  destruct h; cbn; intros; inv H0.
  inv H. induction H3; inv H1. inv H2. inv H4.
Qed.

Lemma unT_elem_eq :
  forall (A : LinDec) (m x : A) (h h' : Tree A),
    isHeap h -> unT h = Some (m, h') ->
      elem x h <-> x = m \/ elem x h'.
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
    rewrite mergePairs_size. apply le_n.
Defined.

(*Lemma elem_toList_In :
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    isHeap h -> elem x h <-> In x (toList h).
Proof.
  split; intros.
    functional induction @toList A h; cbn.
      destruct h; cbn in *.
        inv H.
        inv e.
      assert (x = m \/ elem x h') by (eapply unT_elem_eq; eauto).
        destruct H1; auto. apply unT_isHeap in e; auto.
    functional induction @toList A h; cbn.
      inv H0.
      rewrite (@unT_elem_eq A m x h h'); auto.
        apply unT_isHeap in e; auto. inv H0.
Qed.*)

Require Export Sorting.Sort.

Theorem toList_sorted :
  forall (A : LinDec) (h : PairingHeap A),
    isHeap h -> sorted A (toList h).
Proof.
  intros. functional induction @toList A h.
    constructor.
    rewrite toList_equation in *. destruct h'; cbn in *; constructor.
      eapply unT_spec; eauto. erewrite unT_elem_eq; eauto.
      eapply IHl, unT_isHeap; eauto.
Qed.

(** [countTree] and its properties. *)

Lemma countTree_empty :
  forall (A : LinDec) (x : A),
    countTree x empty = 0.
Proof. reflexivity. Qed.

Lemma countTree_singleton :
  forall (A : LinDec) (x y : A),
    countTree x (singleton y) = if x =? y then 1 else 0.
Proof.
  intros. dec.
Qed.

Lemma countTree_merge :
  forall (A : LinDec) (x : A) (h1 h2 : PairingHeap A),
    countTree x (merge h1 h2) = countTree x h1 + countTree x h2.
Proof.
  destruct h1, h2; cbn; intros; dec; dec; unfold id; omega.
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
  forall (A : LinDec) (x : A) (h : PairingHeap A),
    isHeap h -> countTree x h = count A x (toList h).
Proof.
  intros. functional induction @toList A h;
  destruct h; inv e; cbn; dec.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply mergePairs_isHeap. inv H.
    rewrite <- IHl, countTree_mergePairs.
      reflexivity.
      apply mergePairs_isHeap. inv H.
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

Lemma fromList_isHeap :
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
    perm A l (pairingSort A l).
Proof.
  unfold perm, pairingSort. intros.
  rewrite <- countTree_toList, countTree_fromList.
    reflexivity.
    apply fromList_isHeap.
Qed.

Instance Sort_pairingSort : Sort :=
{
    sort := @pairingSort;
}.
Proof.
  all: intros.
    unfold pairingSort. apply toList_sorted, fromList_isHeap.
    apply pairingSort_perm.
Defined.