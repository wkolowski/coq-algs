Require Export CoqAlgs.Base.
(* Require Export Ord. *)

Set Implicit Arguments.

Require Export Data.Tree.
Require Export DS.Heap.
Require Export Sorting.Sort.

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

Definition extractMin
  {A : Type} (cmp : A -> A -> bool) (h : PairingHeap A) : option (A * PairingHeap A) :=
match h with
    | E => None
    | T x l => Some (x, mergePairs cmp l)
end.

(** Properties of [empty] and [isEmpty]. *)

Lemma isEmpty_empty :
  forall A : Type,
    isEmpty (@empty A) = true.
Proof. reflexivity. Qed.

Lemma Elem_empty :
  forall (A : Type) (x : A), ~ Elem x empty.
Proof. inversion 1. Qed.

Lemma isHeap_empty :
  forall {A : Type} (R : A -> A -> Prop),
    isHeap R empty.
Proof. constructor. Qed.

Lemma isHeap2_empty :
  forall {A : Type} (R : A -> A -> Prop),
    isHeap2 R empty.
Proof. constructor. Qed.

(** Properties of [singleton]. *)

Lemma isEmpty_singleton :
  forall (A : Type) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma size_singleton :
  forall (A : Type) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma Elem_singleton :
  forall (A : Type) (x y : A),
    Elem x (singleton y) <-> x = y.
Proof.
  split; intro; subst.
    inv H. inv H1.
    constructor.
Qed.

(* Lemma Elem_singleton' :
  forall (A : Type) (x : A),
    Elem x (singleton x).
Proof.
  intros. rewrite Elem_singleton. reflexivity.
Qed. *)

Lemma isHeap_singleton :
  forall {A : Type} (R : A -> A -> Prop) (x : A),
    isHeap R (singleton x).
Proof. do 2 constructor. Qed.

Lemma isHeap2_singleton :
  forall {A : Type} (R : A -> A -> Prop) (x : A),
    isHeap2 R (singleton x).
Proof.
  do 2 constructor.
Qed.

(** Properties of [merge]. *)

Lemma Elem_merge :
  forall (A : Type) (cmp : A -> A -> bool) (x : A) (h1 h2 : PairingHeap A),
    Elem x (merge cmp h1 h2) <-> Elem x h1 \/ Elem x h2.
Proof.
  split; destruct h1, h2; cbn;
  repeat match goal with
      | |- context [if ?x then _ else _] => destruct x
      | H : Elem _ _ |- _ => inv H
      | H : T _ _ = T _ _ |- _ => inv H
      | H : Exists _ (_ :: _) |- _ => inv H
      | H : Elem _ _ \/ Elem _ _ |- _ => inv H
      | H : Elem _ _ \/ Elem _ E |- _ => inv H
      | _ => intros
  end.
Qed.

Lemma isHeap_merge :
  forall {A : Ord} (h1 h2 : PairingHeap A),
    isHeap cmp h1 -> isHeap cmp h2 ->
      isHeap cmp (merge cmp h1 h2).
Proof.
  intros A h1 h2.
  functional induction (merge cmp h1 h2);
  isHeap'.
    inv 1. induction H1; isHeap.
      specialize (H5 _ H). unfold comparison2bool in *. trich.
    inv 1.
      unfold comparison2bool in *. trich.
      induction H1; isHeap. specialize (H3 _ H). unfold comparison2bool in *. trich.
Qed.

Lemma isHeap2_merge :
  forall {A : Ord} (h1 h2 : PairingHeap A),
    isHeap2 cmp h1 -> isHeap2 cmp h2 ->
      isHeap2 cmp (merge cmp h1 h2).
Proof.
  intros A h1 h2.
  functional induction (merge cmp h1 h2);
  isHeap2.
    repeat constructor; auto. unfold comparison2bool in *. trich.
Qed.

Lemma isEmpty_merge :
  forall (A : Type) (cmp : A -> A -> bool) (h1 h2 : PairingHeap A),
    isEmpty (merge cmp h1 h2) = isEmpty h1 && isEmpty h2.
Proof.
  destruct h1, h2; cbn.
    1-3: reflexivity.
    destruct (cmp a a0); cbn; reflexivity.
Qed.

(* Lemma isEmpty_merge_true :
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
 *)
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

(* Lemma Elem_insert :
  forall (A : Type) (p : A -> A -> bool) (x y : A) (h : PairingHeap A),
    Elem x h -> Elem x (insert p y h).
Proof.
  unfold insert, merge, singleton.
  destruct h; intro.
    inv H.
    destruct (p y a); inv H.
Qed.
 *)
(* Lemma Elem_insert' :
  forall (A : Type) (p : A -> A -> bool) (x : A) (h : PairingHeap A),
    Elem x (insert p x h).
Proof.
  unfold insert, merge, singleton.
  destruct h.
    constructor.
    destruct (p x a); auto.
Qed.
 *)

Lemma Elem_insert :
  forall (A : Type) (p : A -> A -> bool) (x y : A) (h : PairingHeap A),
    Elem x (insert p y h) <-> x = y \/ Elem x h.
Proof.
  intros.
  unfold insert.
  rewrite Elem_merge, Elem_singleton.
  reflexivity.
Qed.

Lemma isHeap_insert :
  forall (A : Ord) (x : A) (h : PairingHeap A),
    isHeap cmp h -> isHeap cmp (insert cmp x h).
Proof.
  intros. unfold insert. apply isHeap_merge.
    apply isHeap_singleton.
    assumption.
Qed.

Lemma isEmpty_insert :
  forall (A : Type) (cmp : A -> A -> bool) (x : A) (h : PairingHeap A),
    isEmpty (insert cmp x h) = false.
Proof.
  destruct h; cbn.
    reflexivity.
    destruct (cmp x a); cbn; reflexivity.
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

Lemma Elem_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (x : A) (l : list (Tree A)),
    Elem x (mergePairs p l) <-> Exists (Elem x) l.
Proof.
  split; intro.
    functional induction mergePairs p l; auto.
      inv H.
      rewrite ?Elem_merge in H. decompose [or] H; clear H; auto.
    functional induction mergePairs p l;
      rewrite ?Elem_merge; inv H; inv H1.
Qed.

Lemma isHeap_mergePairs :
  forall (A : Ord) (l : list (PairingHeap A)),
    Forall (isHeap cmp) l -> isHeap cmp (mergePairs cmp l).
Proof.
  intros.
  functional induction mergePairs cmp l;
  isHeap.
    apply isHeap_merge.
      apply isHeap_merge; assumption.
      apply IHp. assumption.
Qed.

Lemma isEmpty_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    isEmpty (mergePairs p l) = true <->
    Forall (fun t => isEmpty t = true) l.
Proof.
  split.
    functional induction mergePairs p l; isHeap.
      rewrite !isEmpty_merge, !andb_true_iff. firstorder.
    functional induction mergePairs p l; isHeap.
      rewrite !isEmpty_merge, H1, H2, IHp0; auto.
Qed.

Lemma size_mergePairs' :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    size (mergePairs p l) = fold_right (fun h t => size h + t) 0 l.
Proof.
  intros.
  functional induction mergePairs p l;
  cbn; intros; auto.
  rewrite !size_merge, IHp0, plus_assoc. reflexivity.
Qed.

Lemma size_mergePairs :
  forall (A : Type) (p : A -> A -> bool) (l : list (PairingHeap A)),
    size (mergePairs p l) = sum (map size l).
Proof.
  intros.
  functional induction mergePairs p l;
  cbn; intros; auto.
  rewrite !size_merge, IHp0, plus_assoc.
  reflexivity.
Qed.

(** Properties of [extractMin]. *)

Lemma Elem_extractMin :
  forall (A : Type) (p : A -> A -> bool) (m x : A) (h h' : Tree A),
    isHeap p h -> extractMin p h = Some (m, h') ->
      Elem x h <-> x = m \/ Elem x h'.
Proof.
  inv 1; inv 1.
  rewrite Elem_mergePairs.
  split; inv 1.
Qed.

Lemma isHeap_extractMin :
  forall (A : Ord) (m : A) (h h' : PairingHeap A),
    isHeap cmp h -> extractMin cmp h = Some (m, h') -> isHeap cmp h'.
Proof.
  inv 1; inv 1.
  apply isHeap_mergePairs.
  assumption.
Qed.

Lemma isEmpty_extractMin :
  forall (A : Type) (cmp : A -> A -> bool) (m : A) (h h' : PairingHeap A),
    extractMin cmp h = Some (m, h') -> isEmpty h = false.
Proof.
  destruct h; cbn; intros.
    inv H.
    reflexivity.
Qed.

Lemma size_extractMin :
  forall (A : Type) (p : A -> A -> bool) (m : A) (h h' : PairingHeap A),
    isHeap p h -> extractMin p h = Some (m, h') -> size h = 1 + size h'.
Proof.
  destruct h; cbn; intros; inv H0.
  rewrite size_mergePairs. reflexivity.
Qed.

Lemma extractMin_spec :
  forall (A : Ord) (m : A) (h h' : Tree A),
    isHeap cmp h -> extractMin cmp h = Some (m, h') ->
      forall x : A, Elem x h -> cmp m x.
Proof.
  inv 1; inv 1; inv 1.
    trich.
    induction H3; isHeap.
Qed.

(** [countTree] and its properties. *)

Lemma countTree_empty :
  forall (A : Type) (p : A -> bool),
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
      (if p x then 1 else 0) + countTree p h.
Proof.
  intros. unfold insert.
  rewrite countTree_merge, countTree_singleton.
  destruct (p x); unfold id; lia.
Qed.

Lemma countTree_mergePairs' :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (l : list (PairingHeap A)),
    countTree p (mergePairs cmp l) =
    fold_right (fun h t => countTree p h + t) 0 l.
Proof.
  intros. functional induction mergePairs cmp l; cbn.
    reflexivity.
    rewrite <- plus_n_O. reflexivity.
    rewrite !countTree_merge, IHp0, plus_assoc. reflexivity.
Qed.

Lemma countTree_mergePairs :
  forall (A : Type) (cmp : A -> A -> bool) (p : A -> bool) (l : list (PairingHeap A)),
    countTree p (mergePairs cmp l) = sum (map (countTree p) l).
Proof.
  intros. functional induction mergePairs cmp l; cbn.
    reflexivity.
    rewrite <- plus_n_O. reflexivity.
    rewrite !countTree_merge, IHp0, plus_assoc. reflexivity.
Qed.