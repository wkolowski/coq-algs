Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Require Import LinDec.
Require Import ListLemmas.
Require Import Sorting.Sort.

Require Export Classes.EquivDec.
Require Export Compare_dec.

Inductive BTree (A : Type) : Type :=
    | empty : BTree A
    | node : A -> BTree A -> BTree A -> BTree A.

Arguments empty {A}.
Arguments node {A} _ _ _.

Inductive elem {A : Type} (a : A) : BTree A -> Prop :=
    | elem_root : forall l r : BTree A, elem a (node a l r)
    | elem_left : forall (v : A) (l r : BTree A),
        elem a l -> elem a (node v l r)
    | elem_right : forall (v : A) (l r : BTree A),
        elem a r -> elem a (node v l r).

Inductive isHeap {A : LinDec} : BTree A -> Prop :=
    | isHeap_empty : isHeap empty
    | isHeap_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, elem x l -> v ≤ x) -> isHeap l ->
          (forall x : A, elem x r -> v ≤ x) -> isHeap r ->
            isHeap (node v l r).

Hint Constructors elem isHeap.

Definition singleton {A : Type} (x : A) : BTree A :=
  node x empty empty.

Fixpoint elem_decb
  {A : LinDec} (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        (x =? v) || elem_decb x l || elem_decb x r
end.

Definition root {A : Type} (bt : BTree A) : option A :=
match bt with
    | empty => None
    | node v l r => Some v
end.

Definition isEmpty {A : Type} (t : BTree A) : bool :=
match t with
    | empty => true
    | _ => false
end.

(* [BTree_toList], [fromList] and their variants *)
Function BTree_toList {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => BTree_toList l ++ v :: BTree_toList r
end.

Function BTree_toList'_aux {A : LinDec} (t : BTree A) (acc : list A) : list A :=
match t with
    | empty => acc
    | node v l r => BTree_toList'_aux l (v :: BTree_toList'_aux r acc)
end.

Definition BTree_toList' {A : LinDec} (t : BTree A) : list A :=
  BTree_toList'_aux t [].

(** [size] and counting. *)
Fixpoint size {A : Type} (bt : BTree A) : nat :=
match bt with
    | empty => 0
    | node _ l r => S (size l + size r)
end.

Fixpoint count_BTree {A : LinDec} (x : A) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        let n := count_BTree x l in
        let m := count_BTree x r in
        if x =? v then S (n + m) else n + m
end.

(** * Tactics *)
Ltac elem :=
  intros; unfold singleton in *; cbn in *; subst; repeat
match goal with
    | |- elem ?x (node ?x _ _) => constructor
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ empty empty) |- _ => inv H
    | H : elem _ _ /\ elem _ _ |- _ => destruct H
    | H : elem _ _ \/ elem _ _ |- _ => destruct H
end; auto.

(** * Theorems *)

(** Propertes of [elem] and [elem_decb]. *)
Lemma elem_decb_reflect :
  forall (A : LinDec) (x : A) (t : BTree A),
    reflect (elem x t) (elem_decb x t).
Proof.
  induction t as [| v l IHl r IHr]; cbn.
    constructor. inv 1.
    dec. destruct IHl, IHr; auto.
      constructor. inv 1.
Qed.

(** Properties of casts to/from list. *)

Lemma BTree_toList'_aux_spec :
  forall (A : LinDec) (t : BTree A) (acc : list A),
    BTree_toList'_aux t acc = BTree_toList t ++ acc.
Proof.
  intros. functional induction @BTree_toList'_aux A t acc; cbn.
    trivial.
    rewrite <- app_assoc. cbn. rewrite <- IHl, <- IHl0. trivial.
Qed.

Theorem BTree_toList'_spec : @BTree_toList' = @BTree_toList.
Proof.
  ext A. ext t. unfold BTree_toList'.
  rewrite BTree_toList'_aux_spec, app_nil_r. trivial.
Qed.

Lemma toList_In_elem :
  forall (A : Type) (x : A) (t : BTree A),
    In x (BTree_toList t) <-> elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; firstorder.
Qed.

(** Properties of [size]. *)

Lemma size_swap :
  forall (A : Type) (v : A) (l r : BTree A),
    size (node v l r) = size (node v r l).
Proof.
  intros. cbn. rewrite plus_comm. trivial.
Qed.

Lemma size_length :
  forall (A : Type) (t : BTree A),
    length (BTree_toList t) = size t.
Proof.
  induction t; cbn.
    reflexivity.
    rewrite !app_length. cbn. rewrite IHt1, IHt2. omega.
Qed.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (BTree_toList t) = count_BTree x t.
Proof.
  induction t; cbn; rewrite ?count_app; dec.
Qed.

(** Properties of [empty]. *)
Lemma empty_elem :
  forall (A : LinDec) (x : A), ~ elem x empty.
Proof. inv 1. Qed.

Lemma empty_isHeap :
  forall A : LinDec, isHeap (@empty A).
Proof. constructor. Qed.

Lemma empty_size :
  forall A : LinDec, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma empty_count_BTree :
  forall (A : LinDec) (x : A),
    count_BTree x empty = 0.
Proof. reflexivity. Qed.

(** Properties of [singleton]. *)

Lemma singleton_elem :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  split; elem.
Qed.

Lemma singleton_isHeap :
  forall (A : LinDec) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton. constructor; auto; inv 1.
Qed.

Lemma singleton_size :
  forall (A : LinDec) (x : A),
    size (singleton x) = 1.
Proof. reflexivity. Qed.

Lemma singleton_count_BTree :
  forall (A : LinDec) (x y : A),
    count_BTree x (singleton y) = if x =? y then 1 else 0.
Proof. dec. Qed.

(** Properties of [isEmpty]. *)

Lemma isEmpty_elem_false :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = false <-> exists x : A, elem x t.
Proof.
  split; destruct t; cbn; firstorder.
    eauto.
    inv H.
Qed.

Lemma isEmpty_elem_true :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true <-> forall x : A, ~ elem x t.
Proof.
  split; destruct t; cbn; firstorder.
    inv 1.
    contradiction (H c). auto.
Qed.

Lemma isEmpty_isHeap :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true -> isHeap t.
Proof.
  destruct t; firstorder.
Qed.

Lemma isEmpty_empty :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> t = empty.
Proof.
  destruct t; cbn; firstorder. inv H.
Qed.

Lemma isEmpty_singleton :
  forall (A : Type) (x : A),
    isEmpty (singleton x) = false.
Proof. reflexivity. Qed.

Lemma isEmpty_size_false :
  forall (A : Type) (t : BTree A),
    isEmpty t = false <-> size t <> 0.
Proof.
  split; destruct t; cbn; firstorder.
Qed.

Lemma isEmpty_size_true :
  forall (A : Type) (t : BTree A),
    isEmpty t = true <-> size t = 0.
Proof.
  split; destruct t; cbn; congruence.
Qed.

Lemma isEmpty_count_BT :
  forall (A : LinDec) (t : BTree A),
    isEmpty t = true <-> forall x : A, count_BTree x t = 0.
Proof.
  split; destruct t; cbn; try congruence.
    intro. specialize (H c). dec.
Qed.