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

(** The [elem] predicate. *)
Inductive elem {A : Type} (a : A) : BTree A -> Prop :=
    | elem_root : forall l r : BTree A, elem a (node a l r)
    | elem_left : forall (v : A) (l r : BTree A),
        elem a l -> elem a (node v l r)
    | elem_right : forall (v : A) (l r : BTree A),
        elem a r -> elem a (node v l r).

Hint Constructors elem.

(*Theorem elem_dec :
  forall {A : Type} {dec : EqDec A eq} (a : A) (t : BTree A),
    {elem a t} + {~ elem a t}.
Proof.
  induction t as [| v l [IHl | IHl] r [IHr | IHr]]; auto.
    right. inv 1.
    destruct (dec a v).
      left. rewrite  e. auto.
      right. inv 1.
Defined.*)

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