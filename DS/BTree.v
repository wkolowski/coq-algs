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

Fixpoint size {A : Type} (bt : BTree A) : nat :=
match bt with
    | empty => 0
    | node _ l r => S (size l + size r)
end.

Lemma size_swap :
  forall (A : Type) (v : A) (l r : BTree A),
    size (node v l r) = size (node v r l).
Proof.
  intros. cbn. rewrite plus_comm. trivial.
Qed.

Definition root {A : Type} (bt : BTree A) : option A :=
match bt with
    | empty => None
    | node v l r => Some v
end.

Fixpoint map {A B : Type} (f : A -> B) (bt : BTree A) : BTree B :=
match bt with
    | empty => empty
    | node v l r => node (f v) (map f l) (map f r)
end.

(*From mathcomp Require Import ssreflect.*)

Theorem map_pres_size : forall (A B : Type) (f : A -> B) (bt : BTree A),
    size bt = size (map f bt).
Proof.
  induction bt as [| v l Hl r Hr]; cbn; intros;
  rewrite <- ?Hl, <- ?Hr; reflexivity.
(*Restart.
  intros. elim: bt => //= v l -> r -> //=. *)
Qed.

Fixpoint combine
  {A B : Type} (ta : BTree A) (tb : BTree B) : BTree (A * B) :=
match ta, tb with
    | empty, _ => empty
    | _, empty => empty
    | node v1 l1 r1, node v2 l2 r2 =>
        node (v1, v2) (combine l1 l2) (combine r1 r2)
end.

Fixpoint fold
  {A B : Set} (op : A -> B -> B -> B) (b : B) (bt : BTree A) : B :=
match bt with
    | empty => b
    | node v l r => op v (fold op b l) (fold op b r)
end.

Definition bool_to_nat (b : bool) : nat :=
match b with
    | true => 1
    | false => 0
end.

Definition size_fold {A : Set} := @fold A nat (fun _ l r => 1 + l + r) 0.
Definition sum_fold := fold (fun v l r => v + l + r) 0.
Definition find_fold (n : nat) : BTree nat -> bool :=
    fold (fun v l r => orb (beq_nat v n) (orb l r)) false.
Definition count_fold (n : nat) : BTree nat -> nat :=
    fold (fun v l r => bool_to_nat (beq_nat v n) + l + r) 0.
Definition map_fold {A B : Set} (f : A -> B) : BTree A -> BTree B :=
    fold (fun v l r => node (f v) l r) empty.

Inductive elem {A : Type} (a : A) : BTree A -> Prop :=
    | elem_root : forall l r : BTree A, elem a (node a l r)
    | elem_left : forall (v : A) (l r : BTree A),
        elem a l -> elem a (node v l r)
    | elem_right : forall (v : A) (l r : BTree A),
        elem a r -> elem a (node v l r).

Hint Constructors elem.

Theorem elem_dec :
  forall {A : Type} {dec : EqDec A eq} (a : A) (t : BTree A),
    {elem a t} + {~ elem a t}.
Proof.
  induction t as [| v l IHl r IHr].
    right. inversion 1.
    destruct (dec a v).
      left. rewrite <- e. constructor.
      destruct IHl as [IHl1 | IHl2].
        left. apply elem_left. assumption.
        destruct IHr as [IHr1 | IHr2].
          left. apply elem_right; assumption.
          right. intro. inversion H; contradiction.
(*Restart.
  intros. elim: t => [| v l [Hl | Hl] r [Hr | Hr]]; auto.
    right. inversion 1.
    case: (dec a v) => H; [left | right].
      by rewrite H.
      by inversion 1.*)
Defined.

Fixpoint elem_decb
  {A : Type} (dec : EqDec A eq) (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        if dec x v
        then true
        else elem_decb dec x l || elem_decb dec x r
end.

Require Import Bool.

Lemma elem_decb_reflect :
  forall (A : Type) (dec : EqDec A eq) (x : A) (t : BTree A),
    reflect (elem x t) (elem_decb dec x t).
Proof.
  induction t as [| v l IHl r IHr]; cbn.
    constructor. inversion 1.
    destruct (dec x v), IHl, IHr; try inv e; cbn; auto.
      constructor. intro. inv H. contradiction c. reflexivity.
Qed.

(* toList, fromList and their variants *)
Function BTree_toList {A : Type} (t : BTree A) : list A :=
match t with
    | empty => []
    | node v l r => BTree_toList l ++ v :: BTree_toList r
end.

Function toList'_aux {A : LinDec} (t : BTree A) (acc : list A) : list A :=
match t with
    | empty => acc
    | node v l r => toList'_aux l (v :: toList'_aux r acc)
end.

Definition toList' {A : LinDec} (t : BTree A) : list A :=
  toList'_aux t [].

Lemma toList'_aux_spec :
  forall (A : LinDec) (t : BTree A) (acc : list A),
    toList'_aux t acc = BTree_toList t ++ acc.
Proof.
  intros. functional induction @toList'_aux A t acc; cbn.
    trivial.
    rewrite <- app_assoc. cbn. rewrite <- IHl, <- IHl0. trivial.
Qed.

Theorem toList'_spec : @toList' = @BTree_toList.
Proof.
  ext A. ext t. unfold toList'.
  rewrite toList'_aux_spec, app_nil_r. trivial.
Qed.

(* Counting elements in a binary tree. *)
Fixpoint count_BTree (A : LinDec) (x : A) (t : BTree A) : nat :=
match t with
    | empty => 0
    | node v l r =>
        let n := count_BTree A x l in
        let m := count_BTree A x r in
        if x =? v then S (n + m) else n + m
end.

Lemma count_toList :
  forall (A : LinDec) (x : A) (t : BTree A),
    count A x (BTree_toList t) = count_BTree A x t.
Proof.
  induction t; cbn; rewrite ?count_app; dec.
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