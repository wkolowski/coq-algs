Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export BTree.
Require Export LinDec.
Require Export Sorting.Sort.

Inductive color : Set :=
    | Red : color
    | Black : color.

Inductive RBTree (A : Type) : Type :=
    | E : RBTree A
    | T : color -> RBTree A -> A -> RBTree A -> RBTree A.

Arguments E [A].
Arguments T [A] _ _ _.

Inductive elem {A : Type} (x : A) : RBTree A -> Prop :=
    | elem_root : forall (c : color) (l r : RBTree A),
        elem x (T c l x r)
    | elem_left : forall (c : color) (v : A) (l r : RBTree A),
        elem x l -> elem x (T c l v r)
    | elem_right : forall  (c : color) (v : A) (l r : RBTree A),
        elem x r -> elem x (T c l v r).

Hint Constructors color RBTree elem.

Ltac inv H := inversion H; clear H; subst; cbn; auto.

Lemma elem_color :
  forall (A : Type) (c c' : color) (x v : A) (l r : RBTree A),
    elem x (T c l v r) -> elem x (T c' l v r).
Proof.
  intros; inv H.
Qed.

Function balance {A : Type} (c : color)
  (l : RBTree A) (v : A) (r : RBTree A) : RBTree A :=
match c with
    | Red => T Red l v r
    | Black =>
        match l, v, r with
            | T Red (T Red a xv b) yv c, zv, d
            | T Red a xv (T Red b yv c), zv, d
            | a, xv, T Red (T Red b yv c) zv d
            | a, xv, T Red b yv (T Red c zv d) =>
                T Red (T Black a xv b) yv (T Black c zv d)
            | l, v, r => T Black l v r
        end
end.

Definition makeBlack {A : Type} (t : RBTree A) :=
match t with
    | E => E
    | T _ l v r => T Black l v r
end.

(*Function ins {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => T Red E x E
    | T c l v r =>
        if x <=? v
        then balance c (ins x l) v r
        else if v <=? x
          then balance c l v (ins x r)
          else T c l x r
end.*)

Function ins {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => T Red E x E
    | T c l v r =>
        if x <=? v
        then balance c (ins x l) v r
        else balance c l v (ins x r)
end.

Definition insert {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
  makeBlack (ins x t).

Require Import Coq.Logic.FunctionalExtensionality.

Lemma T_not_E :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    T c l v r <> E.
Proof.
  inversion 1.
Qed.

Lemma balance_not_E :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    balance c l v r <> E.
Proof.
  intros. functional induction @balance A c l v r; apply T_not_E.
Qed.

Lemma balance_is_T :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    exists (c' : color) (v' : A) (l' r' : RBTree A),
      balance c l v r = T c' l' v' r'.
Proof.
  intros. functional induction @balance A c l v r; eauto 6.
Qed.

(*Ltac dst := repeat
match goal with
    | |- context [if ?x then _ else _] => destruct x
    | |- context [match ?x with _ => _ end] => destruct x
end; try apply T_not_E.*)

Lemma ins_not_E :
  forall (A : LinDec) (x : A) (t : RBTree A),
    ins x t <> E.
Proof.
  intros. functional induction @ins A x t;
  try apply T_not_E; apply balance_not_E.
Qed.

Inductive is_bst {A : LinDec} : RBTree A -> Prop :=
    | is_bst_E : is_bst E
    | is_bst_T : forall (c : color) (v : A) (l r : RBTree A),
        (forall x : A, elem x l -> leq x v) -> is_bst l ->
        (forall x : A, elem x r -> leq v x) -> is_bst r ->
        is_bst (T c l v r).

Hint Constructors is_bst.

Lemma color_is_bst :
  forall (A : LinDec) (c c' : color) (v : A) (l r : RBTree A),
    is_bst (T c l v r) <-> is_bst (T c' l v r).
Proof.
  split; intros; inv H.
Qed.

Hint Resolve elem_color.

(*Lemma balance_is_bst :
  forall (A : LinDec) (c : color) (v : A) (l r : RBTree A),
    is_bst (T c l v r) -> is_bst (balance c l v r).
Proof.
  intros. functional induction @balance (@carrier A) c l v r;
  try assumption.
    inv H. inv H5. inv H8. constructor; intros; auto.
      apply H3. eapply elem_color. eauto.
      inv H.
      apply H3.
      apply *)

(*Ltac bd := intros; repeat (match goal with
    | |- context [if ?x then _ else _] =>
        bdestruct (x); subst; cbn in *; try discriminate; auto
    | H : (?x <? ?y) = _ |- _ => destruct (blt_reflect x y); try congruence
    | H : ?x <> ?x |- _ => contradiction
    | H : ?x = ?x |- _ => clear H
    | H : ~ ?x < ?y, H' : ~ ?y < ?x |- _ =>
        assert (x = y) by (unfold key in *; omega); subst; clear H; clear H'
    | H : Abs E _ |- _ => inv H    
    | H : Abs (T _ _ _ _ _) _ |- _ => inv H
    | _ => auto; omega
end; st; cbn in *)
