Require Export RCCBase.

Require Export BTree.
Require Export Ord.

Require Export EBTree.

Inductive color : Set :=
    | Red : color
    | Black : color.

Definition RBTree (A : Type) : Type := EBTree color A.

Inductive isBST {A : Ord} : RBTree A -> Prop :=
    | isBST_E : isBST E
    | isBST_N : forall (c : color) (v : A) (l r : RBTree A),
        (forall x : A, Elem x l -> x ≤ v) -> isBST l ->
        (forall x : A, Elem x r -> x >= v) -> isBST r ->
        isBST (N c l v r).

Hint Constructors color EBTree Elem isBST : core.

Ltac isBST :=
repeat match goal with
    | H : isBST E           |- _       => clear H
    | H : isBST (N _ _ _ _) |- _       => inv H
    |                       |- isBST E => constructor
end.

Ltac isBST' :=
repeat match goal with
    | H : isBST E           |- _       => clear H
    | H : isBST (N _ _ _ _) |- _       => inv H
    |                       |- isBST _ => constructor; intros; auto
end.

(** [empty], [isEmpty] and [singleton] are my own. *)
Definition empty {A : Type} : RBTree A := E.

Definition singleton {A : Type} (x : A) : RBTree A := N Red E x E.

Function balance {A : Type} (c : color)
  (l : RBTree A) (v : A) (r : RBTree A) : RBTree A :=
match c with
    | Red => N Red l v r
    | Black =>
        match l, v, r with
            | N Red (N Red a xv b) yv c, zv, d
            | N Red a xv (N Red b yv c), zv, d
            | a, xv, N Red (N Red b yv c) zv d
            | a, xv, N Red b yv (N Red c zv d) =>
                N Red (N Black a xv b) yv (N Black c zv d)
            | l, v, r => N Black l v r
        end
end.

Definition makeBlack {A : Type} (t : RBTree A) :=
match t with
    | E => E
    | N _ l v r => N Black l v r
end.

Function ins {A : Ord} (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => N Red E x E
    | N c l v r =>
        if x ≤? v
        then balance c (ins x l) v r
        else balance c l v (ins x r)
end.

Definition insert {A : Ord} (x : A) (t : RBTree A) : RBTree A :=
  makeBlack (ins x t).

Fixpoint fromList {A : Ord} (l : list A) : RBTree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Definition redblackSort (A : Ord) (l : list A) : list A :=
  toList (fromList l).

(*Definition redblackSort' (A : Ord) (l : list A) : list A :=
  toList' (fromList' l).*)

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : Ord) (c : color) (v : A) (l r : RBTree A),
    isEmpty (balance c l v r) = false.
Proof.
  intros. functional induction @balance (@carrier A) c l v r;
  cbn; reflexivity.
Qed.

Lemma isEmpty_makeBlack :
  forall (A : Ord) (t : RBTree A),
    isEmpty (makeBlack t) = isEmpty t.
Proof.
  destruct t; cbn; reflexivity.
Qed.

Lemma isEmpty_ins :
  forall (A : Ord) (x : A) (t : RBTree A),
    isEmpty (ins x t) = false.
Proof.
  intros. functional induction @ins A x t;
  cbn; rewrite ?isEmpty_balance; reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : Ord) (x : A) (t : RBTree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_makeBlack, isEmpty_ins. reflexivity.
Qed.

(** Properties of [singleton]. *)

Lemma Elem_singleton :
  forall (A : Ord) (x y : A),
    Elem x (singleton y) <-> x = y.
Proof.
  unfold singleton. split.
    inv 1; inv H1.
    intros ->. auto.
Qed.

Lemma isBST_singleton :
  forall (A : Ord) (x : A),
    isBST (singleton x).
Proof.
  unfold singleton. intros. constructor; auto; inv 1.
Qed.

(** Properties of [balance]. *)

Lemma Elem_balance :
  forall (A : Ord) (c : color) (x v : A) (l r : RBTree A),
    Elem x (N c l v r) <-> Elem x (balance c l v r).
Proof.
  split;
  functional induction balance c l v r;
  auto; intros; Elem'.
Qed.

Lemma isBST_balance :
  forall (A : Ord) (c : color) (v : A) (l r : RBTree A),
    isBST (N c l v r) -> isBST (balance c l v r).
Proof.
  intros.
  functional induction balance c l v r;
  isBST'; Elem'; trich.
Qed.

Lemma countEBT_balance :
  forall (A : Type) (p : A -> bool) (c : color) (v : A) (l r : RBTree A),
    countEBT p (balance c l v r) = countEBT p (N c l v r).
Proof.
  intros.
  functional induction balance c l v r;
  cbn;
  repeat match goal with
      | |- context [if ?p then _ else _] => destruct p
  end;
  lia.
Qed.

(** Properties of [makeBlack]. *)

Lemma Elem_makeBlack :
  forall (A : Ord) (x : A) (t : RBTree A),
    Elem x (makeBlack t) <-> Elem x t.
Proof.
  split; destruct t; cbn; auto; inv 1.
Qed.

Lemma isBST_makeBlack :
  forall (A : Ord) (t : RBTree A),
    isBST t -> isBST (makeBlack t).
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma countEBT_makeBlack :
  forall (A : Type) (p : A -> bool) (t : RBTree A),
    countEBT p (makeBlack t) = countEBT p t.
Proof.
  destruct t; reflexivity.
Qed.

(** Properties of [ins]. *)

Lemma Elem_ins :
  forall (A : Ord) (x y : A) (t : RBTree A),
    Elem x (ins y t) <-> x = y \/ Elem x t.
Proof.
  intros until t. revert x.
  functional induction ins y t;
  intros; rewrite <- ?Elem_balance, ?Elem_N, ?IHl, ?IHr;
  firstorder.
Qed.

Lemma isBST_ins :
  forall (A : Ord) (x : A) (t : RBTree A),
    isBST t -> isBST (ins x t).
Proof.
  intros. functional induction ins x t.
    constructor; auto; inv 1.
    apply isBST_balance. inv H. constructor; auto.
      intros. rewrite Elem_ins in H. inv H. trich.
    apply isBST_balance. inv H. constructor; auto.
      intros. rewrite Elem_ins in H. inv H. trich.
Qed.

Lemma countEBT_ins :
  forall (A : Ord) (p : A -> bool) (x : A) (t : RBTree A),
    countEBT p (ins x t) = (if p x then 1 else 0) + countEBT p t.
Proof.
  induction t; cbn; trich;
  rewrite countEBT_balance; cbn; rewrite ?IHt1, ?IHt2;
  repeat match goal with
      | |- context [if ?p then _ else _] => destruct p
  end;
  lia.
Qed.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall (A : Ord) (x y : A) (t : RBTree A),
    Elem x (insert y t) <-> x = y \/ Elem x t.
Proof.
  unfold insert. intros. rewrite Elem_makeBlack, Elem_ins. reflexivity.
Qed.

Lemma isBST_insert :
  forall (A : Ord) (x : A) (t : RBTree A),
    isBST t -> isBST (insert x t).
Proof.
  intros. unfold insert. apply isBST_makeBlack, isBST_ins. assumption.
Qed.

Lemma countEBT_insert :
  forall (A : Ord) (p : A -> bool) (x : A) (t : RBTree A),
    countEBT p (insert x t) = (if p x then 1 else 0) + countEBT p t.
Proof.
  intros. unfold insert.
  rewrite countEBT_makeBlack, countEBT_ins. reflexivity.
Qed.

Lemma Permutation_toList_balance :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    Permutation (toList (balance c l v r)) (toList (N c l v r)).
Proof.
  intros.
  functional induction balance c l v r;
  cbn; rewrite <- ?app_assoc; cbn;
  try reflexivity.
    rewrite <- !app_assoc. cbn. reflexivity.
Qed.

Lemma Permutation_toList_ins :
  forall (A : Ord) (x : A) (t : RBTree A),
    Permutation (toList (ins x t)) (x :: toList t).
Proof.
  intros. functional induction @ins A x t.
    cbn. reflexivity.
    rewrite Permutation_toList_balance. cbn. rewrite IHr. cbn. reflexivity.
    rewrite Permutation_toList_balance. cbn. rewrite IHr.
      rewrite Permutation_middle. apply Permutation_app.
        reflexivity.
        constructor.
Qed.

Lemma Permutation_toList_insert :
  forall (A : Ord) (x : A) (t : RBTree A),
    Permutation (toList (insert x t)) (x :: toList t).
Proof.
  intros. unfold insert. destruct (ins x t) eqn: Heq; cbn.
    apply (f_equal (countEBT (fun _ => true))) in Heq.
      rewrite countEBT_ins in Heq. cbn in Heq. inv Heq.
    rewrite <- (Permutation_toList_ins _ x t). rewrite Heq.
      cbn. reflexivity.
Qed.

(** Properties of [toList]. *)

Lemma Elem_toList :
  forall (A : Type) (x : A) (t : RBTree A),
    In x (toList t) <-> Elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; apply in_or_app; firstorder.
Qed.

Require Export Sorting.Sort.

Lemma toList_countEBT :
  forall (A : Type) (p : A -> bool) (t : RBTree A),
    countEBT p t = count p (toList t).
Proof.
  induction t; cbn.
    reflexivity.
    rewrite count_app, IHt1, IHt2.
      cbn. destruct (p a); lia.
Qed.

Lemma Sorted_toList :
  forall (A : Ord) (t : RBTree A),
    isBST t -> Sorted trich_le (toList t).
Proof.
  induction t as [| c l Hl v r Hr]; cbn; intros.
    constructor.
    inv H. apply Sorted_app_all; auto.
      case_eq (toList r); intros; subst; auto. constructor.
        apply H6. rewrite <- Elem_toList. rewrite H. cbn. auto.
        rewrite <- H. auto.
      intros. apply Elem_toList in H. auto.
Qed.

(** Properties of [fromList]. *)

Lemma Elem_fromList :
  forall (A : Ord) (x : A) (l : list A),
    Elem x (fromList l) <-> In x l.
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inv H.
      rewrite Elem_insert in H. inv H.
    induction l as [| h t]; cbn; intros.
      inv H.
      rewrite Elem_insert. inv H.
Qed.

Lemma isBST_fromList :
  forall (A : Ord) (l : list A),
    isBST (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insert. assumption.
Qed.

Lemma countEBT_fromList :
  forall (A : Ord) (p : A -> bool) (l : list A),
    countEBT p (fromList l) = count p l.
Proof.
  induction l as [| h t]; cbn; trich;
  rewrite countEBT_insert, IHt.
  destruct (p h); reflexivity.
Qed.

(** Properties of [redblackSort]. *)

Lemma Sorted_redblackSort :
  forall (A : Ord) (l : list A),
    Sorted trich_le (redblackSort A l).
Proof.
  intros. unfold redblackSort. apply Sorted_toList, isBST_fromList.
Qed.

Lemma perm_redblackSort :
  forall (A : Ord) (l : list A),
    perm l (redblackSort A l).
Proof.
  unfold perm, redblackSort. intros.
  rewrite <- toList_countEBT, countEBT_fromList. reflexivity.
Qed.

Lemma Permutation_redblackSort :
  forall (A : Ord) (l : list A),
    Permutation (redblackSort A l) l.
Proof.
  intros. unfold redblackSort.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_toList_insert, IHt. reflexivity.
Qed.

(** TODO: implement [join] and [split] *)