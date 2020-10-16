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

Arguments E {A}.
Arguments T {A} _ _ _.

Inductive elem {A : Type} (x : A) : RBTree A -> Prop :=
    | elem_root : forall (c : color) (l r : RBTree A),
        elem x (T c l x r)
    | elem_left : forall (c : color) (v : A) (l r : RBTree A),
        elem x l -> elem x (T c l v r)
    | elem_right : forall  (c : color) (v : A) (l r : RBTree A),
        elem x r -> elem x (T c l v r).

Inductive isBST {A : LinDec} : RBTree A -> Prop :=
    | isBST_E : isBST E
    | isBST_T : forall (c : color) (v : A) (l r : RBTree A),
        (forall x : A, elem x l -> leq x v) -> isBST l ->
        (forall x : A, elem x r -> leq v x) -> isBST r ->
        isBST (T c l v r).

Hint Constructors color RBTree elem isBST : core.

(** [empty], [isEmpty] and [singleton] are my own. *)
Definition empty {A : Type} : RBTree A := E.

Definition isEmpty {A : Type} (t : RBTree A) : bool :=
match t with
    | E => true
    | _ => false
end.

Definition singleton {A : Type} (x : A) : RBTree A := T Red E x E.

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

Fixpoint count_RBT {A : Type} (p : A -> bool) (t : RBTree A) : nat :=
match t with
    | E => 0
    | T _ l v r =>
        (if p v then S else id) (count_RBT p l + count_RBT p r)
end.

Function toList {A : Type} (t : RBTree A) : list A :=
match t with
    | E => []
    | T _ l v r => toList l ++ v :: toList r
end.

Fixpoint fromList {A : LinDec} (l : list A) : RBTree A :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

Definition redblackSort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

(*Definition redblackSort' (A : LinDec) (l : list A) : list A :=
  toList' (fromList' l).*)

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall (A : LinDec) (c : color) (v : A) (l r : RBTree A),
    isEmpty (balance c l v r) = false.
Proof.
  intros. functional induction @balance (@carrier A) c l v r;
  cbn; reflexivity.
Qed.

Lemma isEmpty_makeBlack :
  forall (A : LinDec) (t : RBTree A),
    isEmpty (makeBlack t) = isEmpty t.
Proof.
  destruct t; cbn; reflexivity.
Qed.

Lemma isEmpty_ins :
  forall (A : LinDec) (x : A) (t : RBTree A),
    isEmpty (ins x t) = false.
Proof.
  intros. functional induction @ins A x t;
  cbn; rewrite ?isEmpty_balance; reflexivity.
Qed.

Lemma isEmpty_insert :
  forall (A : LinDec) (x : A) (t : RBTree A),
    isEmpty (insert x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_makeBlack, isEmpty_ins. reflexivity.
Qed.

(** Properties of [singleton]. *)

Lemma singleton_elem :
  forall (A : LinDec) (x y : A),
    elem x (singleton y) <-> x = y.
Proof.
  unfold singleton. split.
    inv 1; inv H1.
    intros ->. auto.
Qed.

Lemma singleton_isBST :
  forall (A : LinDec) (x : A),
    isBST (singleton x).
Proof.
  unfold singleton. intros. constructor; auto; inv 1.
Qed.

(** Properties of [balance]. *)

Lemma elem_inv :
  forall (A : Type) (P : A -> Prop) (c : color) (v : A) (l r : RBTree A),
    (forall x : A, elem x (T c l v r) -> P x) ->
      P v /\
      (forall x : A, elem x l -> P x) /\
      (forall x : A, elem x r -> P x).
Proof.
  repeat split; intros; apply H; auto.
Qed.

Ltac aux := intros;
repeat match goal with
    | H : context [match ?x with _ => _ end] |- _ => destruct x
end; cbn in *;
try match goal with
    | H : False |- _ => destruct H
end;
repeat match goal with
    | H : isBST (T _ _ _ _) |- _ => inv H
    | H : elem _ E |- _ => destruct H
    | H : elem _ (T _ _ _ _) |- _ => inv H
    | |- isBST _ => constructor; auto
    | |- forall _, elem _ _ -> _ => inv 1
end;
repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : forall _, elem _ (T _ _ _ _) -> _ |- _ =>
        apply elem_inv in H
end;
repeat match goal with
    | H : forall _, elem _ _ -> _, H' : elem _ _ |- _ =>
        specialize (H _ H')
end;
try match goal with
    | H : ?a ≤ ?b |- ?a ≤ ?b => assumption
    | H : ?a ≤ ?b, H' : ?b≤ ?c |- ?a ≤ ?c =>
        apply leq_trans with b; assumption
end.

Lemma balance_elem :
  forall (A : LinDec) (c : color) (x v : A) (l r : RBTree A),
    elem x (T c l v r) <-> elem x (balance c l v r).
Proof.
  split; functional induction @balance (@carrier A) c l v r; aux.
Qed.

Lemma balance_isBST :
  forall (A : LinDec) (c : color) (v : A) (l r : RBTree A),
    isBST (T c l v r) -> isBST (balance c l v r).
Proof.
  intros; functional induction @balance (@carrier A) c l v r; aux.
Qed.

Ltac destruct_if := repeat
match goal with
    | |- context [if ?p then _ else _] => destruct p
end.

Lemma balance_count_RBT :
  forall (A : Type) (p : A -> bool) (c : color) (v : A) (l r : RBTree A),
    count_RBT p (balance c l v r) = count_RBT p (T c l v r).
Proof.
  intros. functional induction @balance A c l v r;
  cbn; destruct_if;
  unfold id; try lia.
Qed.

(** Properties of [makeBlack]. *)

Lemma makeBlack_elem :
  forall (A : LinDec) (x : A) (t : RBTree A),
    elem x (makeBlack t) <-> elem x t.
Proof.
  split; destruct t; cbn; auto; inv 1.
Qed.

Lemma makeBlack_isBST :
  forall (A : LinDec) (t : RBTree A),
    isBST t -> isBST (makeBlack t).
Proof.
  destruct t; cbn; inv 1.
Qed.

Lemma makeBlack_count_RBT :
  forall (A : Type) (p : A -> bool) (t : RBTree A),
    count_RBT p (makeBlack t) = count_RBT p t.
Proof.
  destruct t; reflexivity.
Qed.

(** Properties of [ins]. *)

Lemma ins_elem :
  forall (A : LinDec) (x y : A) (t : RBTree A),
    elem x (ins y t) <-> x = y \/ elem x t.
Proof.
  split.
    induction t; cbn; intros.
      inv H.
      dec; rewrite <- balance_elem in H; inv H; firstorder.
    induction t; cbn; intros.
      inv H.
      dec; rewrite <- balance_elem; inv H; inv H0.
Qed.

Lemma ins_isBST :
  forall (A : LinDec) (x : A) (t : RBTree A),
    isBST t -> isBST (ins x t).
Proof.
  intros. functional induction ins x t.
    constructor; auto; inv 1.
    apply balance_isBST. inv H. constructor; auto.
      intros. rewrite ins_elem in H. destruct H; subst; dec.
    apply balance_isBST. inv H. constructor; auto.
      intros. rewrite ins_elem in H. destruct H; subst; dec.
Qed.

Lemma ins_count_RBT :
  forall (A : LinDec) (p : A -> bool) (x : A) (t : RBTree A),
    count_RBT p (ins x t) = (if p x then S else id) (count_RBT p t).
Proof.
  induction t; cbn; dec;
  rewrite balance_count_RBT; cbn; rewrite ?IHt1, ?IHt2;
  destruct_if; unfold id; lia.
Qed.

(** Properties of [insert]. *)

Lemma insert_elem :
  forall (A : LinDec) (x y : A) (t : RBTree A),
    elem x (insert y t) <-> x = y \/ elem x t.
Proof.
  unfold insert. intros. rewrite makeBlack_elem, ins_elem. reflexivity.
Qed.

Lemma insert_isBST :
  forall (A : LinDec) (x : A) (t : RBTree A),
    isBST t -> isBST (insert x t).
Proof.
  intros. unfold insert. apply makeBlack_isBST, ins_isBST. assumption.
Qed.

Lemma insert_count_RBT :
  forall (A : LinDec) (p : A -> bool) (x : A) (t : RBTree A),
    count_RBT p (insert x t) = (if p x then S else id) (count_RBT p t).
Proof.
  intros. unfold insert.
  rewrite makeBlack_count_RBT, ins_count_RBT. reflexivity.
Qed.

Lemma Permutation_toList_balance :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    Permutation (toList (balance c l v r)) (toList (T c l v r)).
Proof.
  intros. functional induction @balance A c l v r; cbn.
    reflexivity.
    rewrite <- !app_assoc. cbn. reflexivity.
    rewrite <- !app_assoc. cbn. rewrite <- !app_assoc. cbn. reflexivity.
    rewrite <- !app_assoc. cbn. reflexivity.
    rewrite <- !app_assoc. cbn. reflexivity.
    reflexivity.
Qed.

Lemma Permutation_toList_ins :
  forall (A : LinDec) (x : A) (t : RBTree A),
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
  forall (A : LinDec) (x : A) (t : RBTree A),
    Permutation (toList (insert x t)) (x :: toList t).
Proof.
  intros. unfold insert. destruct (ins x t) eqn: Heq; cbn.
    admit.
    rewrite <- (Permutation_toList_ins _ x t). rewrite Heq.
      cbn. reflexivity.
Admitted.

(** Properties of [toList]. *)

Lemma toList_elem :
  forall (A : Type) (x : A) (t : RBTree A),
    In x (toList t) <-> elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; apply in_or_app; firstorder.
Qed.

Lemma toList_count_RBT :
  forall (A : Type) (p : A -> bool) (t : RBTree A),
    count_RBT p t = count p (toList t).
Proof.
  induction t; cbn.
    reflexivity.
    rewrite count_app, IHt1, IHt2.
      cbn. destruct (p a); auto.
Qed.

Lemma Sorted_toList :
  forall (A : LinDec) (t : RBTree A),
    isBST t -> Sorted A (toList t).
Proof.
  induction t as [| c l Hl v r Hr]; cbn; intros.
    constructor.
    inv H. apply Sorted_app_all; auto.
      case_eq (toList r); intros; subst; auto. constructor.
        apply H6. rewrite <- toList_elem. rewrite H. cbn. auto.
        rewrite <- H. auto.
      intros. apply toList_elem in H. auto.
Qed.

(** Properties of [fromList]. *)

Lemma fromList_elem :
  forall (A : LinDec) (x : A) (l : list A),
    elem x (fromList l) <-> In x l.
Proof.
  split.
    induction l as [| h t]; cbn; intros.
      inv H.
      rewrite insert_elem in H. inv H.
    induction l as [| h t]; cbn; intros.
      inv H.
      rewrite insert_elem. inv H.
Qed.

Lemma fromList_isBST :
  forall (A : LinDec) (l : list A),
    isBST (fromList l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply insert_isBST. assumption.
Qed.

Lemma fromList_count_RBT :
  forall (A : LinDec) (p : A -> bool) (l : list A),
    count_RBT p (fromList l) = count p l.
Proof.
  induction l as [| h t]; cbn; dec;
  rewrite insert_count_RBT, IHt.
  destruct (p h); reflexivity.
Qed.

(** Properties of [redblackSort]. *)

Lemma Sorted_redblackSort :
  forall (A : LinDec) (l : list A),
    Sorted A (redblackSort A l).
Proof.
  intros. unfold redblackSort. apply Sorted_toList, fromList_isBST.
Qed.

Lemma redblackSort_perm :
  forall (A : LinDec) (l : list A),
    perm l (redblackSort A l).
Proof.
  unfold perm, redblackSort. intros.
  rewrite <- toList_count_RBT, fromList_count_RBT. reflexivity.
Qed.

Lemma Permutation_redblackSort :
  forall (A : LinDec) (l : list A),
    Permutation (redblackSort A l) l.
Proof.
  intros. unfold redblackSort.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite Permutation_toList_insert, IHt. reflexivity.
Qed.

(** TODO: [join] and [split] *)