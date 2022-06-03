From CoqAlgs Require Export Base.
From CoqAlgs Require Export Ord.
(* From CoqAlgs Require Export BTree. *)
From CoqAlgs Require Export EBTree.
(* From CoqAlgs Require Export Sorting.Sort. *)

Inductive color : Set :=
    | Red : color
    | Black : color.

Definition RBTree (A : Type) : Type := EBTree color A.

Definition empty {A : Type} : RBTree A := E.

Definition singleton {A : Type} (x : A) : RBTree A := N Red E x E.

Function balance
  {A : Type} (c : color)
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

Function ins {A : Type} (leb : A -> A -> bool) (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => N Red E x E
    | N c l v r =>
        if leb x v
        then balance c (ins leb x l) v r
        else balance c l v (ins leb x r)
end.

Definition insert {A : Type} (leb : A -> A -> bool) (x : A) (t : RBTree A) : RBTree A :=
  makeBlack (ins leb x t).

Fixpoint fromList {A : Type} (leb : A -> A -> bool) (l : list A) : RBTree A :=
match l with
    | [] => E
    | h :: t => insert leb h (fromList leb t)
end.

(** Properties of [isEmpty]. *)

Lemma isEmpty_balance :
  forall {A : Type} (c : color) (v : A) (l r : RBTree A),
    isEmpty (balance c l v r) = false.
Proof.
  intros.
  functional induction balance c l v r;
  cbn; reflexivity.
Qed.

Lemma isEmpty_makeBlack :
  forall {A : Type} (t : RBTree A),
    isEmpty (makeBlack t) = isEmpty t.
Proof.
  destruct t; cbn; reflexivity.
Qed.

Lemma isEmpty_ins :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (t : RBTree A),
    isEmpty (ins leb x t) = false.
Proof.
  intros.
  functional induction ins leb x t;
  cbn; rewrite ?isEmpty_balance; reflexivity.
Qed.

Lemma isEmpty_insert :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (t : RBTree A),
    isEmpty (insert leb x t) = false.
Proof.
  intros. unfold insert. rewrite isEmpty_makeBlack, isEmpty_ins. reflexivity.
Qed.

(** Properties of [singleton]. *)

Lemma Elem_singleton :
  forall {A : Type} {x y : A},
    Elem x (singleton y) <-> x = y.
Proof.
  unfold singleton. split.
    inv 1; inv H1.
    intros ->. auto.
Qed.

Lemma isBST_singleton :
  forall {A : Ord} (x : A),
    isBST (singleton x).
Proof.
  unfold singleton. intros. constructor; auto; inv 1.
Qed.

Lemma isBST2_singleton :
  forall {A : Ord} (x : A),
    isBST2 (singleton x).
Proof.
  constructor; auto.
Qed.

(** Properties of [balance]. *)

Lemma Elem_balance :
  forall {A : Type} (c : color) (x v : A) (l r : RBTree A),
    Elem x (balance c l v r) <-> Elem x l \/ x = v \/ Elem x r.
Proof.
  split;
  functional induction balance c l v r;
  auto; intros H.
    all: Elem'.
    all: decompose [or] H; clear H; subst; Elem'.
Qed.

Lemma isBST_balance :
  forall (A : Ord) (c : color) (v : A) (l r : RBTree A),
    isBST (N c l v r) -> isBST (balance c l v r).
Proof.
  intros.
  functional induction balance c l v r;
  isBST'; Elem'; trich.
Qed.

Lemma All_balance :
  forall {A : Type} (P : A -> Prop) (c : color) (v : A) (l r : RBTree A),
    All P (balance c l v r) <-> All P l /\ P v /\ All P r.
Proof.
  intros.
  functional induction balance c l v r;
  firstorder All'.
Qed.

Lemma isBST2_balance :
  forall (A : Ord) (c : color) (v : A) (l r : RBTree A),
    isBST2 (N c l v r) -> isBST2 (balance c l v r).
Proof.
  intros.
  functional induction balance c l v r;
  isBST2';
  do 2 match goal with
      | y : match _ with | _ => _ end |- _ => clear y
      | H : All _ ?t |- All _ ?t => induction H; constructor; isBST2; trich
  end.
Qed.

(** Properties of [makeBlack]. *)

Lemma Elem_makeBlack :
  forall {A : Type} (x : A) (t : RBTree A),
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

Lemma isBST2_makeBlack :
  forall (A : Ord) (t : RBTree A),
    isBST2 t -> isBST2 (makeBlack t).
Proof.
  destruct t; cbn; inv 1.
Qed.

(** Properties of [ins]. *)

Lemma Elem_ins :
  forall {A : Type} (leb : A -> A -> bool) (x y : A) (t : RBTree A),
    Elem x (ins leb y t) <-> x = y \/ Elem x t.
Proof.
  intros until t. revert x.
  functional induction ins leb y t;
  intros; rewrite ?Elem_balance, ?Elem_N, ?IHl, ?IHr;
  firstorder.
Qed.

Lemma isBST_ins :
  forall (A : Ord) (x : A) (t : RBTree A),
    isBST t -> isBST (ins trich_leb x t).
Proof.
  intros. functional induction ins trich_leb x t.
    constructor; auto; inv 1.
    apply isBST_balance. isBST'. apply Elem_ins in H. inv H. trich.
    apply isBST_balance. isBST'. apply Elem_ins in H. inv H. trich.
Qed.

Lemma All_ins :
  forall {A : Type} (leb : A -> A -> bool) (P : A -> Prop) (x : A) (t : RBTree A),
    All P (ins leb x t) <-> P x /\ All P t.
Proof.
  intros.
  functional induction ins leb x t;
  rewrite ?All_balance, ?IHr;
  firstorder All'.
Qed.

Lemma isBST2_ins :
  forall (A : Ord) (x : A) (t : RBTree A),
    isBST2 t -> isBST2 (ins trich_leb x t).
Proof.
  intros. functional induction ins trich_leb x t; isBST.
    auto.
    apply isBST2_balance. isBST2'. apply All_ins. split; trich.
    apply isBST2_balance. isBST2'. apply All_ins. split; trich.
Qed.

(** Properties of [insert]. *)

Lemma Elem_insert :
  forall {A : Type} (leb : A -> A -> bool) (x y : A) (t : RBTree A),
    Elem x (insert leb y t) <-> x = y \/ Elem x t.
Proof.
  unfold insert. intros. rewrite Elem_makeBlack, Elem_ins. reflexivity.
Qed.

Lemma isBST_insert :
  forall {A : Ord} (x : A) (t : RBTree A),
    isBST t -> isBST (insert trich_leb x t).
Proof.
  intros. unfold insert. apply isBST_makeBlack, isBST_ins. assumption.
Qed.

Lemma isBST2_insert :
  forall (A : Ord) (x : A) (t : RBTree A),
    isBST2 t -> isBST2 (insert trich_leb x t).
Proof.
  intros. unfold insert. apply isBST2_makeBlack, isBST2_ins. assumption.
Qed.

(** Properties of [inorder]. *)

Lemma Elem_inorder :
  forall (A : Type) (x : A) (t : RBTree A),
    In x (inorder t) <-> Elem x t.
Proof.
  split.
    induction t; cbn; intros; try apply in_app_or in H; firstorder.
      subst. firstorder.
    induction 1; cbn; apply in_or_app; firstorder.
Qed.

(** Properties of [fromList]. *)

Lemma Elem_fromList :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (l : list A),
    Elem x (fromList leb l) <-> In x l.
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
    isBST (fromList trich_leb l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insert. assumption.
Qed.

Lemma isBST2_fromList :
  forall (A : Ord) (l : list A),
    isBST2 (fromList trich_leb l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST2_insert. assumption.
Qed.

(** TODO: implement [join] and [split] *)