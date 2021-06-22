Require Export CoqAlgs.Base.
Require Export Ord.
Require Export Data.EBTree.

Definition Tree (A : Type) : Type := EBTree nat A.

Definition height' {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | N h _ _ _ => h
end.

Definition prebalance {A : Type} (l : Tree A) (v : A) (r : Tree A) : Tree A :=
  N (1 + max (height l) (height r)) l v r.

Function rotateLR {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ (N _ a y b) x c => prebalance a y (prebalance b x c)
    | _ => t
end.

Function rotateRL {A : Type} (t : Tree A) : Tree A :=
match t with
    | N _ a x (N _ b y c) => prebalance (prebalance a x b) y c
    | _ => t
end.

Function balance {A : Type} (l : Tree A) (v : A) (r : Tree A) : Tree A :=
match height l <?> height r with
    | Lt =>
        match r with
            | N _ a x b => prebalance (prebalance l v a) x b
            | _ => prebalance l v r
        end
    | Eq => prebalance l v r
    | Gt =>
        match l with
            | N _ a x b => prebalance a x (prebalance b v r)
            | _ => prebalance l v r
        end
end.

Function insert {A : Type} (leb : A -> A -> bool) (x : A) (t : Tree A) : Tree A :=
match t with
    | E => N 1 E x E
    | N _ l v r =>
        if leb x v
        then balance (insert leb x l) v r
        else balance l v (insert leb x r)
end.

Fixpoint fromList {A : Type} (leb : A -> A -> bool) (l : list A) : Tree A :=
match l with
    | [] => E
    | h :: t => insert leb h (fromList leb t)
end.

Lemma height_prebalance :
  forall (A : Type) (v : A) (l r : Tree A),
    height (prebalance l v r) = 1 + max (height l) (height r).
Proof.
  cbn. reflexivity.
Qed.

(* TODO: height_rotate *)

Lemma height_balance :
  forall (A : Type) (v : A) (l r : Tree A),
    height (balance l v r) <= 1 + max (height l) (height r).
Proof.
  intros. functional induction balance l v r; trich; cbn in *.
    destruct (height b).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
    destruct (height r).
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
      rewrite (@cmp_spec1 natlt) in e. cbn in e. lia.
Qed.

Lemma height_insert :
  forall {A : Type} (leb : A -> A -> bool) (x : A) (t : Tree A),
    height (insert leb x t) <= 1 + height t.
Proof.
  intros.
  functional induction insert leb x t;
  cbn; rewrite ?height_balance; lia.
Qed.

(** Properties of [balance]. *)

(* Lemma Elem_balance :
  forall {A : Type} (c : color) (x v : A) (l r : RBTree A),
    Elem x (N c l v r) <-> Elem x (balance c l v r).
Proof.
  split;
  functional induction balance c l v r;
  auto; intros; Elem'.
Qed.
 *)

Lemma All_balance :
  forall {A : Type} (P : A -> Prop) (v : A) (l r : Tree A),
    All P (balance l v r) <-> All P l /\ P v /\ All P r.
Proof.
  intros.
  functional induction balance l v r;
  unfold prebalance;
  firstorder All'.
Qed.

Lemma isBST2_balance :
  forall (A : Ord) (h : nat) (v : A) (l r : Tree A),
    isBST2 (N h l v r) -> isBST2 (balance l v r).
Proof.
  intros.
  functional induction balance l v r;
  isBST2'; unfold prebalance; clear e.
    induction H4; isBST2'. trich.
    induction H5; isBST2'. trich.
Qed.

(** Properties of [insert]. *)

Lemma All_insert :
  forall {A : Type} (P : A -> Prop) (leb : A -> A -> bool) (x : A) (t : Tree A),
    All P (insert leb x t) <-> P x /\ All P t.
Proof.
  intros until t.
  functional induction insert leb x t;
  rewrite ?All_balance, ?IHt0;
  firstorder All'.
Qed.

Lemma isBST2_insert :
  forall {A : Ord} (x : A) (t : Tree A),
    isBST2 t -> isBST2 (insert trich_leb x t).
Proof.
  intros until t.
  functional induction insert trich_leb x t;
  isBST2'.
    apply isBST2_balance with 0. isBST2'. apply All_insert. split; trich.
    apply isBST2_balance with 0. isBST2'. apply All_insert. split; trich.
Qed.

(** Properties of [fromList]. *)

Lemma isBST2_fromList :
  forall (A : Ord) (l : list A),
    isBST2 (fromList trich_leb l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST2_insert. assumption.
Qed.