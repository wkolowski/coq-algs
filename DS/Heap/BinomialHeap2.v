From CoqAlgs Require Export Base.
From CoqAlgs Require Export Ord.

Inductive BinomialTree (A : Type) : nat -> Type :=
    | node : A -> forall {r : nat}, BinomialForest A r -> BinomialTree A r

with BinomialForest (A : Type) : nat -> Type :=
    | bfnil : BinomialForest A 0
    | bfcons : forall {r : nat},
        BinomialTree A r -> BinomialForest A r ->
          BinomialForest A (S r).

Arguments node {A} _ {r} _.
Arguments bfnil {A}.
Arguments bfcons {A r} _ _.

Inductive OK {A : Type} (R : A -> A -> Prop) (x : A) : forall {r : nat}, BinomialTree A r -> Prop :=
    | OK_node :
        forall (v : A) {r : nat} (f : BinomialForest A r),
          R x v -> OK R x (node v f).

Inductive OKF {A : Type} (R : A -> A -> Prop) (x : A) : forall {r : nat}, BinomialForest A r -> Prop :=
    | OKF_bfnil : OKF R x bfnil
    | OKF_bfcons :
        forall {r : nat} (t : BinomialTree A r) (f : BinomialForest A r),
          OK R x t -> OKF R x f -> OKF R x (bfcons t f).

Inductive isHeap {A : Type} (R : A -> A -> Prop) : forall {r : nat}, BinomialTree A r -> Prop :=
    | isHeap_node :
        forall (v : A) {r : nat} (f : BinomialForest A r),
          OKF R v f -> isHeap R (node v f)

with isHeapF {A : Type} (R : A -> A -> Prop) : forall {r : nat}, BinomialForest A r -> Prop :=
    | isHeapF_bfnil : isHeapF R bfnil
    | isHeapF_bfcons :
        forall {r : nat} (t : BinomialTree A r) (f : BinomialForest A r),
          isHeap R t -> isHeapF R f -> isHeapF R (bfcons t f).

Definition link {A : Ord} {r : nat} (t1 t2 : BinomialTree A r)
  : BinomialTree A (S r).
Proof.
  destruct t1 as [x1 r1 ts1], t2 as [x2 r2 ts2].
    destruct (x1 ≤? x2).
      exact (node x1 (bfcons (node x2 ts2) ts1)).
      exact (node x2 (bfcons (node x1 ts1) ts2)).
Defined.

Lemma isHeap_link :
  forall {A : Ord} {r : nat} {t1 t2 : BinomialTree A r},
    isHeap cmp t1 -> isHeap cmp t2 ->
      isHeap cmp (link t1 t2).
Proof.
  destruct t1 as [x1 r1 ts1], t2 as [x2 r2 ts2].
  inv 1. inv 1. cbn.
  trich; repeat constructor.
    unfold comparison2bool in *. trich.
    inv H3.
    unfold comparison2bool in *. trich.
    inv H5.
Qed.

(** Elem *)

Inductive Elem {A : Type} (x : A)
  : forall {r : nat}, BinomialTree A r -> Prop :=
    | ElemC :
        forall (y : A) (r : nat) (f : BinomialForest A r),
          x = y \/ ElemForest x f -> Elem x (node y f)

with ElemForest {A : Type} (x : A)
  : forall {r : nat}, BinomialForest A r -> Prop :=
    | ElemForestC :
        forall (r : nat) (t : BinomialTree A r) (f : BinomialForest A r),
          Elem x t \/ ElemForest x f -> ElemForest x (bfcons t f).

#[global] Hint Constructors Elem ElemForest : core.

Fixpoint Elem_dec
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) :
    {Elem x t} + {~ Elem x t}

with ElemForest_dec
  {A : Ord} (x : A) {r : nat} (f : BinomialForest A r) :
    {ElemForest x f} + {~ ElemForest x f}.
Proof.
  destruct t as [y r f].
    case_eq (x =? y); intros.
      left. trich.
      destruct (ElemForest_dec A x _ f).
        left. auto.
        right. inv 1.
          trich.
          apply inj_pair2 in H4. inv H3.
  destruct f as [| r t f'].
    right. inv 1.
    destruct (Elem_dec A x _ t).
      left. constructor. auto.
      destruct (ElemForest_dec A x _ f').
        left. auto.
        right. inv 1; apply inj_pair2 in H1; apply inj_pair2 in H3;
          subst; inv H2.
Defined.

Fixpoint Elem_decb
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) : bool :=
match t with
    | node x' ts =>
        (x =? x') || ElemForest_decb x ts
end
with ElemForest_decb
  {A : Ord} (x : A) {r : nat} (ts : BinomialForest A r) : bool :=
match ts with
    | bfnil => false
    | bfcons h ts' => Elem_decb x h || ElemForest_decb x ts'
end.

Lemma Elem_decb_spec :
  forall (A : Ord) (x : A) (r : nat) (t : BinomialTree A r),
    BoolSpec (Elem x t) (~ Elem x t) (Elem_decb x t)

with ElemForest_decb_spec :
  forall (A : Ord) (x : A) (r : nat) (ts : BinomialForest A r),
    BoolSpec (ElemForest x ts) (~ ElemForest x ts) (ElemForest_decb x ts).
Proof.
  destruct t as [x' r ts]; cbn. unfold orb. trich.
    destruct (ElemForest_decb_spec A x r ts); auto.
      constructor. inv 1. inj. destruct H4; contradiction.
  destruct ts as [| r t ts']; simpl.
    constructor. inv 1.
    destruct (Elem_decb_spec A x r t); auto.
      destruct (ElemForest_decb_spec A x r ts'); auto.
        constructor. inv 1. inj. firstorder.
Qed.