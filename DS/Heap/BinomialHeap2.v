Require Export Ord.
Require Export RCCBase.

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

Inductive elem {A : Type} (x : A)
  : forall {r : nat}, BinomialTree A r -> Prop :=
    | elemC :
        forall (y : A) (r : nat) (f : BinomialForest A r),
          x = y \/ elemForest x f -> elem x (node y f)

with elemForest {A : Type} (x : A)
  : forall {r : nat}, BinomialForest A r -> Prop :=
    | elemForestC :
        forall (r : nat) (t : BinomialTree A r) (f : BinomialForest A r),
          elem x t \/ elemForest x f -> elemForest x (bfcons t f).

Hint Constructors elem elemForest : core.

Fixpoint elem_dec
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) :
    {elem x t} + {~ elem x t}

with elemForest_dec
  {A : Ord} (x : A) {r : nat} (f : BinomialForest A r) :
    {elemForest x f} + {~ elemForest x f}.
Proof.
  destruct t as [y r f].
    case_eq (x =? y); intros.
      left. trich.
      destruct (elemForest_dec A x _ f).
        left. auto.
        right. inv 1.
          trich.
          apply inj_pair2 in H4. inv H3.
  destruct f as [| r t f'].
    right. inv 1.
    destruct (elem_dec A x _ t).
      left. constructor. auto.
      destruct (elemForest_dec A x _ f').
        left. auto.
        right. inv 1; apply inj_pair2 in H1; apply inj_pair2 in H3;
          subst; inv H2.
Defined.

Fixpoint elem_decb
  {A : Ord} (x : A) {r : nat} (t : BinomialTree A r) : bool :=
match t with
    | node x' ts =>
        (x =? x') || elemForest_decb x ts
end
with elemForest_decb
  {A : Ord} (x : A) {r : nat} (ts : BinomialForest A r) : bool :=
match ts with
    | bfnil => false
    | bfcons h ts' => elem_decb x h || elemForest_decb x ts'
end.

Lemma elem_decb_spec :
  forall (A : Ord) (x : A) (r : nat) (t : BinomialTree A r),
    BoolSpec (elem x t) (~ elem x t) (elem_decb x t)

with elemForest_decb_spec :
  forall (A : Ord) (x : A) (r : nat) (ts : BinomialForest A r),
    BoolSpec (elemForest x ts) (~ elemForest x ts) (elemForest_decb x ts).
Proof.
  destruct t as [x' r ts]; cbn. unfold orb. trich.
    destruct (elemForest_decb_spec A x r ts); auto.
      constructor. inv 1. inj. destruct H4; contradiction.
  destruct ts as [| r t ts']; simpl.
    constructor. inv 1.
    destruct (elem_decb_spec A x r t); auto.
      destruct (elemForest_decb_spec A x r ts'); auto.
        constructor. inv 1. inj. firstorder.
Qed.

Definition BinomialHeap (A : Type) : Type :=
  list {r : nat & BinomialTree A r}.

Definition BinomialHeap' (A : Type) : Type :=
  {r : nat & BinomialForest A r}.

Definition link {A : Ord} {r : nat} (t1 t2 : BinomialTree A r)
  : BinomialTree A (S r).
Proof.
  destruct t1 as [x r ts], t2 as [x' r ts'].
    destruct (x ≤? x').
      exact (node x (bfcons (node x' ts') ts)).
      exact (node x' (bfcons (node x ts) ts')).
Defined.