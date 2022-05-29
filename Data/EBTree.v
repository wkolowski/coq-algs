Require Export CoqAlgs.Base.
Require Import Ord.

Inductive EBTree (M A : Type) : Type :=
    | E : EBTree M A
    | N : M -> EBTree M A -> A -> EBTree M A -> EBTree M A.

Arguments E {M A}.
Arguments N {M A} _ _ _ _.

(** * Function definitions *)

Definition isEmpty {M A : Type} (t : EBTree M A) : bool :=
match t with
    | E => true
    | _ => false
end.

Fixpoint height {M A : Type} (t : EBTree M A) : nat :=
match t with
    | E => 0
    | N _ l _ r => 1 + max (height l) (height r)
end.

Fixpoint countEBT {M A : Type} (p : A -> bool) (t : EBTree M A) : nat :=
match t with
    | E => 0
    | N _ l v r =>
        (if p v then 1 else 0) + countEBT p l + countEBT p r
end.

Fixpoint inorder {M A : Type} (t : EBTree M A) : list A :=
match t with
    | E => []
    | N _ l v r => inorder l ++ v :: inorder r
end.

Fixpoint inorder'_aux {M A : Type} (t : EBTree M A) (acc : list A) : list A :=
match t with
    | E => acc
    | N _ l v r => inorder'_aux l (v :: inorder'_aux r acc)
end.

Definition inorder' {M A : Type} (t : EBTree M A) : list A := inorder'_aux t [].

Fixpoint preorder {M A : Type} (t : EBTree M A) : list A :=
match t with
    | E => []
    | N _ l v r => v :: (preorder l ++ preorder r)
end.

Fixpoint postorder {M A : Type} (t : EBTree M A) : list A :=
match t with
    | E => []
    | N _ l v r => postorder l ++ postorder r ++ [v]
end.

Fixpoint preorder' {M A : Type} (t : EBTree M A) (acc : list A) : list A :=
match t with
    | E         => acc
    | N _ l v r => v :: preorder' l (preorder' r acc)
end.

Fixpoint postorder' {M A : Type} (t : EBTree M A) (acc : list A) : list A :=
match t with
    | E         => acc
    | N _ l v r => postorder' l (postorder' r (v :: acc))
end.

Lemma preorder'_preorder :
  forall {M A : Type} (t : EBTree M A) (acc : list A),
    preorder' t acc = preorder t ++ acc.
Proof.
  induction t; cbn; intro.
    reflexivity.
    rewrite IHt1, IHt2, <- !app_assoc. cbn. reflexivity.
Qed.

Lemma postorder'_postorder :
  forall {M A : Type} (t : EBTree M A) (acc : list A),
    postorder' t acc = postorder t ++ acc.
Proof.
  induction t; cbn; intro.
    reflexivity.
    rewrite IHt1, IHt2, <- !app_assoc. cbn. reflexivity.
Qed.

(** * Predicates and relations *)

(** ** Elem *)

Inductive Elem {M A : Type} (x : A) : EBTree M A -> Prop :=
    | Elem_root :
        forall (m : M) (l r : EBTree M A),
        Elem x (N m l x r)
    | Elem_left :
        forall (m : M) (v : A) (l r : EBTree M A),
        Elem x l -> Elem x (N m l v r)
    | Elem_right :
        forall (m : M) (v : A) (l r : EBTree M A),
        Elem x r -> Elem x (N m l v r).

#[global] Hint Constructors EBTree Elem : core.

Lemma Elem_N :
  forall {M A : Type} (m : M) (x v : A) (l r : EBTree M A),
    Elem x (N m l v r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  split; inv 1. inv H0.
Qed.

Lemma Elem_inv :
  forall (M A : Type) (P : A -> Prop) (m : M) (v : A) (l r : EBTree M A),
    (forall x : A, Elem x (N m l v r) -> P x) ->
      P v /\
      (forall x : A, Elem x l -> P x) /\
      (forall x : A, Elem x r -> P x).
Proof.
  repeat split; intros; apply H; auto.
Qed.

Ltac Elem :=
repeat match goal with
    | |- Elem ?x (N _ _ ?x _) => constructor
    | H : Elem _ E |- _ => inv H
    | H : Elem _ (N _ E _ E) |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : forall _, Elem _ (N _ _ _ _) -> _ |- _ =>
            apply Elem_inv in H; decompose [and] H; clear H
end; auto.

Ltac Elem' :=
repeat match goal with
    | |- Elem ?x (N _ _ ?x _) => constructor
    | H : Elem _ E             |- _ => inv H
    | H : Elem _ (N _ _ _ _)   |- _ => inv H
    | H : Elem _ _ /\ Elem _ _ |- _ => destruct H
    | H : Elem _ _ \/ Elem _ _ |- _ => destruct H
    | H : forall _, Elem _ (N _ _ _ _) -> _ |- _ =>
            apply Elem_inv in H; decompose [and] H; clear H
    | H1 : forall _, Elem _ _ -> _, H2 : Elem _ _ |- _ =>
        specialize (H1 _ H2)
end; auto.

(** ** Ex *)

Inductive Ex {M A : Type} (P : A -> Prop) : EBTree M A -> Type :=
    | Ex_here :
        forall (m : M) (v : A) (l r : EBTree M A),
          P v -> Ex P (N m l v r)
    | Ex_left :
        forall (m : M) (v : A) (l r : EBTree M A),
          Ex P l -> Ex P (N m l v r)
    | Ex_right :
        forall (m : M) (v : A) (l r : EBTree M A),
          Ex P r -> Ex P (N m l v r).

(** ** All *)

Inductive All {M A : Type} (P : A -> Prop) : EBTree M A -> Prop :=
    | All_E : All P E
    | All_N :
        forall (m : M) (l : EBTree M A) (v : A) (r : EBTree M A),
          All P l -> P v -> All P r -> All P (N m l v r).

#[global] Hint Constructors All : core.

Ltac All :=
repeat match goal with
    | H : All _ E           |- _       => clear H
    | H : All _ (N _ _ _ _) |- _       => inv H
    |                       |- All _ E => constructor
end.

Ltac All' :=
repeat match goal with
    | H : All _ E           |- _       => clear H
    | H : All _ (N _ _ _ _) |- _       => inv H
    |                       |- All _ _ => constructor; auto
end.

(** ** isBST *)

Inductive isBST {M : Type} {A : Ord} : EBTree M A -> Prop :=
    | isBST_E : isBST E
    | isBST_N :
        forall (m : M) (v : A) (l r : EBTree M A),
          (forall x : A, Elem x l -> x ≤ v) -> isBST l ->
          (forall x : A, Elem x r -> x >= v) -> isBST r ->
            isBST (N m l v r).

#[global] Hint Constructors isBST : core.

Ltac isBST :=
repeat match goal with
    | H : isBST E           |- _       => clear H
    | H : isBST (N _ _ _ _) |- _       => inv H
    |                       |- isBST E => constructor
    |                       |- isBST _ _ -> _ => intro
end.

Ltac isBST' :=
repeat match goal with
    | H : isBST E           |- _       => clear H
    | H : isBST (N _ _ _ _) |- _       => inv H
    |                       |- isBST _ => constructor; intros; auto
    |                       |- isBST _ _ -> _ => intro
end.

(** ** isBST2 *)

Inductive isBST2 {M : Type} {A : Ord} : EBTree M A -> Prop :=
    | isBST2_E : isBST2 E
    | isBST2_N : forall (m : M) (v : A) (l r : EBTree M A),
        All (fun x : A => x ≤ v) l -> All (fun x : A => x >= v) r ->
          isBST2 l -> isBST2 r -> isBST2 (N m l v r).

#[global] Hint Constructors isBST2 : core.

Ltac isBST2 :=
repeat match goal with
    | H : isBST2 E           |- _             => clear H
    | H : isBST2 (N _ _ _ _) |- _             => inv H
    |                        |- isBST2 E      => constructor
    |                        |- isBST2 _ -> _ => intro
    | H : All _ E            |- _             => clear H
    | H : All _ (N _ _ _ _)  |- _             => inv H
end.

Ltac isBST2' :=
repeat match goal with
    | H : isBST2 E           |- _             => clear H
    | H : isBST2 (N _ _ _ _) |- _             => inv H
    |                        |- isBST2 _      => constructor; intros; auto
    |                        |- isBST2 _ -> _ => intro
    | H : All _ E            |- _             => clear H
    | H : All _ (N _ _ _ _)  |- _             => inv H
    |                        |- All _ _       => constructor; auto
end.

Lemma All_Elem :
  forall {M : Type} {A : Type} {P : A -> Prop} {t : EBTree M A},
    All P t -> forall x : A, Elem x t -> P x.
Proof.
  induction 1; inv 1.
Qed.

(** * Theorems *)

Lemma inorder'_aux_spec :
  forall (M A : Type) (t : EBTree M A) (acc : list A),
    inorder'_aux t acc = inorder t ++ acc.
Proof.
  induction t; cbn; intros.
    trivial.
    rewrite IHt1, IHt2, <- app_assoc, <- app_comm_cons. trivial.
Qed.

Lemma inorder'_spec :
  forall {M A : Type} (t : EBTree M A),
    inorder' t = inorder t.
Proof.
  intros. unfold inorder'.
  rewrite inorder'_aux_spec, app_nil_r.
  reflexivity.
Qed.