Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Export RCCBase.

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | T : A -> list (Tree A) -> Tree A.

Arguments E [A].
Arguments T [A] _ _.

Fixpoint Tree_rect'
  (A : Type) (P : Tree A -> Type) (Q : list (Tree A) -> Type)
  (HE : P E)
  (Hnil : Q [])
  (Hcons : forall (h : Tree A) (t : list (Tree A)), P h -> Q t -> Q (h :: t))
  (Htrans : forall (x : A) (l : list (Tree A)), Q l -> P (T x l))
  (t : Tree A) : P t.
Proof.
  destruct t.
    assumption.
    apply Htrans. induction l as [| h t].
      assumption.
      apply Hcons.
        eapply Tree_rect'; eauto.
        assumption.
Defined.

Theorem Tree_ind_proper
  (A : Type) (P : Tree A -> Prop)
  (HE : P E)
  (HT : forall (x : A) (l : list (Tree A)), Forall P l -> P (T x l))
  (t : Tree A) : P t.
Proof.
  induction t using Tree_rect' with (Q := Forall P); auto.
Qed.

Theorem Tree_ind_proper'
  (A : Type) (P : Tree A -> Prop)
  (HE : P E)
  (Hnil : forall x : A, P (T x []))
  (HT : forall (x : A) (t : Tree A) (l : list (Tree A)),
    P t -> Forall P l -> P (T x (t :: l)))
  (t : Tree A) : P t.
Proof.
  induction t using Tree_ind_proper; auto.
  destruct l.
    apply Hnil.
    apply HT; inv H.
Qed.

Lemma Tree_ind_proper2
  (A : Type) (P : Tree A -> Prop)
  (HE : P E)
  (Hnil : forall x : A, P (T x []))
  (HT : forall (x : A) (t : Tree A) (ts : list (Tree A)),
    P t -> P (T x ts) -> P (T x (t :: ts)))
  (t : Tree A) : P t.
Proof.
  induction t using Tree_ind_proper.
    apply HE.
    induction H.
      apply Hnil.
      apply HT; assumption.
Qed.

Inductive elem {A : Type} (x : A) : Tree A -> Prop :=
    | elem0 : forall l : list (Tree A), elem x (T x l)
    | elem1 : forall (a : A) (l : list (Tree A)),
        Exists (fun t => elem x t) l -> elem x (T a l).

Inductive elem' {A : Type} (x : A) : Tree A -> Prop :=
    | elem0' : forall l : list (Tree A), elem' x (T x l)
    | elem1' :
        forall (a : A) (t : Tree A) (ts : list (Tree A)),
          elem' x t -> elem' x (T a (t :: ts))
    | elem2' :
        forall (a : A) (t : Tree A) (ts : list (Tree A)),
          elem' x (T a ts) -> elem' x (T a (t :: ts)). 

Inductive isHeap {A : LinDec} : Tree A -> Prop :=
    | isHeap_E : isHeap E
    | isHeap_T :
        forall (v : A) (l : list (Tree A)),
          Forall (fun t : Tree A => forall x : A, elem x t -> v ≤ x) l ->
          Forall (fun t : Tree A => isHeap t) l ->
            isHeap (T v l).

Hint Constructors elem isHeap.

Require Import HSLib.Control.Functor.

Fixpoint fmap_Tree
  {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
match t with
    | E => E
    | T x l => T (f x) (map (fmap_Tree f) l)
end.

Ltac Tree_ind :=
repeat match goal with
    | |- forall t' : Tree _, _ =>
        let x := fresh "x" in
        let t := fresh "t" in
        let ts := fresh "ts" in
        let IHt := fresh "IHt" in
        let IHts := fresh "IHts" in
          induction t' as [| x | x t ts IHt IHts] using Tree_ind_proper2;
          cbn in *; try reflexivity; f_equal; rewrite ?IHt; auto;
          try (inv IHts; fail)
    | |- forall _, _ => intro
end.

Instance Functor_Tree : Functor Tree :=
{
    fmap := @fmap_Tree
}.
Proof.
  all: intros; ext t.
    destruct t as [| x t] using Tree_ind_proper; cbn.
      reflexivity.
      induction H; cbn.
        reflexivity.
        rewrite !id_eq in *. f_equal. inv IHForall.
    destruct t as [| x t] using Tree_ind_proper; cbn.
      reflexivity.
      induction H; cbn.
        reflexivity.
        f_equal. inv IHForall. rewrite H2. f_equal. assumption.
Restart.
  all: intros; ext t.
    induction t as [| x | x t ts] using Tree_ind_proper2;
    cbn in *; rewrite !id_eq in *; try reflexivity.
      rewrite IHt. inv IHt0.
    induction t as [| x | x t ts] using Tree_ind_proper2;
    cbn in *; try reflexivity.
      rewrite IHt. inv IHt0.
Restart.
  all: intros; ext t; gen t; Tree_ind.
    rewrite !id_eq. inv IHts.
Defined.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | T _ ts => 1 + fold_right (fun h t => size h + t) 0 ts
end.

Lemma fmap_size :
  forall (A B : Type) (f : A -> B) (t : Tree A),
    size (fmap_Tree f t) = size t.
Proof.
  Tree_ind.
Qed.

Hint Constructors elem'.

Hint Extern 0 =>
match goal with
    | H : elem' _ E |- _ => inv H
end.

Lemma fmap_elem' :
  forall (A B : Type) (f : A -> B) (t : Tree A) (x : A),
    elem' x t -> elem' (f x) (fmap_Tree f t).
Proof.
  induction 1; cbn; auto.
Qed.

(*Lemma fmap_elem :
  forall (A B : Type) (f : A -> B) (t : Tree A) (x : A),
    elem x t -> elem (f x) (fmap_Tree f t).
Proof.
  induction 1; cbn; auto.
    induction H. cbn.
Qed.*)

Require Import HSLib.Control.Foldable.

Print Foldable.

Fixpoint foldMap_Tree
  {A : Type} {M : Monoid} (f : A -> M) (t : Tree A) : M :=
match t with
    | E => neutr
    | T x l => op (f x)
                  (fold_right (fun h t => op (foldMap_Tree f h) t) neutr l)
        (*let aux := fix aux (l : list (Tree A)) : M :=
        match l with
            | [] => neutr
            | t :: ts => op (foldMap_Tree f t) (aux ts)
        end
        in op (f x) (aux l)*)
end.

Instance Foldable_Tree : Foldable Tree :=
{
    foldMap := @foldMap_Tree;
}.
Proof.
  intros. ext t. gen t.
  apply (@Tree_rect' _ _ (fun l =>
      fold_right (fun t ts => op (foldMap_Tree (f .> g) t) ts) neutr l =
      fold_right (fun t ts => op (g (foldMap_Tree f t)) ts) neutr l)).
    unfold compose; cbn. rewrite H. reflexivity.
    cbn. reflexivity.
    intros. cbn. rewrite H1, H2. reflexivity.
    intros. unfold compose in *. cbn in *. rewrite ?H1, H0.
      f_equal. clear H1. induction l as [| h t]; cbn.
        rewrite H. reflexivity.
        rewrite H0.
        rewrite IHt. reflexivity.
Defined.