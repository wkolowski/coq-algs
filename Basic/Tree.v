Require Export LinDec.

Require Export RCCBase.

(*
Require Import CoqMTL.Control.Functor.
Require Import CoqMTL.Control.Foldable.
Require Import CoqMTL.Misc.Monoid.
*)

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | T : A -> list (Tree A) -> Tree A.

Arguments E {A}.
Arguments T {A} _ _.

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

Inductive All {A : Type} (P : A -> Prop) : Tree A -> Prop :=
    | All_E : All P E
    | All_N :
        forall (x : A) (ts : list (Tree A)),
          P x -> Forall (All P) ts -> All P (T x ts).

Inductive Any {A : Type} (P : A -> Prop) : Tree A -> Prop :=
    | Any_root :
        forall (x : A) (ts : list (Tree A)),
          P x -> Any P (T x ts)
    | Any_children :
        forall (x : A) (ts : list (Tree A)),
          Exists (Any P) ts -> Any P (T x ts).

Hint Constructors elem elem' isHeap : core.

Hint Extern 0 =>
match goal with
    | |- ~ elem _ E => intro
    | |- ~ elem' _ E => intro
    | H : elem _ E |- _ => inv H
    | H : elem' _ E |- _ => inv H
    | H : Exists _ [] |- _ => inv H
end
  : core.

(** * Induction principles *)
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

Ltac Tree_ind :=
repeat match goal with
    | |- forall t' : Tree _, _ =>
        let x := fresh "x" in
        let t := fresh "t" in
        let ts := fresh "ts" in
        let IHt := fresh "IHt" in
        let IHts := fresh "IHts" in
          induction t' as [| x | x t ts IHt IHts] using Tree_ind_proper2;
          cbn in *; intros; try reflexivity; f_equal; rewrite ?IHt;
          (*rewrite ?id_eq;*) try (inv IHts; fail); auto; try congruence
    | |- forall _, _ => intro
end.

Fixpoint fmap_Tree
  {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
match t with
    | E => E
    | T x l => T (f x) (map (fmap_Tree f) l)
end.

(*
#[refine]
Instance Functor_Tree : Functor Tree :=
{
    fmap := @fmap_Tree
}.
Proof.
  all: intros; ext t; gen t; Tree_ind.
Defined.
*)

(*
Fixpoint foldMap_Tree
  {A : Type} {M : Monoid} (f : A -> M) (t : Tree A) : M :=
match t with
    | E => neutr
    | T x l => op (f x)
                  (fold_right (fun h t => op (foldMap_Tree f h) t) neutr l)
end.

#[refine]
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
*)

(** * Utility functions *)

(*Fixpoint foldr {A B : Type} (f : A -> B -> B) (b : B) (t : Tree A) : B :=
match t with
    | E => b
    | T x ts => f x (fold_right (fun t ts => foldr f ts t) b ts)
end.

Fixpoint foldr' {A B : Type} (f : A -> B -> B) (b : B) (t : Tree A) : B :=
match t with
    | E => b
    | T x ts =>
        let
          aux := fix aux (b : B) (ts : list (Tree A)) : B :=
          match ts with
              | [] => f x b
              | t :: ts' =>
                  let b' := foldr f b t in aux b' ts'
          end
        in aux b ts
end.

Lemma foldr_foldr' : @foldr = @foldr'.
Proof.
  ext A; ext  B; ext f; ext b; ext t; gen b; gen t. Tree_ind.
  rewrite IHt. rewrite <- IHts. f_equal.
  rewrite <- !IHt.
Abort.

Definition foldr2
  {A B : Type} (f : A -> list B -> B) (b : B) (t : Tree A) : B :=
match t with
    | E => b
    | T x ts => f x (map foldr2 *)

(* TODO Definition sizef {A : Type} (t : Tree A) : nat :=
  foldr (fun _ ts => 1 + ts) 0 t.

Lemma sizef_spec : @sizef = @size.
Proof.
  ext A; ext t; gen t. Tree_ind. inv IHts.
Abort.

Definition sizef' {A : Type} (t : Tree A) : nat :=
  foldr' (fun _ => S) 0 t.

Compute sizef (T 5 [T 0 []; T 1 []]).
Compute sizef' (T 5 [T 0 []; T 1 []]).

 (T 5 [T 0 []; T 1 []]).
Compute sizef' (T 5 [T 0 []; T 1 []]). *)

Definition isEmpty
  {A : Type} (t : Tree A) : bool :=
match t with
    | E => true
    | _ => false
end.

Fixpoint size {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | T _ ts => 1 + fold_right (fun h t => size h + t) 0 ts
end.

Fixpoint height {A : Type} (t : Tree A) : nat :=
match t with
    | E => 0
    | T _ ts => 1 + fold_right (fun h t => max (height h) t) 0 ts
end.

Fixpoint countTree {A : LinDec} (x : A) (t : Tree A) : nat :=
match t with
    | E => 0
    | T x' l =>
        (if x =? x' then S else id)
          (fold_right (fun h t => countTree x h + t) 0 l)
end.

(** Properties of [isEmpty]. *)

Lemma isEmpty_elem :
  forall (A : Type) (x : A) (t : Tree A),
    isEmpty t = true -> ~ elem x t.
Proof. Tree_ind. Qed.

Lemma isEmpty_isHeap :
  forall (A : LinDec) (t : Tree A),
    isEmpty t = true -> isHeap t.
Proof. Tree_ind. Qed.

Lemma isEmpty_size_false :
  forall (A : Type) (t : Tree A),
    isEmpty t = false -> size t <> 0.
Proof. Tree_ind. Qed.

Lemma isEmpty_size_true :
  forall (A : LinDec) (t : Tree A),
    isEmpty t = true -> size t = 0.
Proof. Tree_ind. Qed.

(** Properties of [size]. *)

Lemma size_fmap :
  forall (A B : Type) (f : A -> B) (t : Tree A),
    size (fmap_Tree f t) = size t.
Proof. Tree_ind. Qed.

Lemma fmap_elem' :
  forall (A B : Type) (f : A -> B) (t : Tree A) (x : A),
    elem' x t -> elem' (f x) (fmap_Tree f t).
Proof.
  induction 1; cbn; auto.
Qed.

(** Properties of [height]. *)

(*
Lemma height_fmap :
  forall (A B : Type) (f : A -> B) (t : Tree A),
    height (fmap f t) = height t.
Proof. Tree_ind. Qed.
*)

Lemma height_isEmpty_true :
  forall (A : Type) (t : Tree A),
    height t = 0 <-> isEmpty t = true.
Proof.
  Tree_ind; firstorder; congruence.
Qed.

Lemma height_isEmpty_false :
  forall (A : Type) (t : Tree A),
    height t <> 0 <-> isEmpty t = false.
Proof.
  Tree_ind; firstorder; congruence.
Qed.

Fixpoint mirror {A : Type} (t : Tree A) : Tree A :=
match t with
    | E => E
    | T x ts => T x (rev (map mirror ts))
end.

Lemma mirror_inv :
  forall (A : Type) (t : Tree A),
    mirror (mirror t) = t.
Proof.
  Tree_ind. rewrite ?map_app, ?rev_app_distr. cbn. inv IHts.
Qed.

Fixpoint count {A : Type} (p : A -> bool) (t : Tree A) : nat :=
match t with
    | E => 0
    | T x ts =>
        (if p x then S else id) (fold_left (fun t h => count p h + t) ts 0)
end.

Lemma fold_left_snoc :
  forall (A B : Type) (f : A -> B -> A) (a : A) (l : list B) (b : B),
    fold_left f (l ++ [b]) a = f (fold_left f l a) b.
Proof.
  intros A B f a l. gen a.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    rewrite IHt. reflexivity.
Qed.

Lemma fold_left_init :
forall (A B : Type) (f : A -> B -> A) (a : A) (l : list B) (b : B),
  fold_left f l (f a b) = fold_left f (b :: l) a.
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    reflexivity.
Qed.

Lemma count_mirror :
  forall (A : Type) (p : A -> bool) (t : Tree A),
    count p (mirror t) = count p t.
Proof.
  Tree_ind. destruct (p x) eqn: Hpx.
    inv IHts. rewrite fold_left_snoc, IHt, H0.
      change (count p t0 + 0) with ((fun t h => count p h + t) 0 t0).
      rewrite fold_left_init.
Abort.