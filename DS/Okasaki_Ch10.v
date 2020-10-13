(** * 10 Data-Structural Bootstrapping *)

Require Import List.
Import ListNotations.

Require Import FunInd.

(** ** 10.1 Structural Decomposition *)

(** *** 10.1.2 Binary Random-Access Lists Revisited *)

Inductive Seq (A : Type) : Type :=
    | Nil : Seq A
    | Zero : Seq (A * A) -> Seq A
    | One : A -> Seq (A * A) -> Seq A.

Arguments Nil  {A}.
Arguments Zero {A} _.
Arguments One  {A} _ _.

Definition empty {A : Type} : Seq A := Nil.

Definition isEmpty {A : Type} (s : Seq A) : bool :=
match s with
    | Nil => true
    | _ => false
end.

Fixpoint isEmpty' {A : Type} (s : Seq A) : bool :=
match s with
    | Nil => true
    | Zero s' => isEmpty' s'
    | One _ _ => false
end.

Function cons {A : Type} (x : A) (s : Seq A) : Seq A :=
match s with
    | Nil => One x Nil
    | Zero s' => One x s'
    | One h t => Zero (cons (x, h) t)
end.

Function uncons {A : Type} (s : Seq A) : option (A * Seq A) :=
match s with
    | Nil => None
    | Zero s' =>
        match uncons s' with
            | None => None
            | Some ((x, y), s'') => Some (x, One y s'')
        end
    | One h t => Some (h, Zero t)
end.

(*
Require Import CoqMTL.Base.
Require Import CoqMTL.Control.Functor.
Require Import CoqMTL.Control.Monad.All.
*)

Require Import RCCBase.

(*
Definition head {A : Type} (s : Seq A) : option A :=
  fmap fst (uncons s).

Definition tail {A : Type} (s : Seq A) : option (Seq A) :=
  fmap snd (uncons s).

Require Import Div2.

Fixpoint even (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
end.

(** [lookup] *)
Inductive lookupGraph :
  nat -> forall A : Type, Seq A -> option A -> Type :=
    | graph_Nil :
        forall i A, lookupGraph i A Nil None
    | graph_Zero :
        forall i A s r,
          lookupGraph (div2 i) (A * A) s r ->
          lookupGraph i A (Zero s)
            (fmap (fun '(x, y) => if even i then x else y) r)
    | graph_One_0 :
        forall A h t,
          lookupGraph 0 A (One h t) (Some h)
    | graph_One_S :
        forall i A h t r,
          lookupGraph i A (Zero t) r -> lookupGraph (S i) A (One h t) r.

Hint Constructors lookupGraph.

Definition lookup_strong
  (i : nat) {A : Type} (s : Seq A)
  : {r : option A & lookupGraph i A s r}.
Proof.
  gen i. induction s as [| A s' | A h t]; intros.
    exists None. auto.
    destruct (IHs' (div2 i)). eauto.
    destruct i as [| i'].
      exists (Some h). constructor.
      destruct (IHt (div2 i')) as [r g]. eauto.
Defined.

Definition lookup
  (i : nat) {A : Type} (s : Seq A) : option A :=
    projT1 (lookup_strong i s).

(** [update] *)
Definition enhance {A : Type} (i : nat) (f : A -> A) : A * A -> A * A :=
  fun '(x, y) => if even i then (f x, y) else (x, f y).

Inductive fupdateGraph
  : nat -> forall A : Type, (A -> A) -> Seq A -> Seq A -> Type :=
    | fupdateGraph_Nil :
        forall i A f, fupdateGraph i A f Nil Nil
    | fupdateGraph_Zero :
        forall i A f s r,
          fupdateGraph (div2 i) (A * A) (enhance i f) s r ->
          fupdateGraph i A f (Zero s) (Zero r)
    | fupdateGraph_One_0 :
        forall A f h t,
          fupdateGraph 0 A f (One h t) (One (f h) t)
    | fupdateGraph_One_S :
        forall i A f h t r,
          fupdateGraph i A f (Zero t) r ->
            fupdateGraph (S i) A f (One h t) (cons h r).

Hint Constructors fupdateGraph.

Definition fupdate_strong
  (i : nat) (A : Type) (f : A -> A) (s : Seq A)
  : {r : Seq A & fupdateGraph i A f s r}.
Proof.
  gen i. gen f. induction s as [| A s' | A h t]; intros.
    exists Nil. auto.
    destruct (IHs' (enhance i f) (div2 i)). eauto.
    destruct i as [| i'].
      exists (One (f h) t). constructor.
      destruct (IHt (enhance i' f) (div2 i')) as [r g]. eauto.
Defined.

Definition fupdate
  (i : nat) {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
    projT1 (fupdate_strong i A f s).

Definition update
  (i : nat) {A : Type} (y : A) (s : Seq A) : Seq A :=
    fupdate i (const y) s.

(** Other functions *)

Fixpoint fromList {A : Type} (l : list A) : Seq A :=
match l with
    | [] => Nil
    | h :: t => cons h (fromList t)
end.

Fixpoint zipjoin {A : Type} (l : list (A * A)) : list A :=
match l with
    | [] => []
    | (x, y) :: t => x :: y :: zipjoin t
end.

Fixpoint toList {A : Type} (s : Seq A) : list A :=
match s with
    | Nil => []
    | Zero s' => zipjoin (toList s')
    | One h t => h :: zipjoin (toList t)
end.

Fixpoint size {A : Type} (s : Seq A) : nat :=
match s with
    | Nil => 0
    | Zero s' => 2 * size s'
    | One h t => S (2 * size t)
end.

Fixpoint index {A : Type} (i : nat) (l : list A) {struct l} : option A :=
match l with
    | [] => None
    | h :: t =>
        match i with
            | 0 => Some h
            | S i' => index i' t
        end
end.

Fixpoint lupdate
  (i : nat) {A : Type} (f : A -> A) (l : list A) {struct l} : list A :=
match l with
    | [] => []
    | h :: t =>
        match i with
            | 0 => f h :: t
            | S i' => h :: lupdate i' f t
        end
end.

Fixpoint valid {A : Type} (s : Seq A) : Prop :=
match s with
    | Nil => True
    | Zero s' => s' <> Nil /\ valid s'
    | One _ t => valid t
end.

Fixpoint normalize {A : Type} (s : Seq A) : Seq A :=
match s with
    | Nil => Nil
    | Zero s' =>
        match normalize s' with
            | Nil => Nil
            | s'' => Zero s''
        end
    | One h t => One h (normalize t)
end.

(** Tests *)

Let to_1_10 := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Compute fromList to_1_10.
Compute update 5 42 (fromList to_1_10).
Compute lookup 1 (fromList to_1_10).
Compute lookup 5 (fromList to_1_10).
Compute update 1 42 (fromList to_1_10).

(** Properties of [isEmpty]. *)

Lemma isEmpty_empty :
  forall (A : Type) (s : Seq A),
    isEmpty s = true <-> s = empty.
Proof.
  split; destruct s; compute; congruence.
Qed.

Lemma isEmpty_cons :
  forall (A : Type) (h : A) (t : Seq A),
    isEmpty (cons h t) = false.
Proof.
  destruct t; cbn; reflexivity.
Qed.

Lemma empty_valid :
  forall A : Type,
    valid (@empty A).
Proof.
  cbn. trivial.
Qed.

(** Properties of [isEmpty']. *)

Lemma isEmpty'_empty :
  forall A : Type,
    isEmpty' (@empty A) = true.
Proof.
  reflexivity.
Qed.

Lemma isEmpty'_cons :
  forall (A : Type) (h : A) (t : Seq A),
    isEmpty' (cons h t) = false.
Proof.
  induction t; cbn; rewrite ?IHt; reflexivity.
Qed.

Lemma isEmpty'_size :
  forall (A : Type) (s : Seq A),
    isEmpty' s = true <-> size s = 0.
Proof.
  split.
    induction s as [| s' | h t]; cbn; intro.
      reflexivity.
      rewrite IHs; auto.
      congruence.
    induction s as [| s' | h t]; cbn; intro.
      reflexivity.
      apply IHs. destruct (size s); inv H.
      inv H.
Qed.

(** Properties of cons *)

Lemma cons_not_Nil :
  forall (A : Type) (x : A) (s : Seq A),
    cons x s <> Nil.
Proof.
  induction s as [| s' | h t]; inv 1.
Qed.

Lemma cons_uncons :
  forall (A : Type) (x : A) (s s' : Seq A),
    uncons s = Some (x, s') -> cons x s' = s.
Proof.
  intros. functional induction @uncons A s.
    congruence.
    congruence.
    inv H. cbn. rewrite IHo; auto.
    inv H.
Qed.

Lemma cons_toList :
  forall (A : Type) (x : A) (s : Seq A),
    toList (cons x s) = x :: toList s.
Proof.
  intros. functional induction @cons A x s; cbn.
    reflexivity.
    reflexivity.
    rewrite IHs0. cbn. reflexivity.
Qed.

Lemma cons_size :
  forall (A : Type) (x : A) (s : Seq A),
    size (cons x s) = S (size s).
Proof.
  induction s as [| s' | h t]; cbn.
    reflexivity.
    reflexivity.
    rewrite <- ?plus_n_O. rewrite IHs. cbn. rewrite <- plus_n_Sm.
      reflexivity.
Qed.

Lemma cons_valid :
  forall (A : Type) (x : A) (s : Seq A),
    valid s -> valid (cons x s).
Proof.
  induction s as [| s' | h t]; cbn; intros; firstorder.
    apply cons_not_Nil.
Qed.

(** Properties of uncons *)

Lemma uncons_cons :
  forall (A : Type) (x : A) (s : Seq A),
    fmap (fun '(x, s) => (x, normalize s)) (uncons (cons x s)) =
    Some (x, normalize s).
Proof.
  intros. remember (cons x s) as w. gen s; gen x.
  functional induction @uncons A w; intros.
    symmetry in Heqw. apply cons_not_Nil in Heqw. contradiction.
    functional inversion Heqw; inj; subst.
      specialize (IHo (x, h) t eq_refl). rewrite e0 in IHo.
        cbn in *. congruence.
    functional inversion Heqw; inj; subst.
      specialize (IHo (x0, h) t eq_refl). rewrite e0 in IHo.
        cbn in *. congruence.
    functional inversion Heqw; inj; subst; cbn; reflexivity.
Qed.

Lemma uncons_valid :
  forall (A : Type) (h : A) (t s : Seq A),
    valid s -> uncons s = None \/ (uncons s = Some (h, t) -> valid t).
Proof.
  intros A h t s. gen t; gen h.
  induction s as [| s' | h' t']; cbn; intros.
    left. reflexivity.
    destruct (uncons s).
      destruct p, p. right. inv 1. cbn. destruct H.
        destruct (IHs (h, s2) s0 H0).
          inv H1.
          apply H1. reflexivity.
      left. reflexivity.
    right. inv 1. cbn. split; auto. case_eq (uncons s); intros.
      destruct p. destruct (IHs p s0 H).
        congruence.
        destruct s; cbn in *; congruence.
Abort.

(** Properties of head *)

Lemma head_cons :
  forall (A : Type) (x : A) (s : Seq A),
    head (cons x s) = Some x.
Proof.
  intros. remember (cons x s) as w.
  gen s; gen x. unfold head.
  functional induction @uncons A w; cbn; intros.
    symmetry in Heqw. apply cons_not_Nil in Heqw. contradiction.
    functional inversion Heqw; inj; subst.
      specialize (IHo (x, h) t eq_refl). rewrite e0 in IHo. cbn in IHo.
        congruence.
    functional inversion Heqw; inj; subst.
      specialize (IHo (x0, h) t eq_refl). rewrite e0 in IHo. cbn in IHo.
        congruence.
    functional inversion Heqw; inj; subst; reflexivity.
Qed.

(** Properties of tail *)
Lemma tail_cons :
  forall (A : Type) (x : A) (s : Seq A),
    fmap normalize (tail (cons x s)) = Some (s).
Proof.
  intros. remember (cons x s) as w. gen s; gen x. unfold tail.
  functional induction @uncons A w; intros.
    symmetry in Heqw. apply cons_not_Nil in Heqw. contradiction.
    functional inversion Heqw; inj; subst; cbn.
Abort.

Lemma toList_tail :
  forall (A : Type) (s : Seq A),
    fmap toList (tail s) = match toList s with
                 | [] => None
                 | _ :: t => Some t
             end.
Proof.
  intros. unfold tail.
  functional induction @uncons A s; cbn.
    reflexivity.
    rewrite e0 in IHo. cbn in *. destruct (toList s') as [| h t]; cbn.
      reflexivity.
      congruence.
    apply cons_uncons in e0. rewrite <- e0, cons_toList. cbn. reflexivity.
    reflexivity.
Qed.

(** Properties of lookup and lookup *)

Lemma lookupGraph_unique :
  forall (i : nat) (A : Type) (s : Seq A) (r r' : option A),
    lookupGraph i A s r -> lookupGraph i A s r' -> r = r'.
Proof.
  induction 1; inv 1; try inj.
    cbn. f_equal. apply IHX. assumption.
    reflexivity.
    eauto.
Qed.

Lemma lookup_spec :
  forall (i : nat) (A : Type) (s : Seq A),
    lookupGraph i A s (@lookup i A s).
Proof.
  intros. unfold lookup. destruct (lookup_strong). cbn. assumption.
Qed.

Lemma lookup_eq :
  forall (i : nat) (A : Type) (s : Seq A),
    lookup i s =
    match s with
        | Nil => None
        | Zero s' => fmap (fun '(x, y) => if even i then x else y)
                          (lookup (div2 i) s')
        | One h t =>
            match i with
                | 0 => Some h
                | S i' => lookup i' (Zero t)
            end
    end.
Proof.
  intros. apply (@lookupGraph_unique i A s).
    apply lookup_spec.
    destruct s as [| s' | h t]; cbn.
      constructor.
      constructor. apply lookup_spec.
      destruct i as [| i']; cbn.
        constructor.
        constructor. apply lookup_spec.
Qed.

Lemma lookup_ind :
  forall P : nat -> forall A : Type, Seq A -> option A -> Prop,
    (forall (i : nat) (A : Type),
      P i A Nil None) ->
    (forall (i : nat) (A : Type) (s : Seq (A * A)%type),
      P (div2 i) (A * A)%type s (lookup (div2 i) s) ->
          P i A (Zero s) (lookup i (Zero s))) ->
    (forall (A : Type) (h : A) (t : Seq (A * A)%type),
      P 0 A (One h t) (lookup 0 (One h t))) ->
    (forall (i : nat) (A : Type) (h : A) (t : Seq (A * A)%type),
      P i A (Zero t) (lookup i (Zero t)) ->
        P (S i) A (One h t) (lookup (S i) (One h t))) ->
    forall (i : nat) (A : Type) (s : Seq A),
      P i A s (lookup i s).
Proof.
  intros.
  eapply (lookupGraph_ind (fun i A s r _ => P i A s (lookup i s))
           _ _ _ _ i A s (lookup i s) (lookup_spec i A s)).
Unshelve.
  all: cbn in *; intros; auto.
Defined.

Lemma index_aux :
  forall (i : nat) (A : Type) (l : list (A * A)%type),
    fmap (fun '(x, y) => if even i then x else y) (index (div2 i) l) =
    index i (zipjoin l).
Proof.
  intros. gen i. induction l as [| [x y] t]; cbn; intros.
    reflexivity.
    destruct i as [| [| i']]; cbn; auto.
Qed.

Lemma lookup_index :
  forall (i : nat) (A : Type) (s : Seq A),
    lookup i s = index i (toList s).
Proof.
  intros. functional induction (lookup i s) using lookup_ind; cbn.
    1, 3: reflexivity.
    rewrite lookup_eq, IHo, index_aux. reflexivity.
    rewrite lookup_eq. assumption.
Qed.

(** Properties of update *)

Lemma fupdate_spec :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A),
    fupdateGraph i A f s (fupdate i f s).
Proof.
  intros. unfold fupdate. destruct (fupdate_strong i A f s). cbn.
  assumption.
Qed.

Lemma fupdate_ind :
  forall P : nat -> forall A : Type, (A -> A) -> Seq A -> Seq A -> Prop,
    (forall (i : nat) (A : Type) (f : A -> A),
      P i A f Nil Nil) ->
    (forall (i : nat) (A : Type) (f : A -> A) (s : Seq (A * A)),
      P (div2 i) (A * A)%type (enhance i f) s
        (fupdate (div2 i) (enhance i f) s) ->
          P i A f (Zero s) (fupdate i f (Zero s))) ->
    (forall (A : Type) (f : A -> A) (h : A) (t : Seq (A * A)),
      P 0 A f (One h t) (One (f h) t)) ->
    (forall (i : nat) (A : Type) (f : A -> A) (h : A) (t : Seq (A * A)),
      P i A f (Zero t) (fupdate i f (Zero t)) ->
        P (S i) A f (One h t) (fupdate (S i) f (One h t))) ->
    forall (i : nat) (A : Type) (f : A -> A) (s : Seq A),
      P i A f s (fupdate i f s).
Proof.
  intros.
  eapply (@fupdateGraph_ind (fun i A f s _ _ => P i A f s (fupdate i f s))
          _ _ _ _ i A f s (fupdate i f s) (fupdate_spec i A f s)).
Unshelve.
  all: cbn; intros; eauto.
Defined.

Lemma fupdateGraph_unique :
  forall (i : nat) (A : Type) (f : A -> A) (s r r' : Seq A),
    fupdateGraph i A f s r -> fupdateGraph i A f s r' -> r = r'.
Proof.
  induction 1; inv 1; inj; f_equal; eauto.
Qed.

Lemma fupdateGraph_correct :
  forall (i : nat) (A : Type) (f : A -> A) (s r : Seq A),
    fupdate i f s = r -> fupdateGraph i A f s r.
Proof.
  intros. subst. apply fupdate_spec.
Qed.

Lemma fupdateGraph_complete :
  forall (i : nat) (A : Type) (f : A -> A) (s r : Seq A),
    fupdateGraph i A f s r -> fupdate i f s = r.
Proof.
  intros. eapply fupdateGraph_unique.
    apply fupdateGraph_correct. reflexivity.
    assumption.
Qed.

Lemma fupdate_eq :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A),
    fupdate i f s =
    match s with
        | Nil => Nil
        | Zero s' => Zero (fupdate (div2 i) (enhance i f) s')
        | One h t =>
            match i with
                | 0 => One (f h) t
                | S i' => cons h (fupdate i' f (Zero t))
            end
    end.
Proof.
  intros. apply (@fupdateGraph_unique i A f s).
    apply fupdate_spec.
    destruct s as [| s' | h t].
      constructor.
      constructor. apply fupdate_spec.
      destruct i as [| i'].
        constructor.
        constructor. apply fupdate_spec.
Qed.

Lemma enhance_SS :
  forall (i : nat) (A : Type) (f : A -> A),
    enhance (S (S i)) f = enhance i f.
Proof.
  reflexivity.
Qed.

Lemma lupdate_aux :
  forall (i : nat) (A : Type) (f : A -> A) (l : list (A * A)%type),
    zipjoin (lupdate (div2 i) (enhance i f) l) =
    lupdate i f (zipjoin l).
Proof.
  intros. gen i. gen f.
  induction l as [| [x y] t]; cbn; intros.
    reflexivity.
    destruct i as [| [| i']]; cbn; auto.
      rewrite enhance_SS, IHt. reflexivity.
Qed.

Lemma fupdate_lupdate :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A),
    toList (fupdate i f s) = lupdate i f (toList s).
Proof.
  intros.
  functional induction (fupdate i f s) using fupdate_ind; cbn.
    1, 3: reflexivity.
    rewrite fupdate_eq. cbn. rewrite IHs0, lupdate_aux. reflexivity.
    rewrite fupdate_eq, cons_toList, IHs0. cbn. reflexivity.
Qed.

Lemma lookup_cons :
  forall (i : nat) (A : Type) (h : A) (t : Seq A),
    lookup (S i) (cons h t) = lookup i t.
Proof.
  intros. rewrite !lookup_index, cons_toList. cbn. reflexivity.
Qed.

Lemma lookup_fupdate :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A),
    lookup i (fupdate i f s) = fmap_Option f (lookup i s).
Proof.
  intros. functional induction (fupdate i f s) using fupdate_ind; cbn.
    1, 3: reflexivity.
    rewrite (lookup_eq i A (Zero s)). rewrite fupdate_eq, lookup_eq.
      cbn. rewrite  1!IHs0. destruct (lookup (div2 i) s); cbn.
        destruct p. cbn. destruct (even i); reflexivity.
        reflexivity.
    rewrite (lookup_eq (S i) A (One h t)), <- IHs0.
    rewrite 2!fupdate_eq. cbn. rewrite lookup_eq. reflexivity.
Restart.
  intros. rewrite !lookup_index, !fupdate_lupdate.
  gen i. induction (toList s); cbn; intros.
    reflexivity.
    destruct i; cbn.
      reflexivity.
      apply IHl.
Qed.

(* TODO: Ex. 10.2 *)

Module Ex_10_2.
End Ex_10_2.

(** *** 10.1.3 Bootstrapped Queues *)
*)