(** * 10 Data-Structural Bootstrapping *)

Require Import List.
Import ListNotations.

(** ** 10.1 Structural Decomposition *)

(** *** 10.1.2 Binary Random-Access Lists Revisited *)

Inductive Seq (A : Type) : Type :=
    | Nil : Seq A
    | Zero : Seq (A * A) -> Seq A
    | One : A -> Seq (A * A) -> Seq A.

Arguments Nil [A].
Arguments Zero [A] _.
Arguments One [A] _ _.

Definition empty {A : Type} : Seq A := Nil.

Definition isEmpty {A : Type} (s : Seq A) : bool :=
match s with
    | Nil => true
    | _ => false
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

Add Rec LoadPath "/home/Zeimer/Code/Coq".
Require Import HSLib.Base.
Require Import HSLib.Control.Functor.
Require Import HSLib.Instances.All.

Definition head {A : Type} (s : Seq A) : option A :=
  fmap fst (uncons s).

Definition tail {A : Type} (s : Seq A) : option (Seq A) :=
  fmap snd (uncons s).

Require Import Div2.

(** lookup v1 *)
Inductive lookupDom : nat -> forall A : Type, Seq A -> Type :=
    | dom_Nil :
        forall {i : nat} {A : Type}, lookupDom i A Nil
    | dom_Zero :
        forall {i : nat} {A : Type} {s : Seq (A * A)},
          lookupDom (div2 i) (A * A) s -> lookupDom i A (Zero s)
    | dom_One_0 :
        forall {A : Type} (h : A) {t : Seq (A * A)},
          lookupDom 0 A (One h t)
    | dom_One_S :
        forall {i : nat} {A : Type} {h : A} {t : Seq (A * A)},
          lookupDom i A (Zero t) -> lookupDom (S i) A (One h t).

Lemma lookupDom_all :
  forall (i : nat) (A : Type) (s : Seq A), lookupDom i A s.
Proof.
  intros. gen i.
  induction s as [| s' | h t]; intros.
    constructor.
    constructor. apply IHs.
    destruct i as [| i'].
      constructor.
      constructor. constructor. apply IHs.
Defined.

Fixpoint even (n : nat) : bool :=
match n with
    | 0 => true
    | 1 => false
    | S (S n') => even n'
end.

Fixpoint lookup_aux
  {i : nat} {A : Type} {s : Seq A} (dom : lookupDom i A s) : option A :=
match dom with
    | dom_Nil => None
    | dom_Zero dom =>
        match lookup_aux dom with
            | None => None
            | Some (x, y) => Some (if even i then x else y)
        end
    | dom_One_0 h => Some h
    | dom_One_S dom => lookup_aux dom
end.

Definition lookup
  (i : nat) {A : Type} (s : Seq A) : option A :=
    lookup_aux (lookupDom_all i A s).

(*Lemma lookup_aux_eq :
  forall (i : nat) (A : Type) (s : Seq A) (dom : lookupDom i A s),
    lookup_aux dom =
    match s with
        | Nil => None
        | Zero s' => fmap (fun '(x, y) => if even i then x else y)
                          (lookup_aux (div2 i) s')
        | One h t =>
            match i with
                | 0 => Some h
                | S i' => fmap (fun '(x, y) => if even i then x else y)
                               (lookup (div2 i') t)
            end
end.*)

Lemma lookup_eq_Nil :
  forall (i : nat) (A : Type) (s : Seq A),
    lookup i Nil = @None A.
Proof. reflexivity. Qed.

Lemma lookup_aux_eq_dom_Zero :
  forall (i : nat) (A : Type) (s : Seq (A * A))
  (w : lookupDom (div2 i) (A * A) s),
    lookup_aux (dom_Zero w) =
    fmap (fun '(x, y) => if even i then x else y) (lookup_aux w).
Proof.
Abort.

(*Lemma lookup_eq_Zero :
  forall (i : nat) (A : Type) (s : Seq (A * A)),
    lookup i (Zero s) =
    fmap (fun '(x, y) => if even i then x else y) (lookup (div2 i) s).
Proof.
*)  
  

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
  intros. unfold lookup.
  pose (w := lookupDom_all i A s).
  replace (lookupDom_all i A s) with w by reflexivity.
  clearbody w.
  induction w; auto.
Abort.

(** lookup v2 *)
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

Definition lookup'_strong
  (i : nat) {A : Type} (s : Seq A)
  : {r : option A & lookupGraph i A s r}.
Proof.
  gen i. induction s as [| A s' | A h t]; intros.
    exists None. auto.
    destruct (IHs' (div2 i)). eauto.
    destruct i as [| i'].
      exists (Some h). constructor.
      destruct (IHt (div2 i')) as [r g]. eauto.
Defined. (*
  gen s; gen A; gen i. fix 3. destruct s as [| s' | h t].
    exists None. constructor.
    destruct (lookup'_strong (div2 i) _ s'). clear -l. eauto.
    destruct i as [| i'].
      exists (Some h). eauto.
      destruct (lookup'_strong i' _ (Zero t)).
Defined.*)

Definition lookup'
  (i : nat) {A : Type} (s : Seq A) : option A :=
    projT1 (lookup'_strong i s).

Require Import Eqdep.

        Ltac inj := repeat
        match goal with
            | H : existT _ _ _ = existT _ _ _ |- _ =>
                apply inj_pair2 in H
        end; subst.

Lemma lookup'_eq :
  forall (i : nat) (A : Type) (s : Seq A),
    lookup' i s =
    match s with
        | Nil => None
        | Zero s' => fmap (fun '(x, y) => if even i then x else y)
                          (lookup' (div2 i) s')
        | One h t =>
            match i with
                | 0 => Some h
                | S i' => lookup' i' (Zero t)
            end
end.
Proof.
  intros i A s. gen i.
  induction s as [| s' | h t]; cbn; intros.
    reflexivity.
    Focus 2. unfold lookup'. simpl. destruct i; cbn; auto.
      destruct (lookup'_strong (PeanoNat.Nat.div2 i) s). cbn. reflexivity.
    unfold lookup'. cbn in *.
    destruct (Seq_rect _ _). cbn. unfold lookup' in IHs.
(* cbn in IHs. rewrite IHs.*)
      Require Import Eqdep.
      destruct s.
        f_equal. inversion l. reflexivity.
        Focus 2. rewrite IHs. inversion l; inj.
          reflexivity.
          f_equal. cbn. destruct (Seq_rect _ _). cbn. 
        f_equal. inversion l.
        inj.
Abort.

Fixpoint size_add {A : Type} (s : Seq A) : nat :=
match s with
    | Nil => 0
    | Zero s' => 1 + size_add s'
    | One _ t => 2 + size_add t
end.

Require Import Recdef.

(*Function lookup2
  (i : nat) {A : Type} (s : Seq A) {measure size s} : option A :=
match s with
    | Nil => None
    | Zero s' => (*fmap (fun '(x, y) => if even i then x else y)
                      (lookup2 (div2 i) s')*)
        match @lookup2 (div2 i) (A * A) s' with
            | None => None
            | Some p => Some (if even i then fst p else snd p)
        end
    | One h t =>
        match i with
            | 0 => Some h
            | S i' => lookup2 i' (Zero t)
        end
end.*)

(** update *)
Definition enhance {A : Type} (i : nat) (f : A -> A) : A * A -> A * A :=
  fun '(x, y) => if even i then (f x, y) else (x, f y).

Inductive fupdateDom
  : nat -> forall A : Type, (A -> A) -> Seq A -> Type :=
    | fDom_Nil :
        forall i A f, fupdateDom i A f Nil
    | fDom_Zero :
        forall i A f s,
          fupdateDom (div2 i) (A * A) (enhance i f) s ->
          fupdateDom i A f (Zero s)
    | fDom_One_0 :
        forall A f h t,
          fupdateDom 0 A f (One h t)
    | fDom_One_S :
        forall i A f h t,
          fupdateDom i A f (Zero t) -> fupdateDom (S i) A f (One h t).

Arguments fDom_Nil [i A f].
Arguments fDom_Zero [i A f s] _.
Arguments fDom_One_0 [A] _ _ _.
Arguments fDom_One_S [i A f] _ [t] _.

Lemma fupdateDom_all :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A), fupdateDom i A f s.
Proof.
  intros. gen f; gen i.
  induction s as [| s' | h t]; cbn; intros.
    constructor.
    constructor. apply IHs.
    destruct i as [| i']; repeat constructor. apply IHs.
Defined.

Fixpoint fupdate_aux
  {i : nat} {A : Type} {f : A -> A} {s : Seq A} (dom : fupdateDom i A f s)
  : Seq A :=
match dom with
    | fDom_Nil => Nil
    | fDom_Zero dom' => Zero (fupdate_aux dom')
    | fDom_One_0 f h t => One (f h) t
    | fDom_One_S h dom' => cons h (fupdate_aux dom')
 end.

Definition fupdate
  (i : nat) {A : Type} (f : A -> A) (s : Seq A) : Seq A :=
    fupdate_aux (fupdateDom_all i A f s).

Definition update
  (i : nat) {A : Type} (y : A) (s : Seq A) : Seq A :=
    fupdate i (const y) s.

(** Other functions *)

Fixpoint fromList {A : Type} (l : list A) : Seq A :=
  let aux := fix f (l : list A) : Seq A :=
    match l with
        | [] => Nil
        | h :: t => cons h (f t)
    end
  in aux l.

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

(** Tests *)

Let to_1_10 := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Compute fromList to_1_10.
Compute update 5 42 (fromList to_1_10).
Compute lookup 1 (fromList to_1_10).
Compute lookup' 1 (fromList to_1_10).
Compute update 1 42 (fromList to_1_10).

(** Properties of empty *)

(** Properties of cons *)

Lemma cons_uncons :
  forall (A : Type) (x : A) (s s' : Seq A),
    uncons s = Some (x, s') -> cons x s' = s.
Proof.
  intros. functional induction @uncons A s.
    congruence.
    congruence.
    inversion H; subst. cbn. rewrite IHo; auto.
    inversion H. cbn. reflexivity.
Qed.

Lemma toList_cons :
  forall (A : Type) (x : A) (s : Seq A),
    toList (cons x s) = x :: toList s.
Proof.
  intros. functional induction @cons A x s; cbn.
    reflexivity.
    reflexivity.
    rewrite IHs0. cbn. reflexivity.
Qed.

Lemma cons_not_Nil :
  forall (A : Type) (x : A) (s : Seq A),
    cons x s <> Nil.
Proof.
  induction s as [| s' | h t]; inversion 1.
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

(** Properties of uncons *)

Require Import Eqdep.

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
    apply cons_uncons in e0. rewrite <- e0, toList_cons. cbn. reflexivity.
    reflexivity.
Qed.

(** Properties of lookup and lookup' *)

Lemma lookup_aux_spec :
  forall (i : nat) (A : Type) (s : Seq A) (dom : lookupDom i A s),
    lookup_aux dom = index i (toList s).
Proof.
  induction dom; cbn; auto.
  rewrite IHdom. clear -s. gen i.
  induction (toList s) as [| h t]; cbn; intros.
    reflexivity.
    destruct i as [| [| i']], h; cbn.
      reflexivity.
      reflexivity.
      apply IHt.
Qed.

Lemma lookup_spec :
  forall (i : nat) (A : Type) (s : Seq A),
    lookup i s = index i (toList s).
Proof.
  intros. apply lookup_aux_spec.
Qed.

Theorem lookup'_spec :
  forall (i : nat) (A : Type) (s : Seq A),
    lookupGraph i A s (lookup' i s).
Proof.
  intros. unfold lookup'.
  destruct (lookup'_strong i s) as [r H].
  cbn. assumption.
Qed.

(** Properties of update *)

Lemma fupdate_aux_spec :
  forall (i : nat) (A : Type) (f : A -> A) (s : Seq A)
  (dom : fupdateDom i A f s),
    toList (fupdate_aux dom) = lupdate i f (toList s).
Proof.
  induction dom; cbn; auto.
    rewrite IHdom. clear -s. gen i.
      induction (toList s) as [| h t ]; cbn; intros.
        reflexivity.
        destruct i as [| [| i']], h; cbn in *; auto.
          unfold enhance. cbn. rewrite IHt. reflexivity.
    rewrite toList_cons, IHdom. cbn. reflexivity.
Qed.

(* TODO: Ex. 10.2 *)

Module Ex_10_2.
End Ex_10_2.

(** *** 10.1.3 Bootstrapped Queues *)