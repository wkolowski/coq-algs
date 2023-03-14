Require Import Div2.

From CoqAlgs Require Import Base.

Set Implicit Arguments.

Definition Deque (A : Type) : Type := list A * list A.

(* Auxiliary function that restores balance. *)
Function split {A : Type} (n : nat) (l : list A) : list A * list A :=
match n, l with
    | 0, _ => ([], l)
    | _, [] => ([], [])
    | S n', h :: t =>
        let '(f, r) := split n' t in (h :: f, r)
end.

Definition halve {A : Type} (l : list A) : list A * list A :=
  split (div2 (length l)) l.

Function deque {A : Type} (f r : list A) : Deque A :=
match f, r with
    | [], _ :: _ :: _ => let '(r, f) := halve r in (rev f, r)
    | _ :: _ :: _, [] => let '(f, r) := halve f in (f, rev r)
    | _, _ => (f, r)
end.

(* The proper Deque functions. *)
Definition empty {A : Type} : Deque A := ([], []).

Function isEmpty {A : Type} (d : Deque A) : bool :=
match d with
    | ([], []) => true
    | _ => false
end.

Definition cons {A : Type} (x : A) (d : Deque A) : Deque A :=
  let '(f, r) := d in deque (x :: f) r.

Function head {A : Type} (d : Deque A) : option A :=
match d with
    | (h :: _, _) => Some h
    | ([], [h]) => Some h
    | ([], _) => None
end.

Function tail {A : Type} (d : Deque A) : option (Deque A) :=
match d with
    | (_ :: t, r) => Some (deque t r)
    | ([], [_]) => Some empty
    | ([], _) => None
end.

Definition snoc {A : Type} (x : A) (d : Deque A) : Deque A :=
  let '(f, r) := d in deque f (x :: r).

Function last {A : Type} (d : Deque A) : option A :=
match d with
    | (_, x :: _) => Some x
    | ([x], []) => Some x
    | (_, []) => None
end.

Function init {A : Type} (d : Deque A) : option (Deque A) :=
match d with
    | (f, _ :: t) => Some (deque f t)
    | ([_], []) => Some empty
    | (_, []) => None
end.

(** Lemmas for [split]. *)
Lemma split_inv_l :
  forall {A : Type} {n : nat} {l r : list A},
    split n l = ([], r) -> n = 0 \/ (l = [] /\ r = []).
Proof.
  intros. functional induction @split A n l.
    left. reflexivity.
    right. inv H.
    inv H.
Qed.

Lemma split_inv_r :
  forall {A : Type} {n : nat} {l f : list A},
    split n l = (f, []) -> length l <= n \/ l = [] /\ f = [].
Proof.
  intros A n l. functional induction @split A n l; cbn; inv 1.
  left. apply le_n_S. destruct (IHp _ e1).
    assumption.
    inv H. cbn. apply Nat.le_0_l.
Qed.

Lemma map_split :
  forall (A B : Type) (f : A -> B) (n : nat) (l l1 l2 : list A),
    split n l = (l1, l2) -> split n (map f l) = (map f l1, map f l2).
Proof.
  intros A B f n l. functional induction @split A n l; cbn; inv 1.
    destruct n; reflexivity.
    rewrite (IHp _ _ e1). cbn. reflexivity.
Qed.

Lemma map_split' :
  forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
    split n (map f l) = (map f (fst (split n l)), map f (snd (split n l))).
Proof.
  intros. case_eq (split n l); cbn; intros.
  apply map_split. assumption.
Qed.

(* new *)
Lemma split_spec :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = (l1, l2) -> l = l1 ++ l2.
Proof.
  intros A n l. functional induction @split A n l; inv 1.
    cbn. f_equal. apply IHp. assumption.
Qed.

(* Lemmas for [div2]. *)
Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_inv_aux :
  forall n : nat, n <> 0 -> ~ n <= div2 n.
Proof.
  intros. functional induction div2 n.
    contradiction.
    intro. inv H0.
    intro. apply le_S_n in H0. destruct n'.
      cbn in H0. inv H0.
      assert (S n' <> 0) by congruence. specialize (IHn0 H1).
        assert (S n' <= Init.Nat.div2 (S n')) by lia. contradiction.
Qed.

Lemma div2_inv :
  forall n : nat, n <= div2 n -> n = 0.
Proof.
  intros. destruct n.
    trivial.
    assert (H' := @div2_inv_aux (S n) ltac:(inv 1)).
      contradiction.
Qed.

(* The Deque invariant and proofs that operations maintain it. *)
Definition isDeque {A : Type} (d : Deque A) : Prop :=
  let '(f, r) := d in 2 <= length f + length r -> f <> [] /\ r <> [].

Inductive isDeque' {A : Type} : Deque A -> Prop :=
    | isDeque0 : isDeque' ([], [])
    | isDeque1f : forall x : A, isDeque' ([x], [])
    | isDeque1r : forall x : A, isDeque' ([], [x])
    | isDequeSS :
        forall (hf hr : A) (tf tr : list A),
          isDeque' (hf :: tf, hr :: tr).

#[global] Hint Constructors isDeque' : core.

Lemma empty_isDeque :
  forall A : Type, isDeque (@empty A).
Proof.
  cbn. inv 1.
Qed.

Lemma rev_cons :
  forall (A : Type) (h : A) (t : list A),
    exists (h' : A) (t' : list A), rev (h :: t) = h' :: t'.
Proof.
  cbn. intros. destruct (rev t).
    exists h, []. cbn. reflexivity.
    exists a, (l ++ [h]). cbn. reflexivity.
Qed.

Lemma isEmpty_rev_l :
  forall (A : Type) (f r : list A),
    isEmpty (rev f, r) = isEmpty (f, r).
Proof.
  destruct f, r; cbn; try destruct (rev f); cbn; reflexivity.
Qed.

Lemma isEmpty_rev_r :
  forall (A : Type) (f r : list A),
    isEmpty (f, rev r) = isEmpty (f, r).
Proof.
  destruct f, r; cbn; try destruct (rev r); cbn; reflexivity.
Qed.

Ltac rev_cons_aux h t := 
  let h' := fresh "h'" in
  let t' := fresh "t'" in
  let H := fresh "H" in
    destruct (rev_cons h t) as [h' [t' H]]; rewrite H.

Ltac aux :=
repeat match goal with
    | H : halve _ = ([], _) |- _ =>
        destruct (split_inv_l H); cbn in *
    | H : halve _ = (_, []) |- _ =>
        destruct (split_inv_r H); cbn in *
    | H : S (S ?x) <= S (div2 ?x) |- _ =>
        apply div2_inv in H; cbn in H; inv H
    | |- context [rev (?h :: ?t)] => rev_cons_aux h t
    | H : isEmpty (rev _, _) = _ |- _ =>
        rewrite isEmpty_rev_l in H; cbn in H; try congruence
    | H : isEmpty (_, rev _) = _ |- _ =>
        rewrite isEmpty_rev_r in H; cbn in H; try congruence
    | H : _ /\ _ |- _ => destruct H
end; firstorder (auto; try congruence).

Lemma deque_isDeque :
  forall (A : Type) (f r : list A), isDeque (deque f r).
Proof.
  intros. functional induction @deque A f r; cbn; intros.
    destruct f0, r0; aux.
    destruct f0, r0; aux.
    destruct f as [| hf1 [| hf2 tf]],
             r as [| hr1 [| hr2 tr]];
    cbn in *; firstorder.
      all: inversion 1; inversion H; inversion H2.
Qed.

Lemma deque_isDeque' :
  forall (A : Type) (f r : list A), isDeque' (deque f r).
Proof.
  intros. functional induction @deque A f r; cbn; intros.
    destruct f0, r0; aux.
    destruct f0, r0; aux.
    destruct f as [| hf1 [| hf2 tf]], r as [| hr1 [| hr2 tr]]; cbn in *;
      firstorder.
Qed.

Lemma cons_isDeque :
  forall (A : Type) (x : A) (d : Deque A), isDeque (cons x d).
Proof.
  destruct d. apply deque_isDeque.
Qed.

Lemma tail_isDeque :
  forall (A : Type) (x : A) (d d' : Deque A),
    tail d = Some d' -> isDeque d'.
Proof.
  intros. functional induction @tail A d; inv H.
    apply deque_isDeque.
    apply empty_isDeque.
Qed.

Lemma snoc_isDeque :
  forall (A : Type) (x : A) (d : Deque A), isDeque (snoc x d).
Proof.
  destruct d. apply deque_isDeque.
Qed.

Lemma init_isDeque :
  forall (A : Type) (x : A) (d d' : Deque A),
    init d = Some d' -> isDeque d'.
Proof.
  intros. functional induction @init A d; inv H.
    apply deque_isDeque.
    apply empty_isDeque.
Qed.

(* Properties of [isEmpty]. *)

Lemma isEmpty_deque :
  forall (A : Type) (f r : list A),
    isEmpty (deque f r) = true -> f = [] /\ r = [].
Proof.
  intros. functional induction @deque A f r;
  cbn; auto; try congruence.
    destruct f0; aux.
    destruct f0; aux.
    destruct f as [| h1 [| h2 t]], r; firstorder.
      all: cbn in H; congruence.
Qed.

Lemma isEmpty_deque' :
  forall (A : Type) (f r : list A),
    isEmpty (deque f r) =
    match f, r with
        | [], [] => true
        | _, _ => false
    end.
Proof.
  intros. functional induction @deque A f r.
    destruct f0; aux.
    destruct f0; aux.
    destruct f as [| h1 [| h2 t]], r; firstorder.
Qed.

Lemma isEmpty_deque_true :
  forall A : Type,
    isEmpty (@deque A [] []) = true.
Proof. cbn. reflexivity. Qed.

Lemma isEmpty_deque_false_f :
  forall (A : Type) (x : A) (f r : list A),
    isEmpty (deque (x :: f) r) = false.
Proof.
  intros. rewrite isEmpty_deque'. reflexivity.
Qed.

Lemma isEmpty_deque_false_r :
  forall (A : Type) (x : A) (f r : list A),
    isEmpty (deque f (x :: r)) = false.
Proof.
  intros. rewrite isEmpty_deque'. destruct f; reflexivity.
Qed.

Lemma isEmpty_cons :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty (cons x d) = false.
Proof.
  destruct d as [f r]. unfold cons. rewrite isEmpty_deque'. reflexivity.
Qed.

Lemma isEmpty_head_false :
  forall (A : Type) (h : A) (d : Deque A),
    head d = Some h -> isEmpty d = false.
Proof.
  intros. functional induction @head A d; inv H.
Qed.

Lemma isEmpty_head_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true -> head d = None.
Proof.
  intros. functional inversion H. reflexivity.
Qed.

Lemma isEmpty_tail_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = true -> tail d = None.
Proof.
  intros. destruct d. functional inversion H; subst. reflexivity.
Qed.

Lemma isEmpty_tail_true :
  forall (A : Type) (d d' : Deque A),
    tail d = Some d' -> isEmpty d = false.
Proof.
  intros. destruct d. functional inversion H; subst; reflexivity.
Qed.

Lemma isEmpty_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty (snoc x d) = false.
Proof.
  destruct d as [f r]. unfold snoc. rewrite isEmpty_deque_false_r. auto.
Qed.

Lemma isEmpty_last_false :
  forall (A : Type) (h : A) (d : Deque A),
    last d = Some h -> isEmpty d = false.
Proof.
  intros. functional induction @last A d; inv H.
  destruct _x; reflexivity.
Qed.

Lemma isEmpty_last_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true -> last d = None.
Proof.
  intros. functional inversion H. reflexivity.
Qed.

Lemma isEmpty_init_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = true -> init d = None.
Proof.
  intros. destruct d. functional inversion H; subst. reflexivity.
Qed.

Lemma isEmpty_init_true :
  forall (A : Type) (d d' : Deque A),
    init d = Some d' -> isEmpty d = false.
Proof.
  intros. destruct d. functional inversion H; subst; cbn.
    destruct l; reflexivity.
    reflexivity.
Qed.

(* [size] and it's properties *)
Definition size {A : Type} (d : Deque A) : nat :=
  let '(f, r) := d in length f + length r.

Lemma size_empty :
  forall A : Type, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma split_length :
  forall (A : Type) (n : nat) (l l1 l2 : list A),
    split n l = (l1, l2) -> length l = length l1 + length l2.
Proof.
  intros A n l. functional induction @split A n l; inv 1.
  cbn. f_equal. apply IHp. assumption.
Qed.

Lemma size_deque :
  forall (A : Type) (f r : list A),
    size (deque f r) = length f + length r.
Proof.
  intros. functional induction @deque A f r; cbn; auto;
  apply split_length in e1; cbn in e1; rewrite rev_length; lia.
Qed.

Lemma size_cons :
  forall (A : Type) (x : A) (d : Deque A),
    size (cons x d) = S (size d).
Proof.
  destruct d as [f r]. unfold cons. rewrite size_deque. cbn. reflexivity.
Qed.

Lemma size_tail :
  forall (A : Type) (d d' : Deque A),
    tail d = Some d' -> size d' = pred (size d).
Proof.
  intros. functional inversion H; subst.
    rewrite size_deque. cbn. reflexivity.
    reflexivity.
Qed.

Lemma size_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    size (snoc x d) = S (size d).
Proof.
  intros. unfold snoc. destruct d. rewrite size_deque. cbn. lia.
Qed.

Lemma size_init :
  forall (A : Type) (d d' : Deque A),
    init d = Some d' -> size d' = pred (size d).
Proof.
  intros. functional inversion H; subst.
    rewrite size_deque. cbn. lia.
    reflexivity.
Qed.

(* [map] and its properties *)
Definition fmap {A B : Type} (f : A -> B) (d : Deque A) : Deque B :=
  let '(front, rear) := d in (map f front, map f rear).

Lemma fmap_empty :
  forall (A B : Type) (f : A -> B),
    fmap f (@empty A) = @empty B.
Proof. reflexivity. Qed.

Lemma fmap_isEmpty :
  forall (A B : Type) (f : A -> B) (d : Deque A),
    isEmpty (fmap f d) = isEmpty d.
Proof.
  intros. functional induction @isEmpty A d; cbn.
    reflexivity.
    destruct d, l, l0; cbn; firstorder.
Qed.

Lemma fmap_deque :
  forall (A B : Type) (g : A -> B) (f r : list A),
    fmap g (deque f r) = deque (map g f) (map g r).
Proof.
  intros. functional induction @deque A f r; unfold deque, halve.
    rewrite ?map_split', ?map_length. cbn in *. rewrite e1, map_rev.
      cbn. reflexivity.
    rewrite ?map_split', ?map_length. cbn in *. rewrite e1, map_rev.
      cbn. reflexivity.
    destruct f as [| hf1 [| hf2 tf]], r as [| hr1 [| hr2 tr]]; cbn;
    firstorder.
Qed.

Lemma fmap_cons :
  forall (A B : Type) (f : A -> B) (x : A) (d : Deque A),
    fmap f (cons x d) = cons (f x) (fmap f d).
Proof.
  unfold cons at 1. destruct d. rewrite fmap_deque. reflexivity.
Qed.

Lemma fmap_head :
  forall (A B : Type) (f : A -> B) (d : Deque A),
    head (fmap f d) =
    match head d with
        | None => None
        | Some x => Some (f x)
    end.
Proof.
  intros. functional induction @head A d; cbn; try reflexivity.
  destruct _x as [| h1 [| h2 t]]; cbn; try tauto.
Qed.

Lemma fmap_tail :
  forall (A B : Type) (f : A -> B) (d d' : Deque A),
    tail d = Some d' -> tail (fmap f d) = Some (fmap f d').
Proof.
  intros. functional induction @tail A d; cbn; inv H.
  f_equal. rewrite fmap_deque. reflexivity.
Qed.

Lemma fmap_snoc :
  forall (A B : Type) (f : A -> B) (x : A) (d : Deque A),
    fmap f (snoc x d) = snoc (f x) (fmap f d).
Proof.
  unfold snoc at 1. destruct d. rewrite fmap_deque. reflexivity.
Qed.

Lemma fmap_last :
  forall (A B : Type) (f : A -> B) (d : Deque A),
    last (fmap f d) =
    match last d with
        | None => None
        | Some x => Some (f x)
    end.
Proof.
  intros. functional induction @last A d; cbn; try reflexivity.
  all: destruct _x as [| h1 [| h2 t]]; cbn; tauto.
Qed.

Lemma fmap_init :
  forall (A B : Type) (f : A -> B) (d d' : Deque A),
    init d = Some d' -> init (fmap f d) = Some (fmap f d').
Proof.
  intros. functional induction @init A d; cbn; inv H.
  case_eq (map f f0); intros.
    f_equal. assert (f0 = []) by (destruct f0; inv H). subst.
      rewrite fmap_deque. reflexivity.
    rewrite fmap_deque, H. destruct l; reflexivity.
Qed.

Lemma fmap_size :
  forall (A B : Type) (f : A -> B) (d : Deque A),
    size (fmap f d) = size d.
Proof.
  destruct d. cbn. rewrite ?map_length. reflexivity.
Qed.

(* Properties of [head]. *)
(*Lemma head_deque :
  forall (A : Type) (f r : list A),
    head (deque f r) =
    match f, r with
        | 
Proof.
  intros. functional induction @deque A f r; cbn; auto;
  unfold halve in *.
    functional induction @split A (Nat.div2 (length r)) r; inv e1.
      destruct f0 as [| h1 [| h2 t]]; cbn; firstorder.
  
    match f, r with
        | [], [] => None
        | [], *)

Lemma head_empty :
  forall A : Type, head (@empty A) = None.
Proof. reflexivity. Qed.

Lemma head_cons :
  forall (A : Type) (x : A) (d : Deque A),
    head (cons x d) = Some x.
Proof.
  destruct d as [f r]. unfold cons. remember (x :: f) as f'.
  functional induction @deque A f' r; cbn in *; try congruence.
  destruct (split (div2 (length _x1)) (_x0 :: _x1)). inv e1.
Qed.

Lemma head_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    isDeque d -> isEmpty d = false -> head (snoc x d) = head d.
Proof.
  destruct d as [f r]. unfold snoc. remember (x :: r) as r'. intros.
  functional induction @deque A f r'; cbn in *; try inv Heqr'; try congruence.
    destruct _x1 as [| h1 [| h2 t]]; cbn in *.
      inv e1.
      destruct H; firstorder.
      destruct (H ltac:(lia)). congruence.
    destruct _x, r; firstorder congruence.
Qed.

(* [toList] and its properties. *)
Definition toList {A : Type} (d : Deque A) : list A :=
  let '(f, r) := d in f ++ rev r.

Lemma toList_deque :
  forall (A : Type) (f r : list A),
    toList (deque f r) = f ++ rev r.
Proof.
  intros. functional induction @deque A f r; cbn; auto;
  unfold halve in *; apply split_spec in e1.
    rewrite <- rev_app_distr, <- e1. reflexivity.
    rewrite rev_involutive, app_nil_r, e1. reflexivity.
Qed.

Lemma toList_empty :
  forall A : Type, toList (@empty A) = [].
Proof. reflexivity. Qed.

Lemma toList_cons :
  forall (A : Type) (x : A) (d : Deque A),
    toList (cons x d) = x :: toList d.
Proof.
  destruct d. unfold cons. rewrite toList_deque. cbn. reflexivity.
Qed.

Lemma toList_head :
  forall (A : Type) (d : Deque A),
    isDeque d ->
    head d =
    match toList d with
        | [] => None
        | h :: _ => Some h
    end.
Proof.
  intros. functional induction @head A d; cbn in *; auto.
  destruct _x as [| h1 [| h2 t]]; cbn in *; try tauto.
  destruct (H ltac:(lia)). congruence.
Qed.

Lemma toList_tail :
  forall (A : Type) (d d' : Deque A),
    tail d = Some d' -> toList d' =
    match toList d with
        | [] => toList d'
        | _ :: t => t
    end.
Proof.
  intros. functional induction @tail A d; cbn; inv H.
  rewrite toList_deque. reflexivity.
Qed.

Lemma toList_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    toList (snoc x d) = toList d ++ [x].
Proof.
  destruct d. unfold cons. cbn. rewrite toList_deque. cbn.
  rewrite app_assoc. reflexivity.
Qed.

Lemma toList_last :
  forall (A : Type) (d : Deque A), isDeque d ->
    last d =
    match rev (toList d) with
        | [] => None
        | h :: _ => Some h
    end.
Proof.
  intros. functional induction @last A d; cbn; auto.
    case_eq (rev (_x ++ rev _x0 ++ [x])); intros;
      rewrite !rev_app_distr in H0; cbn in *; congruence.
    cbn in H. destruct _x as [| h1 [| h2 t]]; cbn; try tauto.
      cbn in *. destruct (H ltac:(lia)). contradiction.
Qed.

Lemma toList_init :
  forall (A : Type) (d d' : Deque A),
    init d = Some d' -> toList d' =
    match rev (toList d) with
        | [] => []
        | _ :: t => rev t
    end.
Proof.
  intros. functional induction @init A d; cbn; inv H.
  rewrite toList_deque. rewrite !rev_app_distr. cbn.
  rewrite rev_app_distr, !rev_involutive. reflexivity.
Qed.

Lemma toList_size :
  forall (A : Type) (d : Deque A),
    size d = length (toList d).
Proof.
  destruct d as [f r]. unfold size. cbn.
  rewrite app_length, rev_length. reflexivity.
Qed.

(* [drev] (deque reversion) and its properties. *)
Definition drev {A : Type} (d : Deque A) : Deque A :=
  let '(f, r) := d in (r, f).

Lemma drev_spec :
  forall (A : Type) (d : Deque A),
    toList (drev d) = rev (toList d).
Proof.
  destruct d. cbn. rewrite rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma drev_inv :
  forall (A : Type) (d : Deque A), drev (drev d) = d.
Proof. destruct d; reflexivity. Qed.

Lemma drev_deque_toList :
  forall (A : Type) (f r : list A),
    toList (drev (deque f r)) = toList (deque r f).
Proof.
  intros. rewrite drev_spec, ?toList_deque, rev_app_distr, rev_involutive.
  reflexivity.
Qed.

Lemma drev_deque :
  forall (A : Type) (f r : list A),
    drev (deque f r) = deque r f.
Proof.
  intros. assert (isDeque (deque f r)) by apply deque_isDeque.
  functional induction @deque A f r; cbn; auto; unfold halve in *.
    destruct _x1 as [| hr1 [| hr2 tr]]; cbn in *; inv e1.
      case_eq (split (Nat.div2 (length tr)) (hr1 :: hr2 :: tr)); intros.
        rewrite H0 in H1. inv H1.
    destruct _x1 as [| hf1 [| hf2 tf]]; cbn in *; inv e1.
      case_eq (split (Nat.div2 (length tf)) (hf1 :: hf2 :: tf)); intros.
        rewrite H0 in H1. inv H1.
    destruct f as [| hf1 [| hf2 t]], r as [| hr1 [| hr2 tr]]; cbn; firstorder.
Qed.

Lemma drev_cons :
  forall (A : Type) (x : A) (d : Deque A),
    drev (cons x d) = snoc x (drev d).
Proof.
  destruct d as [f r]. unfold cons. rewrite drev_deque. cbn. reflexivity.
Qed.

Lemma drev_head :
  forall (A : Type) (d : Deque A),
    head (drev d) = last d.
Proof.
  intros. functional induction @head A d; cbn; auto.
    destruct _x0, _x; reflexivity.
Qed.

Lemma drev_tail :
  forall (A : Type) (d : Deque A),
    isDeque d -> tail (drev d) =
    match init d with
        | None => None
        | Some d' => Some (drev d')
    end.
Proof.
  intros. functional induction @tail A d; cbn; trivial.
    destruct r as [| hr1 [| hr2 [| hr3 tr]]], t; cbn; auto.
      destruct (split (Nat.div2 (length t)) (a :: t)).
        cbn. reflexivity.
    destruct _x as [| h1 [| h2 t]]; cbn in *; firstorder.
      destruct (H ltac:(lia)). congruence.
Qed.

(** [fromList] and its properties. *)

Definition fromList {A : Type} (l : list A) : Deque A := deque l [].

Lemma fromList_isDeque :
  forall (A : Type) (l : list A),
    isDeque (fromList l).
Proof.
  intros. apply deque_isDeque. 
Qed.

Lemma toList_fromList :
  forall (A : Type) (l : list A),
    toList (fromList l) = l.
Proof.
  intros. unfold fromList. rewrite toList_deque. cbn. apply app_nil_r.
Qed.