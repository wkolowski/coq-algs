Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Definition Deque (A : Type) : Type := list A * list A.

(* Auxiliary function that restores balance. *)
Require Import Div2.

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
    | [], [] => (f, r)
    | [], [_] => (f, r)
    | [], _ => let '(r, f) := halve r in (rev f, r)
    | [_], [] => (f, r)
    | _, [] => let '(f, r) := halve f in (f, rev r)
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
    | ([], []) => None
    | ([], [h]) => Some h
    | ([], _) => None
    | (h :: _, _) => Some h
end.

Function tail {A : Type} (d : Deque A) : option (Deque A) :=
match d with
    | ([], []) => None
    | ([], [_]) => Some empty
    | ([], _) => None
    | (_ :: t, r) => Some (deque t r)
end.

Definition snoc {A : Type} (x : A) (d : Deque A) : Deque A :=
  let '(f, r) := d in deque f (x :: r).

Function last {A : Type} (d : Deque A) : option A :=
match d with
    | ([], []) => None
    | ([x], []) => Some x
    | (_, []) => None
    | (_, x :: _) => Some x
end.

Function init {A : Type} (d : Deque A) : option (Deque A) :=
match d with
    | ([], []) => None
    | ([_], []) => Some empty
    | (_, []) => None
    | (f, _ :: t) => Some (deque f t)
end.

(** Lemmas for [split]. *)
Lemma split_inv_l :
  forall (A : Type) (n : nat) (l r : list A),
    split n l = ([], r) -> n = 0 \/ (l = [] /\ r = []).
Proof.
  intros. functional induction @split A n l.
    left. reflexivity.
    right. inv H.
    inv H.
Qed.

Lemma split_inv_r :
  forall (A : Type) (n : nat) (l f : list A),
    split n l = (f, []) -> length l <= n \/ l = [] /\ f = [].
Proof.
  intros. functional induction @split A n l; cbn; inv H.
    left. apply le_n_S. destruct (IHp _ e1).
      assumption.
      inv H. cbn. apply le_0_n.
Qed.

Lemma map_split :
  forall (A B : Type) (f : A -> B) (n : nat) (l l1 l2 : list A),
    split n l = (l1, l2) -> split n (map f l) = (map f l1, map f l2).
Proof.
  intros. functional induction @split A n l; cbn; inv H.
    destruct n; reflexivity.
    rewrite (IHp _ _ _ e1). cbn. reflexivity.
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
  intros. functional induction @split A n l; inv H.
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
        assert (S n' <= Init.Nat.div2 (S n')) by omega. contradiction.
Qed.

Lemma div2_inv :
  forall n : nat, n <= div2 n -> n = 0.
Proof.
  intros. destruct n.
    trivial.
    assert (H' := div2_inv_aux (S n) ltac:(inv 1)).
      contradiction.
Qed.

(* The Deque invariant and proofs that operations maintain it. *)
Definition isDeque {A : Type} (d : Deque A) : Prop :=
  let '(f, r) := d in 2 <= length f + length r -> f <> [] /\ r <> [].

Lemma empty_isDeque :
  forall A : Type, isDeque (@empty A).
Proof.
  cbn. inv 1.
Qed.

Lemma deque_isDeque :
  forall (A : Type) (f r : list A), isDeque (deque f r).
Proof.
  intros. functional induction @deque A f r; cbn; intros; try omega.
    destruct f0.
      destruct (split_inv_r _ _ _ _ e1).
        apply div2_inv in H0. destruct r; inv H0.
        destruct H0; subst; cbn in *. contradiction.
      destruct r0.
        apply split_inv_l in e1. destruct e1.
          destruct r as [| h1 [| h2 t]]; cbn in *; firstorder.
          inv H0.
        case_eq (rev (a :: f0)); intros.
          cbn in H0. apply app_eq_nil in H0. inv H0.
          split; congruence.
    destruct f0.
      destruct (split_inv_l _ _ _ _ e1).
        destruct f as [| h1 [| h2 t]]; cbn in *; firstorder.
        inv H0.
      destruct r0.
        apply split_inv_r in e1. destruct e1.
          apply div2_inv in H0.
            destruct f as [| h1 [| h2 t]]; cbn in *; firstorder.
          inv H0.
        case_eq (rev (a0 :: r0)); intros.
          cbn in H0. apply app_eq_nil in H0. inv H0.
          split; congruence.
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
    apply empty_isDeque.
    apply deque_isDeque.
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
    apply empty_isDeque.
    apply deque_isDeque.
Qed.

(* Properties of [isEmpty]. *)
Lemma isEmpty_deque :
  forall (A : Type) (f r : list A),
    isEmpty (deque f r) = true -> f = [] /\ r = [].
Proof.
  intros. functional induction @deque A f r;
  cbn in *; auto; try congruence.
    destruct f0.
      destruct (split_inv_r _ _ _ _ e1).
        apply div2_inv in H0. destruct r; inv H0.
        tauto.
      case_eq (rev (a :: f0)); intros.
        cbn in H0. apply app_eq_nil in H0. destruct H0. congruence.
        rewrite H0 in H. congruence.
    destruct f0.
      destruct (split_inv_l _ _ _ _ e1).
        destruct f as [| h1 [| h2 t]]; cbn in *; firstorder.
        inv H0.
      congruence.
    destruct f as [| h1 [| h2 t]], r; firstorder.
Qed.

Lemma isEmpty_cons :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty (cons x d) = false.
Proof.
  destruct d as [f r]. unfold cons.
  case_eq (isEmpty (deque (x :: f) r)); intros.
    apply isEmpty_deque in H. inv H. congruence.
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
  destruct d as [f r]. unfold snoc.
  case_eq (isEmpty (deque f (x :: r))); intros.
    apply isEmpty_deque in H. inv H. congruence.
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
    reflexivity.
    destruct l; reflexivity.
Qed.

(* [size] and it's properties *)
Definition size {A : Type} (d : Deque A) : nat :=
  let '(f, r) := d in length f + length r.

Lemma size_empty :
  forall A : Type, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma size_deque :
  forall (A : Type) (f r : list A),
    size (deque f r) = length f + length r.
Proof.
  intros. functional induction @deque A f r; cbn; try congruence.
    unfold halve in e1. clear y.
      functional induction @split A (Nat.div2 (length r)) r; inv e1; cbn.
        rewrite rev_length, <- plus_n_O. reflexivity.
        specialize (IHp _ _ e2). omega.
    unfold halve in e1. clear y.
      functional induction @split A (Nat.div2 (length f)) f; inv e1; cbn.
        rewrite <- plus_n_O. apply rev_length.
        specialize (IHp _ _ e2). omega.
Qed.

Lemma size_cons :
  forall (A : Type) (x : A) (d : Deque A),
    size (cons x d) = S (size d).
Proof.
  intros. unfold cons. destruct d. rewrite size_deque. cbn. reflexivity.
Qed.

Lemma size_tail :
  forall (A : Type) (d d' : Deque A),
    tail d = Some d' -> size d' = pred (size d).
Proof.
  intros. functional inversion H; subst.
    reflexivity.
    rewrite size_deque. cbn. reflexivity.
Qed.

Lemma size_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    size (snoc x d) = S (size d).
Proof.
  intros. unfold snoc. destruct d. rewrite size_deque. cbn. omega.
Qed.

Lemma size_init :
  forall (A : Type) (d d' : Deque A),
    init d = Some d' -> size d' = pred (size d).
Proof.
  intros. functional inversion H; subst.
    reflexivity.
    rewrite size_deque. cbn. omega.
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
  intros. functional induction @deque A f r; cbn;
  auto; unfold halve in *.
    rewrite ?map_length, map_split'. destruct r as [| h1 [| h2 t]]; cbn.
      contradiction.
      contradiction.
      cbn in *. destruct (split (Nat.div2 (length t)) (h2 :: t)).
        inv e1. cbn. rewrite map_rev. reflexivity.
    destruct f as [| h1 [| h2 t]].
      contradiction.
      contradiction.
      cbn in *. change (g h2 :: map g t) with (map g (h2 :: t)).
        rewrite ?map_length, map_split'.
        destruct (split (Nat.div2 (length t)) (h2 :: t)).
        inv e1. cbn. rewrite map_rev. reflexivity.
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
  destruct _x as [| h1 [| h2 t]]; cbn; tauto.
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
  functional induction @deque A f' r; cbn; try congruence.
  destruct f as [| hf tf]; cbn in *.
    inv e1.
    destruct (split (Nat.div2 (length tf))). inv e1.
Qed.

Lemma head_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    isDeque d -> isEmpty d = false -> head (snoc x d) = head d.
Proof.
  destruct d as [f r]. unfold snoc. remember (x :: r) as r'. intros.
  functional induction @deque A f r'; cbn in *; try inv Heqr'; try congruence.
    2: destruct _x, r; firstorder.
    destruct r as [| h1 [| h2 t]]; cbn in *.
      congruence.
      inv e1.
      destruct (H ltac:(omega)). congruence.
Qed.

(* [toList] and its properties. *)
Definition toList {A : Type} (d : Deque A) : list A :=
  let '(f, r) := d in f ++ rev r.

Lemma toList_deque :
  forall (A : Type) (f r : list A),
    toList (deque f r) = f ++ rev r.
Proof.
  intros. functional induction @deque A f r; cbn; auto;
  unfold halve in *.
    clear y. functional induction @split A (Nat.div2 (length r)) r; inv e1; cbn.
      apply app_nil_r.
      rewrite app_assoc, (IHp _ _ e2). reflexivity.
    clear y. functional induction @split A (Nat.div2 (length f)) f; inv e1; cbn.
      rewrite rev_involutive, app_nil_r. reflexivity.
      rewrite (IHp _ _ e2). reflexivity.
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
  intros. functional induction @head A d; cbn; auto.
  cbn in H. destruct _x as [| h1 [| h2 t]]; cbn; try tauto.
  cbn in *. destruct H.
    omega.
    contradiction.
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
    cbn in H. destruct _x as [| h1 [| h2 t]]; cbn; try tauto.
      cbn in *. destruct H. omega. contradiction.
    case_eq (rev (_x ++ rev _x0 ++ [x])); intros;
      rewrite !rev_app_distr in H0; cbn in *; congruence.
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

Compute drev (deque [1] [2; 3]).
Compute deque [1; 2] [].

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
    destruct r as [| hr1 [| hr2 tr]]; cbn in *; try contradiction.
      case_eq (split (Nat.div2 (length tr)) (hr2 :: tr)); intros.
        rewrite H0 in e1. inv e1.
    destruct f as [| hf1 [| hf2 tf]]; cbn in *; try contradiction.
      case_eq (split (Nat.div2 (length tf)) (hf2 :: tf)); intros.
        rewrite H0 in e1. inv e1.
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
    destruct _x as [| h1 [| h2 t]]; try contradiction.
      cbn in H. destruct (H ltac:(omega)). congruence.
    destruct r as [| hr1 [| hr2 [| hr3 tr]]], t; cbn; auto.
      destruct (split (Nat.div2 (length t)) (a :: t)).
        cbn. reflexivity.
Qed.