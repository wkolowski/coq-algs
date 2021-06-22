Require Import CoqAlgs.Base.

Definition Queue (A : Type) : Type := list A * list A.

Definition isQueue {A : Type} (q : Queue A) : Prop :=
  let '(f, r) := q in f = [] -> r = [].

(** See note in Okasaki, p. 56 *)
Definition queue {A : Type} (f r : list A) : Queue A :=
match f with
    | [] => (rev r, [])
    | _ => (f, r)
end.

Definition empty {A : Type} : Queue A := ([], []).

Definition isEmpty {A : Type} (q : Queue A) : bool :=
match q with
    | ([], _) => true
    | _ => false
end.

Definition snoc {A : Type} (x : A) (q : Queue A) : Queue A :=
  let '(f, r) := q in queue f (x :: r).

Definition head {A : Type} (q : Queue A) : option A :=
match q with
    | ([], _) => None
    | (h :: _, _) => Some h
end.

Definition tail {A : Type} (q : Queue A) : option (Queue A) :=
match q with
    | ([], _) => None
    | (_ :: t, r) => Some (queue t r)
end.

Lemma empty_isQueue :
  forall A : Type, isQueue (@empty A).
Proof. cbn. trivial. Qed.

Lemma queue_isQueue :
  forall (A : Type) (f r : list A),
    isQueue (queue f r).
Proof.
  destruct f; cbn; intros.
    trivial.
    inversion H.
Qed.

Definition tail_isQueue :
  forall (A : Type) (q q' : Queue A),
    tail q = Some q' -> isQueue q'.
Proof.
  destruct q as [[| h t] r]; cbn; inversion 1.
    apply queue_isQueue.
Qed.

Definition snoc_isQueue :
  forall (A : Type) (x : A) (q : Queue A),
    isQueue (snoc x q).
Proof.
  destruct q as [[| h t] r]; inversion 1; trivial.
Qed.

(* Properties of [isEmpty]. *)
Lemma isEmpty_empty :
  forall A : Type, isEmpty (@empty A) = true.
Proof. reflexivity. Qed.

Lemma isEmpty_queue_true :
  forall (A : Type) (f r : list A),
    isEmpty (queue f r) = true -> f = [] /\ r = [].
Proof.
  destruct f; cbn; intros.
    case_eq (rev r); intros.
      assert (rev (rev r) = rev []) by congruence.
        rewrite rev_involutive in H1. auto.
      rewrite H0 in H. congruence.
    congruence.
Qed.

Lemma isEmpty_queue_false :
  forall (A : Type) (f r : list A),
    isEmpty (queue f r) = false -> f <> [] \/ r <> [].
Proof.
  destruct f; cbn; intros.
    case_eq (rev r); intros.
      rewrite H0 in H. congruence.
      right. intro. rewrite H1 in H0. inv H0.
    left. congruence.
Qed.

Lemma isEmpty_tail_false :
  forall (A : Type) (q : Queue A),
    isEmpty q = false -> exists q' : Queue A, tail q = Some q'.
Proof.
  destruct q as [[| h t] r]; cbn; intro.
    inv H.
    eauto.
Qed.

Lemma isEmpty_tail_false' :
  forall (A : Type) (q : Queue A),
    isEmpty q = false -> tail q <> None.
Proof.
  intros A [[| h t] r]; cbn; congruence.
Qed.

Lemma isEmpty_tail_true :
  forall (A : Type) (q : Queue A),
    isEmpty q = true -> tail q = None.
Proof.
  destruct q as [[| h t] r]; cbn; firstorder congruence.
Qed.

Lemma isEmpty_snoc :
  forall (A : Type) (x : A) (q : Queue A),
    isEmpty (snoc x q) = false.
Proof.
  destruct q as [[| h t] r]; cbn.
    case_eq (rev r ++ [x]); intros.
      destruct (rev r); inv H.
      all: trivial.
Qed.

(* [size] and its properties. *)
Definition size {A : Type} (q : Queue A) : nat :=
  let '(f, r) := q in length f + length r.

Lemma size_empty :
  forall A : Type, size (@empty A) = 0.
Proof. reflexivity. Qed.

Lemma size_queue :
  forall (A : Type) (f r : list A),
    size (queue f r) = length f + length r.
Proof.
  destruct f; cbn; intros.
    rewrite rev_length, <- plus_n_O. reflexivity.
    reflexivity.
Qed.

Lemma size_tail :
  forall (A : Type) (q q' : Queue A),
    tail q = Some q' -> size q' = pred (size q).
Proof.
  destruct q as [[| h t] r]; cbn; intros; inv H.
    rewrite size_queue. reflexivity.
Qed.

Lemma size_snoc :
  forall (A : Type) (x : A) (q : Queue A),
    size (snoc x q) = S (size q).
Proof.
  destruct q as [[| h t] r]; cbn; intros.
    rewrite app_length, rev_length, <- plus_n_O, plus_comm; cbn. reflexivity.
    rewrite plus_comm. cbn. rewrite plus_comm. reflexivity.
Qed.

(* [fmap] and its properties. *)
Definition fmap {A B : Type} (f : A -> B) (q : Queue A) : Queue B :=
  let '(front, rear) := q in (map f front, map f rear).

Lemma fmap_queue :
  forall (A B : Type) (g : A -> B) (f r : list A),
    fmap g (queue f r) = queue (map g f) (map g r).
Proof.
  destruct f as [| h t]; cbn; intros; rewrite ?map_rev; reflexivity.
Qed.

Lemma fmap_empty :
  forall (A B : Type) (f : A -> B),
    fmap f (@empty A) = @empty B.
Proof. reflexivity. Qed.

Lemma fmap_isEmpty :
  forall (A B : Type) (f : A -> B) (q : Queue A),
    isEmpty (fmap f q) = isEmpty q.
Proof.
  destruct q as [[| h t] r]; cbn; reflexivity.
Qed.

Lemma fmap_snoc :
  forall (A B : Type) (f : A -> B) (x : A) (q : Queue A),
    fmap f (snoc x q) = snoc (f x) (fmap f q).
Proof.
  destruct q. cbn. rewrite fmap_queue. reflexivity.
Qed.

Lemma fmap_head :
  forall (A B : Type) (f : A -> B) (q : Queue A),
    head (fmap f q) =
    match head q with
        | None => None
        | Some x => Some (f x)
    end.
Proof.
  destruct q as [[| h t] r]; cbn; reflexivity.
Qed.

Lemma fmap_tail :
  forall (A B : Type) (f : A -> B) (q q' : Queue A),
    tail q = Some q' -> tail (fmap f q) = Some (fmap f q').
Proof.
  destruct q as [[| h t] r]; cbn; intros; inv H.
  rewrite fmap_queue. reflexivity.
Qed.

Lemma fmap_size :
  forall (A B : Type) (f : A -> B) (q : Queue A),
    size (fmap f q) = size q.
Proof.
  destruct q. cbn. rewrite ?map_length. reflexivity.
Qed.

(* Properties of [head]. *)
Lemma head_empty :
  forall A : Type, head (@empty A) = None.
Proof. reflexivity. Qed.

Lemma head_singl :
  forall (A : Type) (x : A),
    head (snoc x empty) = Some x.
Proof. reflexivity. Qed.

Lemma head_snoc_false :
  forall (A : Type) (x : A) (q : Queue A),
    isEmpty q = false -> head (snoc x q) = head q.
Proof.
  destruct q as [[| h t] r]; cbn; intros.
    congruence.
    trivial.
Qed.

Lemma head_snoc_true :
  forall (A : Type) (x : A) (q : Queue A),
    isQueue q -> isEmpty q = true -> head (snoc x q) = Some x.
Proof.
  destruct q as [[| h t] r]; cbn; intros.
    rewrite (H eq_refl). cbn. trivial.
    congruence.
Qed.

(* Properties of tail. *)
Lemma tail_empty :
  forall A : Type, tail (@empty A) = None.
Proof. reflexivity. Qed.

Lemma tail_singl :
  forall (A : Type) (x : A),
    tail (snoc x empty) = Some empty.
Proof. reflexivity. Qed.