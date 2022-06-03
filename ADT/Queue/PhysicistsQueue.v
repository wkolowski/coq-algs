From CoqMTL Require Import Control.Monad.Lazy.

From CoqAlgs Require Import Base.
From CoqAlgs Require Import Structures.Ord.

Definition Queue (A : Type) : Type :=
  list A * nat * Lazy (list A) * nat * list A.

Definition empty {A : Type} : Queue A :=
  ([], 0, delay [], 0, []).

Definition isEmpty {A : Type} (q : Queue A) : bool :=
  let '(w, _, _, _, _) := q in
match w with
    | [] => true
    | _ => false
end.

Definition checkw {A : Type} (q : Queue A) : Queue A :=
  let '(w, lenf, f, lenr, r) := q in
match w with
    | [] => (force f, lenf, f, lenr, r)
    | _ => q
end.

Definition queue {A : Type} (q : Queue A) : Queue A :=
  let '(w, lenf, f, lenr, r) := q in
(*   if @trich_leb natlt lenr lenf *)
  if Nat.leb lenr lenf
  then checkw q
  else
    let
      f' := force f
    in
      checkw (f', lenf + lenr, delay (force f ++ rev r), 0, []).

Definition snoc {A : Type} (x : A) (q : Queue A) : Queue A :=
  let '(w, lenf, f, lenr, r) := q in
    queue (w, lenf, f, 1 + lenr, x :: r).

Definition tl {A : Type} (l : list A) : list A :=
match l with
    | [] => []
    | _ :: t => t
end.

Definition tail {A : Type} (q : Queue A) : option (Queue A) :=
  let '(w, lenf, f, lenr, r) := q in
match w with
    | [] => None
    | h :: t => Some (queue (t, pred lenf, delay (tl (force f)), lenr, r))
end.

Definition head {A : Type} (q : Queue A) : option A :=
  let '(w, lenf, f, lenr, r) := q in
match w with
    | [] => None
    | h :: _ => Some h
end.

(** The queue invariant. *)

Inductive prefix {A : Type} : list A -> list A -> Prop :=
    | prefix_nil :
        forall l : list A, prefix [] l
    | prefix_cons :
        forall (h : A) (t l : list A),
          prefix t l -> prefix (h :: t) (h :: l).

#[global] Hint Constructors prefix : core.

Lemma prefix_app :
  forall (A : Type) (l1 l2 : list A),
    prefix l1 (l1 ++ l2).
Proof.
  induction l1 as [| h1 t1]; cbn; auto.
Qed.

Lemma prefix_refl :
  forall (A : Type) (l : list A),
    prefix l l.
Proof.
  induction l; auto.
Qed.

#[global] Hint Resolve prefix_app prefix_refl : core.

Lemma prefix_char :
  forall (A : Type) (l1 l2 : list A),
    prefix l1 l2 <-> exists suffix : list A, l1 ++ suffix = l2.
Proof.
  split.
    induction 1; cbn; firstorder eauto. exists x. congruence.
    destruct 1 as [suffix <-]. apply prefix_app.
Qed.

Definition isQueue {A : Type} (q : Queue A) : Prop :=
  let '(w, lenf, f, lenr, r) := q in
    prefix w (force f) /\ lenf = length (force f)
    /\ lenr = length r /\ lenr <= lenf.

Lemma empty_isQueue :
  forall A : Type, isQueue (@empty A).
Proof. cbn. auto. Qed.

Ltac q := repeat
match goal with
    | |- forall q : Queue _, _ =>
        let w := fresh "w" in
        let lenf := fresh "lenf" in
        let f := fresh "f" in
        let lenr := fresh "lenr" in
        let r := fresh "r" in
          destruct q as [[[[w lenf] f] lenr] r]
    | |- forall _, _ => intro
end.

Lemma checkw_isQueue :
  forall (A : Type) (q : Queue A),
    isQueue q -> isQueue (checkw q).
Proof.
  unfold isQueue. q.
  cbn. destruct w; firstorder.
Qed.

Lemma queue_isQueue :
  forall (A : Type) (q : Queue A),
    isQueue q -> isQueue (queue q).
Proof.
  q. cbn. destruct (Nat.leb lenr lenf).
    destruct w; cbn in *; firstorder.
    cbn in *. destruct (force f); cbn in *.
      rewrite rev_length. firstorder; lia.
      rewrite app_length, rev_length. firstorder; lia.
Qed.

Lemma snoc_isQueue :
  forall (A : Type) (x : A) (q : Queue A),
    isQueue q -> isQueue (snoc x q).
Proof.
  q. cbn in *. destruct lenf as [| lenf']; cbn.
    firstorder. destruct (force f); cbn in *; try congruence.
      firstorder.
        rewrite app_length. cbn. rewrite rev_length. lia.
        lia.
    firstorder. destruct (Nat.leb_spec lenr lenf').
      destruct w; cbn; firstorder; lia.
      destruct (force f); cbn in *; firstorder; try lia.
        rewrite !app_length, rev_length. cbn. lia.
Qed.

Lemma force_delay :
  forall (A : Type) (x : A),
    force (delay x) = x.
Proof. compute. reflexivity. Qed.

Lemma tail_isQueue :
  forall (A : Type) (q q' : Queue A),
    tail q = Some q' -> isQueue q -> isQueue q'.
Proof.
  q; cbn in *. destruct w.
    inv H.
    destruct (Nat.leb_spec lenr (pred lenf)).
      destruct w; inv H; rewrite force_delay; firstorder.
        destruct (force f); cbn in *; subst; auto.
        inv H.
        inv H. rewrite <- H7 in *. cbn in *. lia.
      rewrite !force_delay in *. destruct (force f); cbn in *; inv H.
        inv H0. inv H.
        destruct l; inv H3; firstorder; try lia; rewrite force_delay; inv H.
          rewrite rev_length. cbn. reflexivity.
          cbn. rewrite app_length, rev_length. reflexivity.
Qed.