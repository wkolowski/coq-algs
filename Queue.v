Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import RCCBase.

Definition queue (A : Type) : Type := list A * list A.

Definition isQueue {A : Type} (q : queue A) : Prop :=
  let '(l, r) := q in l = [] -> r = [].

Definition empty {A : Type} : queue A := ([], []).

Lemma empty_isQueue :
  forall A : Type, isQueue (@empty A).
Proof.
  compute. trivial.
Qed.

Definition normalize {A : Type} (q : queue A) : queue A :=
match q with
    | ([], r) => (rev r, [])
    | _ => q
end.

Lemma normalize_isQueue :
  forall (A : Type) (q : queue A),
    isQueue (normalize q).
Proof.
  intros. destruct q, l; cbn.
    trivial.
    inversion 1.
Qed.

Definition enqueue {A : Type} (x : A) (q : queue A) : queue A :=
  let '(l, r) := q in normalize (l, x :: r).

Lemma enqueue_isQueue :
  forall (A : Type) (x : A) (q : queue A),
    isQueue q -> isQueue (enqueue x q).
Proof.
  destruct q, l; cbn; intros.
    trivial.
    inv H0.
Qed.

Definition dequeue {A : Type} (q : queue A) : queue A :=
match q with
    | ([], []) => ([], [])
    | (_ :: l, r) => normalize (l, r)
    | ([], r) => (tl (rev r), [])
end.

Lemma dequeue_isQueue :
  forall (A : Type) (q : queue A),
    isQueue q -> isQueue (dequeue q).
Proof.
  destruct q, l as [| hl tl]; cbn; intros.
    rewrite H; cbn; trivial.
    destruct tl; cbn.
      trivial.
      inversion 1.
Qed.

Definition first {A : Type} (q : queue A) (H : isQueue q)
  : option A.
Proof.
  destruct q. cbn in *. gen l0; gen l.
  refine (fun l r => 
  match l, r with
      | [], [] => fun _ => None
      | h :: _, _ => fun _ => Some h
      | [], _ => _
  end).
  intro. specialize (H eq_refl). inv H.
Defined.

Definition isEmpty {A : Type} (q : queue A) : bool :=
match q with
    | ([], []) => true
    | _ => false
end.

Lemma isEmpty_empty :
  forall A : Type, isEmpty (@empty A) = true.
Proof.
  compute. trivial.
Qed.

Lemma isEmpty_enqueue :
  forall (A : Type) (x : A) (q : queue A),
    isEmpty (enqueue x q) = false.
Proof.
  destruct q, l; cbn.
    case_eq (rev l0 ++ [x]); intros.
      apply app_eq_nil in H. destruct H. congruence.
      congruence.
    trivial.
Qed.

Lemma dequeue_empty :
  forall A : Type, dequeue (@empty A) = @empty A.
Proof.
  compute. trivial.
Qed.

Lemma dequeue_enqueue :
  forall (A : Type) (x : A),
    dequeue (enqueue x empty) = empty.
Proof.
  compute. trivial.
Qed.

Lemma first_empty :
  forall A : Type, first empty (empty_isQueue A) = @None A.
Proof.
  compute. trivial.
Qed.

Lemma first_singl :
  forall (A : Type) (x : A) (H : isQueue (enqueue x empty)),
    first (enqueue x empty) H = Some x.
Proof.
  compute. trivial.
Qed.

Lemma first_enqueue :
  forall (A : Type) (x y : A) (q : queue A)
  (Hxy : isQueue (enqueue x (enqueue y q))) (Hy : isQueue (enqueue y q)),
    first (enqueue x (enqueue y q)) Hxy = first (enqueue y q) Hy.
Proof.
  destruct q, l; cbn; intros.
    case_eq (rev l0 ++ [y]); intros.

Lemma enqueue_dequeue' :
  forall (A : Type) (x y : A) (q : queue A),
    isQueue q -> isEmpty q = false ->
      dequeue (enqueue x (enqueue y q)) = enqueue x (dequeue (enqueue y q)).
Proof.
  intros.
  destruct q, l as [| hl tl]; cbn in *; intros.
    rewrite H in H0; congruence.
    reflexivity.
Qed.