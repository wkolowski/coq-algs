From CoqAlgs Require Export Base.

Set Implicit Arguments.

(* Commutative rings with unit. *)
Class UCRing : Type :=
{
    carrier : Type;
    add : carrier -> carrier -> carrier;
    mul : carrier -> carrier -> carrier;
    zero : carrier;
    one : carrier;
    neg : carrier -> carrier;
    add_assoc: forall x y z : carrier, add (add x y) z = add x (add y z);
    add_comm : forall x y : carrier, add x y = add y x;
    zero_l : forall x : carrier, add zero x = x;
    zero_r : forall x : carrier, add x zero = x;
    neg_l : forall x : carrier, add (neg x) x = zero;
    neg_r : forall x : carrier, add x (neg x) = zero;
    mul_assoc: forall x y z : carrier, mul (mul x y) z = mul x (mul y z);
    mul_comm : forall x y : carrier, mul x y = mul y x;
    one_l : forall x : carrier, mul one x = x;
    one_r : forall x : carrier, mul x one = x;
    distr_l : forall x y z : carrier,
      mul x (add y z) = add (mul x y) (mul x z);
    distr_r : forall x y z : carrier,
      mul (add x y) z = add (mul x z) (mul y z);
}.

Notation "x + y" := (add x y).
Notation "x - y" := (add x (neg y)).
Notation "x * y" := (mul x y).
Notation "0" := zero.
Notation "1" := one.
Notation "- x" := (neg x).

Coercion carrier : UCRing >-> Sortclass.

(* Basic tactics for rewriting UCRing axioms. *)
#[global] Hint Rewrite @zero_l @zero_r @one_l @one_r @neg_l @neg_r : units.
#[global] Hint Rewrite @add_assoc @mul_assoc : assoc.
#[global] Hint Rewrite <- @add_assoc @mul_assoc : assoc'.
#[global] Hint Rewrite @add_comm @mul_comm : comm.
#[global] Hint Rewrite @distr_l @distr_r : distr.
#[global] Hint Rewrite <- @distr_l @distr_r : distr'.

Ltac rng := cbn; intros; autorewrite with units assoc distr; try congruence.
Ltac rng' := cbn; intros; autorewrite with units assoc' distr'; try congruence.

(* Basic lemmas. *)
Lemma add_cancel_l :
  forall (X : UCRing) (a b b' : X), a + b = a + b' -> b = b'.
Proof.
  intros.
  assert (-a + (a + b) = b); rng'.
  assert (-a + (a + b') = b'); rng'.
Qed.

Lemma add_cancel_r :
  forall (X : UCRing) (a a' b : X), a + b = a' + b -> a = a'.
Proof.
  intros. rewrite (add_comm a), (add_comm a') in H.
  eapply add_cancel_l. exact H.
Qed.

Lemma neg_neg :
  forall (X : UCRing) (x : X), --x = x.
Proof.
  intros.
  assert (-x + x = 0); rng.
  assert (-x + --x = 0); rng.
  eapply add_cancel_l. rewrite H0. rng.
Qed.

Lemma minus_a_a :
  forall (X : UCRing) (a : X), a - a = 0.
Proof. rng. Qed.

Lemma mul_0_l :
  forall (X : UCRing) (x : X), 0 * x = 0.
Proof.
  intros.
  assert (0 * x = (0 + 0) * x); rng.
  rewrite distr_r in H.
  assert (0 * x - 0 * x = 0 * x + (0 * x - 0 * x)).
    rewrite <- add_assoc, <- H. trivial.
    rewrite (minus_a_a X (0 * x)) in H0. rewrite zero_r in H0. rng.
Qed.

Lemma mul_0_r :
  forall (X : UCRing) (x : X), x * 0 = 0.
Proof.
  intros. rewrite mul_comm. apply mul_0_l.
Qed.

Lemma minus_zero :
  forall X : UCRing, -0 = 0.
Proof.
  intro.
  rewrite <- (neg_l zero) at 2.
  rewrite zero_r.
  reflexivity.
Qed.

Lemma minus_one_l :
  forall (X : UCRing) (a : X), -(1) * a = -a.
Proof.
  intros.
  apply (add_cancel_l X (1 * a)).
  rewrite <- distr_r, one_l, 2!minus_a_a, mul_0_l.
  reflexivity.
Qed.

Lemma minus_one_r :
  forall (X : UCRing) (a : X), a * -(1) = -a.
Proof.
  intros. rewrite mul_comm. apply minus_one_l.
Qed.

Lemma minus_one_x2 :
  forall X : UCRing, -(1) * -(1) = 1.
Proof.
  intros. rewrite minus_one_l, neg_neg. trivial.
Qed.

Lemma mul_minus_minus :
  forall (X : UCRing) (a b : X), -a * -b = a * b.
Proof.
  intros. rewrite <- (minus_one_l X a), <- (minus_one_l X b).
  rewrite <- mul_assoc, (mul_comm (-(1))).
  rewrite 2!mul_assoc, <- (mul_assoc (-(1))), minus_one_x2. rng.
Qed.

Lemma neg_add :
  forall (X : UCRing) (a b : X), -(a + b) = -a + -b.
Proof.
  intros.
  assert (-(a + b) + (a + b) = 0); rng.
  assert ((-a - b) + (a + b) = 0); rng.
    rewrite (add_comm a). rewrite <- (add_assoc (-b)). rewrite neg_l. rng.
    rewrite <- H0 in H. apply add_cancel_r in H. assumption.
Qed.

Lemma neg_mul :
  forall (X : UCRing) (a b : X), -(a * b) = (-a) * b.
Proof.
  intros. rewrite <- (minus_one_l X (a * b)), <- (minus_one_l X a).
  rewrite ?mul_assoc. trivial.
Qed.

Lemma neg_eq :
  forall (X : UCRing) (a b : X), -a = -b -> a = b.
Proof.
  intros. rewrite <- (neg_neg X a), <- (neg_neg X b).
  rewrite H. trivial.
Qed.

(* Hint base for lemma rewriting. *)
#[global] Hint Rewrite
  add_cancel_l add_cancel_r
  neg_neg neg_add neg_mul neg_eq
  mul_0_l mul_0_r mul_minus_minus
  minus_zero minus_one_l minus_one_r minus_one_x2
  : lemmas.