Require Import LinDec.
Require Import TrichDec.

Require Import InsertionSort.

Definition Task : Type := nat * nat.

Inductive CorrectSchedule : nat -> list Task -> Prop :=
    | CS_nil :
        forall n : nat, CorrectSchedule n []
    | CS_cons :
        forall (n b e : nat) (ts : list Task),
          b <= n -> S n <= e -> CorrectSchedule (S n) ts ->
            CorrectSchedule n ((b, e) :: ts)
    (*| CS_wait :
        forall (n b e : nat) (ts : list Task),
          (*n < b ->*) CorrectSchedule (S n) ((b, e) :: ts) ->
            CorrectSchedule n ((b, e) :: ts).*)
    | CS_wait :
        forall (n : nat) (ts : list Task),
          CorrectSchedule (S n) ts -> CorrectSchedule n ts.

Goal CorrectSchedule 0 [(1, 2)].
Proof.
  apply CS_wait. constructor.
      1-2: omega.
      constructor.
Qed.

Lemma CS_singl :
  forall (n b e : nat),
    b <= n -> S n <= e -> CorrectSchedule n [(b, e)].
Proof.
  induction 1; intro.
    constructor. 1-2: omega. constructor.
    constructor. 1-2: omega. constructor.
Qed.

Lemma CS_S :
  forall (n : nat) (ts : list Task),
    CorrectSchedule (S n) ts -> CorrectSchedule n ts.
Proof.
  destruct ts.
    constructor.
    intros. destruct t. apply CS_wait. assumption.
Qed.

Lemma CS_0 :
  forall (n : nat) (ts : list Task),
    CorrectSchedule n ts -> CorrectSchedule 0 ts.
Proof.
  induction n as [| n']; intros.
    assumption.
    apply IHn', CS_wait. assumption.
Qed.

Lemma le_lemma :
  forall n m : nat,
    n <= m -> exists k : nat, m = k + n.
Proof.
  induction 1.
    exists 0. reflexivity.
    destruct IHle as [k IH]. exists (S k). cbn. rewrite IH. reflexivity.
Qed.

Lemma CS_le :
  forall (n m : nat) (ts : list Task),
    n <= m -> CorrectSchedule m ts -> CorrectSchedule n ts.
Proof.
  intros. destruct (le_lemma _ _ H) as [k H']. subst.
  induction k as [| k']; subst.
    assumption.
    apply IHk'.
      apply CS_wait. assumption.
      omega.
Qed.

Definition leq_Task : Task -> Task -> Prop :=
  fun '(b1, e1) '(b2, e2) => b1 < b2 \/ b1 = b2 /\ e1 <= e2.

Require Import NArith.

Definition leqb_Task : Task -> Task -> bool :=
  fun '(b1, e1) '(b2, e2) =>
  match b1 <?> b2 with
      | Lt => true
      | Eq => leb e1 e2
      | Gt => false
  end.

#[refine]
Instance LinDec_Task : LinDec :=
{
    carrier := Task;
    leq := leq_Task;
    leqb := leqb_Task
}.
Proof.
  destruct x as [b e]. cbn. right. omega.
  destruct x as [b1 e1], y as [b2 e2]. cbn. firstorder.
  destruct x as [b1 e1], y as [b2 e2], z as [b3 e3]. cbn. firstorder.
  destruct x as [b1 e1], y as [b2 e2]. cbn.
    destruct (le_lt_dec b1 b2).
      destruct (le_lt_eq_dec _ _ l).
        left. left. assumption.
        subst. destruct (le_lt_dec e1 e2).
          left. right. split; trivial.
          do 2 right. split; trivial. omega.
      right. left. assumption.
  destruct x as [b1 e1], y as [b2 e2]. cbn.
    destruct (trichb_nat b1 b2) eqn: H.
      constructor. left. rewrite <- (@trichb_spec1 natlt). assumption.
      rewrite (@trichb_spec2 natlt) in H. subst.
        destruct (leb e1 e2) eqn: H.
          constructor. right. split.
            reflexivity.
            apply leb_complete. assumption.
          constructor. intro. destruct H0.
            omega.
            destruct H0. apply leb_correct in H1. congruence.
      constructor. intro. destruct H0.
        rewrite (@trichb_spec3 natlt) in H.
          apply Nat.lt_asymm in H. contradiction.
        destruct H0; subst. apply (Nat.lt_irrefl b2).
          rewrite (@trichb_spec3 natlt) in H. assumption.
Defined.

Definition sort (ts : list Task) : list Task :=
  insertionSort LinDec_Task ts.

Compute sort [(1, 3); (2, 4); (1, 5); (1, 2); (2, 2); (2, 5)].

(*Function schedule_aux
  {A : Type} (time : nat) (ts : list Task) : list Task :=*)

Axiom schedule_aux : forall
  {A : Type} (time : nat) (ts : list Task), list Task.

Axiom schedule : forall
  {A : Type} (ts : list Task), option (list Task).

(*match sort ts with
    | [] => Some []
    | (b, e) :: ts' =>
        match schedule_aux b (sort ts) with
            | None => None
            | 
end.*)

