Require Import LinDec.
Require Import TrichDec.

Require Import InsertionSort.

Definition Task : Type := nat * nat.

Definition Schedule : Type := list (nat * Task).

Inductive CorrectSchedule : Schedule -> Prop :=
    | CS_nil : CorrectSchedule []
    | CS_singl :
        forall n b e : nat,
          b <= n < e -> CorrectSchedule [(n, (b, e))]
    | CS_cons :
        forall (n1 b1 e1 n2 b2 e2 : nat) (ts : Schedule),
          b1 <= n1 < e1 -> n1 < n2 ->
          CorrectSchedule ((n2, (b2, e2)) :: ts) ->
            CorrectSchedule ((n1, (b1, e1)) :: (n2, (b2, e2)) :: ts).

(*Goal CorrectSchedule [(0, (1, 2))].
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
*)

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

(*Function schedule_aux
  (ts : list Task) {measure length ts} : option Schedule :=
match ts with
    | [] => Some (@nil _)
    | (b1, e1) :: ts =>
        if leb (S b1) e1
        then
          match schedule_aux (map (fun '(b, e) => (max (S b1) b, e)) ts) with
              | None => None
              | Some [] => Some [(b1, (b1, e1))]
              | Some ((n, (b2, e2)) :: ts') =>
                  if leb (S b1) n
                  then Some ((b1, (b1, e1)) :: (n, (b2, e2)) :: ts')
                  else None
          end
        else None
end.
Proof.
  intros. subst. induction ts0; cbn.
    apply le_n.
    apply lt_n_S. assumption.
Defined.

Definition schedule (ts : list Task) : option Schedule :=
  schedule_aux (sort ts).
*)

Inductive Result : Type :=
    | Failure : Result
    | End : Result
    | Success : Task -> list Task -> Result.

Fixpoint min
  (time : nat) (ts : list Task) : option (Task * list Task) :=
match ts with
    | [] => None
    | (b1, e1) :: ts' =>
        match min time ts' with
            | None => Some ((b1, e1), [])
            | Some ((b2, e2), ts'') =>
                let 
                  t1 := if leb time b1 then b1 else time
                in let
                  t2 := if leb time b2 then b2 else time
                in
                  match t1 <?> t2 with
                      | Lt => Some ((b1, e1), (b2, e2) :: ts'')
                      | Gt => Some ((b2, e2), (b1, e1) :: ts'')
                      | Eq =>
                          if leb e1 e2
                          then Some ((b1, e1), (b2, e2) :: ts'')
                          else Some ((b2, e2), (b1, e1) :: ts'')
                  end
        end
end.

(* TODO
Fixpoint schedule_aux
  (time : nat) (ts : list Task) : option Schedule :=
match min time ts with
    | None => Some []
    | Some ((b1, e1), ts') =>
        let
          t1 := if leb time b1 then b1 else time
        in
          if leb (S t1) e1
          then
            match schedule_aux t1 ts' with
                | None => None
                | Some [] => Some [(t1, (b1, e1))]
                | Some ((t2, (b2, e2)) :: ts'') =>
                    if leb (S t1) t2
                    then Some ((t1, (b1, e1)) :: (t1, (b2, e2)) :: ts'')
                    else None
            end
          else None
end.

Definition schedule (ts : list Task) : option Schedule :=
  schedule_aux 0 (sort ts).

Definition test := [(1, 3); (2, 4); (1, 5); (1, 2)].

Compute schedule (take 3 test). 




Theorem schedule_correct :
  forall (A : Type) (ts : list Task),
    @schedule A ts = None ->
      ~ exists s : Schedule, CorrectSchedule s.
Abort.

Theorem schedule_correct :
  forall (A : Type) (ts : list Task) (s : Schedule),
    @schedule A ts = Some s -> CorrectSchedule s.
Abort.
*)