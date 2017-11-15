Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

(* Formulas. [not f] will be represented as [fImpl f fFalse] and
   [f1 <-> f2] as [fAnd (fImpl f1 f2) (fImpl f2 f1)]. *)
Inductive formula : Type :=
    | fFalse : formula
    | fTrue : formula
    | fVar : nat -> formula
    | fAnd : formula -> formula -> formula
    | fOr : formula -> formula -> formula
    | fImpl : formula -> formula -> formula.

Section lemmas.

Definition Env : Type := list Prop.

Definition holds (n : nat) (env : Env) : Prop := nth n env False.

Definition Proofs : Type := list nat.

Fixpoint allTrue (env : Env) (proofs : Proofs) : Prop :=
match proofs with
    | [] => True
    | h :: t => holds h env /\ allTrue env t
end.

Theorem find_spec :
  forall (n : nat) (env : Env) (proofs : Proofs),
    allTrue env proofs -> In n proofs -> holds n env.
Proof.
  induction proofs as [| h t]; cbn.
    inversion 2.
    do 2 destruct 1; subst.
      unfold holds in H. apply H.
      apply IHt; assumption.
Qed.

End lemmas.

Fixpoint formulaDenote (env : Env) (f : formula) : Prop :=
match f with
    | fFalse => False
    | fTrue => True
    | fVar i => holds i env
    | fAnd f1 f2 => formulaDenote env f1 /\ formulaDenote env f2
    | fOr f1 f2 => formulaDenote env f1 \/ formulaDenote env f2
    | fImpl f1 f2 => formulaDenote env f1 -> formulaDenote env f2
end.

Function simpFormula (f : formula) : formula :=
match f with
    | fFalse => fFalse
    | fTrue => fTrue
    | fVar P => fVar P
    | fAnd f1 f2 =>
        match simpFormula f1, simpFormula f2 with
            | fOr f11 f12, f2' => fOr (fAnd f11 f2') (fAnd f12 f2')
            | f1', fOr f21 f22 => fOr (fAnd f1' f21) (fAnd f1' f22)
            | fFalse, _ => fFalse
            | _, fFalse => fFalse
            | fTrue, f2' => f2'
            | f1', fTrue => f1'
            | f1', f2' => fAnd f1' f2'
        end
    | fOr f1 f2 =>
        match simpFormula f1, simpFormula f2 with
            | fAnd f11 f12, f2' => fAnd (fOr f11 f2') (fOr f12 f2')
            | f1', fAnd f21 f22 => fAnd (fOr f1' f21) (fOr f1' f22)
            | fFalse, f2' => f2'
            | f1', fFalse => f1'
            | fTrue, _ => fTrue
            | _, fTrue => fTrue
            | f1', f2' => fOr f1' f2'
        end
    | fImpl f1 f2 =>
        match simpFormula f1 with
            | fFalse => fTrue
            | fTrue => f2
            | fAnd f11 f12 => fImpl f11 (fImpl f12 f2)
            | fOr f11 f12 => fAnd (fImpl f11 f2) (fImpl f12 f2)
            | f1' => fImpl f1' f2
        end
end.

Theorem simpFormula_correct :
  forall (f : formula) (env : Env),
    formulaDenote env (simpFormula f) <-> formulaDenote env f.
Proof.
  intros. functional induction simpFormula f; cbn.
  Time all:
  repeat match goal with
      | env : nat -> _, IH : forall _ : nat -> _, _ |- _ =>
          specialize (IH)
      | e : simpFormula ?f = _,
        IH : formulaDenote _ (simpFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
Qed.

Inductive solution (P : Prop) : Type :=
    | Yes' : P -> solution P
    | No' : solution P.

Arguments Yes' [P] _.
Arguments No' [P].

Notation "'Yes'" := (Yes' _).
Notation "'No'" := No'.

Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x && y" := (if x then Reduce y else No).
Notation "x || y" := (if x then Yes else Reduce y).

Definition solveHypothesis (env : Env) :
  forall (proofs : Proofs) (hyp f : formula)
    (cont : forall proofs : Proofs,
      solution (allTrue env proofs -> formulaDenote env f)),
        solution (allTrue env proofs -> formulaDenote env hyp ->
          formulaDenote env f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (hyp f : formula)
      (cont : forall proofs : Proofs,
        solution (allTrue env proofs -> formulaDenote env f)) :
          solution (allTrue env proofs -> formulaDenote env hyp ->
            formulaDenote env f) :=
  match hyp with
      | fFalse => Yes
      | fTrue => Reduce (cont proofs)
      | fVar i => Reduce (cont (i :: proofs))
      | fAnd f1 f2 =>
          Reduce (solve proofs f1 (fImpl f2 f)
                        (fun proofs' => Reduce (cont proofs')))
      | fOr f1 f2 =>
          solve proofs f1 f cont &&
          solve proofs f2 f cont
      | _ => No
  end).
  all: cbn in *; try tauto.
Defined.

Definition solveGoal (env : Env)
  : forall (proofs : Proofs) (f : formula),
      solution (allTrue env proofs -> formulaDenote env f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (f : formula)
      : solution (allTrue env proofs -> formulaDenote env f) :=
  match f with
      | fFalse => No
      | fTrue => Yes
      | fVar i =>
          match in_dec Nat.eq_dec i proofs with
              | left _ => Yes
              | right _ => No
          end
      | fAnd f1 f2 => solve proofs f1 && solve proofs f2
      | fOr f1 f2 => solve proofs f1 || solve proofs f2
      | fImpl f1 f2 =>
          solveHypothesis env proofs f1 f2
            (fun proofs' => solve proofs' f2)
  end).
  all: cbn; try tauto.
    intro. apply find_spec with proofs; assumption.
Defined.

Definition solveFormula (env : Env) (f : formula)
  : solution (formulaDenote env f).
Proof.
  refine (Reduce (solveGoal env [] f)). apply f0. cbn. trivial.
Defined.

Theorem solveFormula_correct :
  forall (env : Env) (f : formula),
    (exists p : formulaDenote env f, solveFormula env f = Yes' p) ->
      formulaDenote env f.
Proof.
  intros. destruct H. assumption.
Qed.

(* Basic tactics for manipulating lists. *)
Ltac inList x l :=
match l with
    | [] => false
    | x :: _ => true
    | _ :: ?l' => inList x l'
end.

Ltac addToList x l :=
  let b := inList x l in
match b with
    | true => l
    | false => constr:(x :: l)
end.

Ltac lookup x l :=
match l with
    | x :: _ => constr:(0%nat)
    | _ :: ?l' => let n := lookup x l' in constr:(S n)
end.

Ltac allVarsFormula xs P :=
match P with
    | ~ ?P' => allVarsFormula xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | _ => addToList P xs
end.

Ltac reifyFormula xs P :=
match P with
    | False => constr:(fFalse)
    | True => constr:(fTrue)
    | ~ ?P' =>
        let e := reifyFormula xs P' in constr:(fImpl e fFalse)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fImpl e1 e2)
    | ?P1 <-> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in
          constr:(fAnd (fImpl e1 e2) (fImpl e2 e1))
    | _ =>
        let i := lookup P xs in constr:(fVar i)
end.

Definition unwrap {P : Prop} (s : solution P) :=
match s return if s then P else Prop with
    | Yes' p => p
    | _ => True
end.

Ltac reflectFormula :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in change (formulaDenote xs f);
          rewrite <- simpFormula_correct; cbn
end.

Ltac solveGoal' :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in change (formulaDenote xs f);
          rewrite <- simpFormula_correct; cbn;
          try apply (unwrap (solveFormula xs (simpFormula f)))
end.

Ltac solveGoal := solveGoal'; fail.

(* Tests for formula solver. *)
Section Test.

Variables A B C D E F G P Q R S : Prop.

(* [False] and [True]. *)
Goal False.
Proof.
  try solveGoal'.
Abort.

Goal True.
Proof. solveGoal'. Qed.

(* Negation. *)
Goal ~ True.
Proof. try solveGoal'. Abort.

Goal ~ False.
Proof. solveGoal'. Qed.

(* Conjunctions, disjunctions and implications of [True]s and [False]s. *)
Goal True /\ True.
Proof. solveGoal'. Qed.

Goal True /\ False.
Proof. try solveGoal'. Abort.

Goal False \/ True.
Proof. solveGoal'. Qed.

Goal False \/ P.
Proof. try solveGoal'. Abort.

Goal True -> True.
Proof. solveGoal'. Qed.

Goal False -> False.
Proof. solveGoal'. Qed.

(* More complex stuff. *)
Goal P \/ True.
Proof. solveGoal'. Qed.

Goal True -> P.
Proof. try solveGoal'. Abort.

Goal False -> P.
Proof. solveGoal'. Qed.

Goal P -> P.
Proof. solveGoal'. Qed.

Goal P -> P \/ Q.
Proof. solveGoal'. Abort.

Goal P \/ Q -> Q \/ P.
Proof. solveGoal'. Qed.

Goal P -> ~~P.
Proof.
  let xs := allVarsFormula constr:(@nil Prop) (P -> ~~P) in pose xs;
  let f := reifyFormula xs (P -> ~~P) in pose f;
    change (formulaDenote xs f);
    rewrite <- simpFormula_correct; cbn.
      Eval cbn in unwrap (solveFormula l (simpFormula f)).
Abort.

Goal P <-> P.
Proof.
  solveGoal'.
Qed.

(* Wzięte z R1.v *)

Theorem dezd : (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  match goal with
  | |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in pose xs;
        let f := reifyFormula xs P in pose f;
        change (formulaDenote xs f); 
          try apply (unwrap (solveFormula xs f))
(*; rewrite <- simpFormula_correct; cbn;*)
(*         apply (unwrap (solveFormula xs (simpFormula f)))*)
  end.
  rewrite <- simpFormula_correct. cbn.
Abort.

(* Przemienność *)
Theorem and_comm : P /\ Q -> Q /\ P.
Proof. solveGoal'. Qed.

Theorem or_comm : P \/ Q -> Q \/ P.
Proof. solveGoal'. Qed.

Theorem and_assoc : P /\ (Q /\ R) <-> (P /\ Q) /\ R.
Proof. solveGoal'. Abort.

Theorem or_assoc : P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof. solveGoal'. Qed.

(* Rozdzielność *)
Ltac gen x := generalize dependent x.

Theorem and_dist_or : P /\ (Q \/ R) <-> (P /\ Q) \/ (P /\ R).
Proof.
  repeat (split; solveGoal'); gen H; gen H0; solveGoal'.
Abort.

Theorem or_dist_and : P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. solveGoal'. Abort.

Theorem imp_dist_imp : (P -> Q -> R) <-> ((P -> Q) -> (P -> R)).
Proof. solveGoal'. Abort.

(* Kuryfikacja *)
Theorem curry : (P /\ Q -> R) -> (P -> Q -> R).
Proof. solveGoal'. Abort.

Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).
Proof. solveGoal'. Abort.

(* De Morgan *)
Theorem deMorgan_1 : ~(P \/ Q) <-> ~P /\ ~Q.
Proof. solveGoal'. Abort.

Theorem deMorgan_2 : ~P \/ ~Q -> ~(P /\ Q).
Proof. solveGoal'. Abort.

(* Niesprzeczność i zasada wyłączonego środka *)
Theorem noncontradiction' : ~(P /\ ~P).
Proof. solveGoal'. Abort.

Theorem noncontradiction_v2 : ~(P <-> ~P).
Proof. solveGoal'. Abort.

Theorem em_irrefutable : ~~(P \/ ~P).
Proof. solveGoal'. Abort.

(* Elementy neutralne i anihilujące *)
Theorem and_false_annihilation : P /\ False <-> False.
Proof. solveGoal'. Qed.

Theorem or_false_neutral : P \/ False <-> P.
Proof. solveGoal'. Qed.

Theorem and_true_neutral : P /\ True <-> P.
Proof. solveGoal'. Qed.

Theorem or_true_annihilation : P \/ True <-> True.
Proof. solveGoal'. Qed.

(* Różne *)
Theorem or_imp_and : (P \/ Q -> R) <-> (P -> R) /\ (Q -> R).
Proof. solveGoal'. Abort.

Theorem and_not_imp : P /\ ~Q -> ~(P -> Q).
Proof. solveGoal'. Abort.

Theorem or_not_imp : ~P \/ Q -> (P -> Q).
Proof. solveGoal'. Abort.

Theorem contraposition : (P -> Q) -> (~Q -> ~P).
Proof. solveGoal'. Abort.

Theorem absurd : ~P -> P -> Q.
Proof. solveGoal'. Abort.

Theorem impl_and : (P -> Q /\ R) -> ((P -> Q) /\ (P -> R)).
Proof. solveGoal'. Abort.

End Test.