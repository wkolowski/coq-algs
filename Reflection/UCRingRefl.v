Require Import UCRing.

Set Implicit Arguments.

(* UCRing expressions. *)
Inductive exp (X : UCRing) : Type :=
    | Var : nat -> exp X
    | Zero : exp X
    | One : exp X
    | Add : exp X -> exp X -> exp X
    | Mul : exp X -> exp X -> exp X
    | Neg : exp X -> exp X.

Arguments Var [X] _.
Arguments Zero [X].
Arguments One [X].
Arguments Add [X] _ _.
Arguments Mul [X] _ _.
Arguments Neg [X] _.

Definition exp_eq_dec {X : UCRing} (e1 e2 : exp X) : {e1 = e2} + {e1 <> e2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint expDenote {X : UCRing} (env : nat -> X) (e : exp X) : X :=
match e with
    | Var n => env n
    | Zero => 0
    | One => 1
    | Add e1 e2 => expDenote env e1 + expDenote env e2
    | Mul e1 e2 => expDenote env e1 * expDenote env e2
    | Neg e' => - expDenote env e'
end.

Function simplifyExp {X : UCRing} (e : exp X) : exp X :=
match e with
    | Var n => Var n
    | Zero => Zero
    | One => One
    | Add e1 e2 =>
        match simplifyExp e1, simplifyExp e2 with
            | Zero, e2' => e2'
            | e1', Zero => e1'
            | e1', Neg e2' =>
                if exp_eq_dec e1' e2'
                then Zero
                else Add e1' (Neg e2')
            | e1', e2' => Add e1' e2'
        end
    | Mul e1 e2 =>
        match simplifyExp e1, simplifyExp e2 with
            | Zero, _ => Zero
            | _, Zero => Zero
            | One, e2' => e2'
            | e1', One => e1'
            | Neg One, e2' => Neg e2'
            | e1', Neg One => Neg e1'
            | Add e11 e12, e2' => Add (Mul e11 e2') (Mul e12 e2')
            | e1', Add e21 e22 => Add (Mul e1' e21) (Mul e1' e22)
            | Neg e1', Neg e2' => Mul e1' e2'
            | e1', Neg e2' => Mul (Neg e1') e2'
            | e1', e2' => Mul e1' e2'
        end
    | Neg e' =>
        match simplifyExp e' with
            | Zero => Zero 
            | Add e1 e2 => Add (Neg e1) (Neg e2)
            | Mul e1 e2 => Mul (Neg e1) e2
            | Neg e'' => e''
            | e'' => Neg e''
        end
end.

Theorem simplifyExp_correct :
  forall (X : UCRing) (env : nat -> X) (e : exp X),
    expDenote env (simplifyExp e) = expDenote env e.
Proof.
  intros X env e. revert env.
  Time functional induction simplifyExp e; cbn; trivial;
  repeat multimatch goal with
      | IH : forall _, _ |- _ => rewrite <- ?IH
      | H : ?a = ?b |- _ => rewrite ?H in *
      | _ => cbn; rng; autorewrite with lemmas
  end; clear y.
    rewrite <- neg_mul, (mul_comm _ (- expDenote env e2')).
    rewrite <- neg_mul. rewrite mul_comm. reflexivity.
Qed.

Function reassoc {X : UCRing} (e : exp X) : exp X :=
match e with
    | Add e1 e2 =>
        match reassoc e1 with
            | Add e11 e12 => Add e11 (Add e12 (reassoc e2))
            | e1' => Add e1' (reassoc e2)
        end
    | Mul e1 e2 =>
        match reassoc e1 with
            | Mul e11 e12 => Mul e11 (Mul e12 (reassoc e2))
            | e1' => Mul e1' (reassoc e2)
        end
    | Neg e' => Neg (reassoc e')
    | _ => e
end.

Theorem reassoc_correct :
  forall (X : UCRing) (envX : nat -> X) (e : exp X),
    expDenote envX (reassoc e) = expDenote envX e.
Proof.
  intros. functional induction reassoc e; cbn;
  try rewrite e3 in *; cbn in *; rewrite <- ?IHe0, ?IHe1; rng.
Qed.

Definition simplify {X : UCRing} (e : exp X) : exp X :=
  reassoc (simplifyExp e).

Lemma simplify_correct :
  forall (X : UCRing) (env : nat -> X) (e : exp X),
    expDenote env (simplify e) = expDenote env e.
Proof.
  unfold simplify; intros.
  rewrite reassoc_correct.
  rewrite !simplifyExp_correct.
  trivial.
Qed.

Theorem reflectExp :
  forall (X : UCRing) (env : nat -> X) (e1 e2 : exp X),
    expDenote env (simplify e1) = expDenote env (simplify e2) ->
      expDenote env e1 = expDenote env e2.
Proof.
  intros. rewrite !simplify_correct in H. assumption.
Qed.

(* Some wut proofs. *)
Inductive NoAdd {X : UCRing} : exp X -> Prop :=
    | NA_Var : forall n : nat, NoAdd (Var n)
    | NA_Zero : NoAdd Zero
    | NA_One : NoAdd One
    | NA_Mul : forall e1 e2 : exp X,
        NoAdd e1 -> NoAdd e2 -> NoAdd (Mul e1 e2)
    | NA_Neg : forall e : exp X, NoAdd e -> NoAdd (Neg e).

Inductive ANF {X : UCRing} : exp X -> Prop :=
    | ANF_Var : forall n : nat, ANF (Var n)
    | ANF_Zero : ANF Zero
    | ANF_One : ANF One
    | ANF_Add : forall e1 e2 : exp X,
        ANF e1 -> ANF e2 -> ANF (Add e1 e2)
    | ANF_Mul : forall e1 e2 : exp X,
        NoAdd e1 -> NoAdd e2 -> ANF e1 -> ANF e2 -> ANF (Mul e1 e2)
    | ANF_Neg : forall e : exp X, ANF e -> ANF (Neg e).

Hint Constructors NoAdd ANF.

Ltac inv H := try inversion H; subst; auto.

Ltac inv_NoAdd := repeat
match goal with
    | H : NoAdd (Add _ _) |- _ => inv H; clear H
    | H : NoAdd (Mul _ _) |- _ => inv H; clear H
    | H : NoAdd (Neg _) |- _ => inv H; clear H
end.

Theorem simplifyExp_pres_NoAdd :
  forall (X : UCRing) (e : exp X),
    NoAdd e -> NoAdd (simplifyExp e).
Proof.
  intros. Time functional induction simplifyExp e; try constructor;
  repeat match goal with
      | H : NoAdd ?x, IH : NoAdd ?x -> _ |- _ => specialize (IH H)
      | H : ?x = _, H' : NoAdd ?x |- _ => rewrite H in H'
      | _ => inv_NoAdd; eauto
  end.
Qed.

Ltac inv_ANF := repeat
match goal with
    | H : ANF (Add _ _) |- _ => inv H; clear H
    | H : ANF (Mul _ _) |- _ => inv H; clear H
    | H : ANF (Neg _) |- _ => inv H; clear H
end.

Theorem simplifyExp_NoAdd_ANF :
  forall (X : UCRing) (e : exp X),
    NoAdd e -> ANF (simplifyExp e).
Proof.
  intros. apply simplifyExp_pres_NoAdd in H.
  Time functional induction simplifyExp e; trivial;
  repeat match goal with
      | H : ?x = _, H' : context [ANF ?x] |- _ => rewrite H in H'
      | H : ?P, IH : ?P -> ?Q |- _ => specialize (IH H)
      | _ => inv_NoAdd; inv_ANF
  end;
  repeat match goal with
      | H : _ -> ?P |- _ => cut P; auto; clear H; intros
  end; inv_ANF.
Qed.

(* Simplification for equality hypotheses *)
Inductive eqExp (X : UCRing) : Type :=
    | E : forall e1 e2 : exp X, eqExp X.

Arguments E [X] _ _.

Definition eqExpDenote
  {X : UCRing} (env : nat -> X) (eq : eqExp X)
  : Prop :=
match eq with
    | E e1 e2 => expDenote env e1 = expDenote env e2
end.

(*Function simpHypEq {X : UCRing} (eq : eqExp X) : eqExp X :=
match eq with
    | E e1 e2 =>
        match simplify e1, simplify e2 with
            | Add e11 e12, Add e21 e22 =>
                if exp_eq_dec e11 e21
                then E e12 e22
                else if exp_eq_dec e12 e22
                     then E e11 e21
                     else E (Add e11 e12) (Add e21 e22)
            | Neg e1', Neg e2' => E e1' e2'
            | e1', e2' => E e1' e2'
        end
end.

Ltac forth :=
repeat match goal with
    | |- expDenote ?env ?e1 = expDenote ?env ?e2 =>
        is_var e1; is_var e2;
        rewrite <- (simplify_correct env e1),
                <- (simplify_correct env e2)
    | H : ?x = _ |- context [?x] => rewrite H; cbn
end; rng.

Ltac back :=
repeat match goal with
    | H : expDenote ?env ?e1 = expDenote ?env ?e2 |- _ =>
        is_var e1; is_var e2;
        rewrite <- (simplify_correct env e1),
                <- (simplify_correct env e2) in H
    | H : ?x = _ , H' : context [?x] |- _ =>
        rewrite H in H'; cbn in H'; auto
end; rng.

Lemma simpHypEq_correct :
  forall (X : UCRing) (env : nat -> X) (eq : eqExp X),
    eqExpDenote env (simpHypEq eq) <-> eqExpDenote env eq.
Proof.
  intros. functional induction simpHypEq eq; cbn; split; intros.
    all: try (forth; fail).
    all: try (back; eapply add_cancel_l + eapply add_cancel_r; eauto; fail).
    back. apply neg_eq. assumption.
Qed.*)

Fixpoint size {X : UCRing} (e : exp X) : nat :=
match e with
    | Add e1 e2 => 1 + size e1 + size e2
    | Mul e1 e2 => 1 + size e1 + size e2
    | Neg e' => 1 + size e'
    | _ => 1
end.

Definition pair_size {X : UCRing} (p : exp X * exp X) : nat :=
  size (fst p) + size (snd p).

Require Import Recdef.

Function simpHypEq' {X : UCRing} (p : exp X * exp X)
  {measure pair_size p} : exp X * exp X :=
match fst p, snd p with
    | Add e11 e12, Add e21 e22 =>
        if exp_eq_dec e11 e21
        then simpHypEq' (e12, e22)
        else if exp_eq_dec e12 e22
             then simpHypEq' (e11, e21)
             else (Add e11 e12, Add e21 e22)
    (*| Mul e11 e12, Add e21 e22 =>
        if exp_eq_dec e11 e21
        then simpHypEq' (e12, e22)
        else if exp_eq_dec e12 e22
             then simpHypEq' (e11, e21)
             else (Add e11 e12, Add e21 e22)*)
    | Neg e1', Neg e2' => simpHypEq' (e1', e2')
    | _, _ => p
end.
Proof.
  all: destruct p; cbn; intros; subst; cbn; omega.
Defined.

Theorem simpHypEq'_correct :
  forall (X : UCRing) (env : nat -> X) (p : exp X * exp X),
    eqExpDenote env (E (fst (simpHypEq' p)) (snd (simpHypEq' p))) <->
    eqExpDenote env (E (fst p) (snd p)).
Proof.
  intros. functional induction simpHypEq' X p; cbn in *;
  rewrite ?e, ?e0 in *; cbn in *; rewrite ?IHp0; split; rng.
    apply add_cancel_l in H. assumption.
    apply add_cancel_r in H. assumption.
  apply neg_eq. assumption.
Qed.

Definition simpHypEq {X : UCRing} (eq : eqExp X) : eqExp X :=
match eq with
    | E e1 e2 =>
        let '(e1', e2') := simpHypEq' (simplify e1, simplify e2)
        in E e1' e2'
end.

Lemma simpHypEq_correct :
  forall (X : UCRing) (env : nat -> X) (eq : eqExp X),
    eqExpDenote env (simpHypEq eq) <-> eqExpDenote env eq.
Proof.
  split; intros; destruct eq; cbn in *.
    pose (simpHypEq'_correct env (simplify e1, simplify e2)). cbn in i.
      case_eq (simpHypEq' (simplify e1, simplify e2)); intros.
      rewrite H0 in *; cbn in *. apply i in H.
      rewrite ?simplify_correct in H. assumption.
    pose (simpHypEq'_correct env (simplify e1, simplify e2)). cbn in i.
      case_eq (simpHypEq' (simplify e1, simplify e2)); intros; cbn.
      rewrite H0 in *; cbn in *. rewrite i.
      rewrite ?simplify_correct. assumption.
Qed.

(* Simplification for goal equalities. *)
Function simpGoalEq {X : UCRing} (eq : eqExp X) : eqExp X :=
match eq with
    | E e1 e2 => E (simplify e1) (simplify e2)
end.

Lemma simpGoalEq_correct :
  forall (X : UCRing) (env : nat -> X) (eq : eqExp X),
    eqExpDenote env (simpGoalEq eq) <-> eqExpDenote env eq.
Proof.
  intros. functional induction simpGoalEq eq; cbn; split; intros.
    rewrite ?simplify_correct in H. assumption.
    rewrite ?simplify_correct. assumption.
Qed.

(* Formulas. *)
Inductive formula (X : UCRing) : Type :=
    | fFalse : formula X
    | fTrue : formula X
    | fVar : Prop -> formula X
    | fEquiv : exp X -> exp X -> formula X
    | fNot : formula X -> formula X
    | fAnd : formula X -> formula X -> formula X
    | fOr : formula X -> formula X -> formula X
    | fImpl : formula X -> formula X -> formula X.

Arguments fFalse [X].
Arguments fTrue [X].
Arguments fVar [X] _.
Arguments fEquiv [X] _ _.
Arguments fNot [X] _.
Arguments fAnd [X] _ _.
Arguments fOr [X] _ _.
Arguments fImpl [X] _ _.

Fixpoint formulaDenote
  {X : UCRing} (env : nat -> X) (p : formula X) : Prop :=
match p with
    | fFalse => False
    | fTrue => True
    | fVar P => P
    | fEquiv e1 e2 => expDenote env e1 = expDenote env e2
    | fNot p' => ~ formulaDenote env p'
    | fAnd p1 p2 => formulaDenote env p1 /\ formulaDenote env p2
    | fOr p1 p2 => formulaDenote env p1 \/ formulaDenote env p2
    | fImpl p1 p2 => formulaDenote env p1 -> formulaDenote env p2
end.

Function simpFormula {X : UCRing} (f : formula X) : formula X :=
match f with
    | fFalse => fFalse
    | fTrue => fTrue
    | fVar P => fVar P
    | fEquiv e1 e2 =>
        match simpHypEq (E e1 e2) with
            | E e1' e2' => fEquiv e1' e2'
        end
    | fNot f' =>
        match simpFormula f' with
            | fFalse => fTrue
            | fTrue => fFalse
            | f'' => fNot f''
        end
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
        match f1 with
            | fEquiv e1 e2 =>
                let '(E e1' e2') := simpHypEq (E e1 e2) in
                  fImpl (fEquiv e1' e2') f2
            | f1' =>
                match simpFormula f1' with
                    | fFalse => fTrue
                    | fTrue => f2
                    | fAnd f11 f12 => fImpl f11 (fImpl f12 f2)
                    | fOr f11 f12 => fAnd (fImpl f11 f2) (fImpl f12 f2)
                    | f1' => fImpl f1' f2
                end
        end
end.

Theorem simpFormula_correct :
  forall (X : UCRing) (env : nat -> X) (f : formula X),
    formulaDenote env (simpFormula f) <-> formulaDenote env f.
Proof.
  intros. functional induction simpFormula f; cbn.
  Time all:
  repeat match goal with
      | env : nat -> _, IH : forall env' : nat -> _, _ |- _ =>
          specialize (IH env)
      | e : simpFormula ?f = _,
        IH : formulaDenote _ (simpFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
    assert (eqExpDenote env (simpHypEq (E e1 e2)) =
           (expDenote env e1' = expDenote env e2')).
      rewrite e0. cbn. trivial.
      rewrite <- H. rewrite simpHypEq_correct. cbn. reflexivity.
    assert (eqExpDenote env (simpHypEq (E e1 e2)) <->
            eqExpDenote env (E e1' e2')).
      rewrite e3. tauto.
      rewrite simpHypEq_correct in H. cbn in H. tauto.
Qed.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solveFormula
  {X : UCRing} (env : nat -> X) (f : formula X)
  : option (formulaDenote env f).
Proof.
  destruct f; cbn.
    apply None.
    apply Some. trivial.
    apply None.
      destruct (exp_eq_dec (simplify e) (simplify e0)).
        rewrite <- (simplify_correct env e),
                <- (simplify_correct env e0).
          rewrite e1. apply Some. trivial.
        apply None.
    apply None.
    destruct (solveFormula X env f1), (solveFormula X env f2).
      apply Some. split; assumption.
      1-3: apply None.
    destruct (solveFormula X env f1).
      apply Some. left. assumption.
      destruct (solveFormula X env f2).
        apply Some. right. assumption.
        apply None.
    destruct (solveFormula X env f2).
      apply Some. intro. assumption.
      apply None.
Defined.

Theorem solveFormula_correct :
  forall (X : UCRing) (env : nat -> X) (f : formula X),
    (exists p : formulaDenote env f, solveFormula env f = Some p) ->
      formulaDenote env f.
Proof.
  intros. destruct H. assumption.
Qed.

(* Basic tactics for manipulating lists. *)
Ltac functionalize l X :=
let rec loop n l' :=
    match l' with
        | [] => constr:(fun _ : nat => 0) (* Here 0 : X *)
        | ?h :: ?t =>
            let f := loop (S n) t in
            constr:(fun m : nat => if m =? n then h else f m)
    end
in loop 0%nat l.

(* Reification for expressions. *)
Ltac allVarsExp xs e :=
match e with
    | 0 => xs
    | 1 => xs
    | ?a + ?b =>
        let xs' := allVarsExp xs b in allVarsExp xs' a
    | ?a * ?b =>
        let xs' := allVarsExp xs b in allVarsExp xs' a
    | -?a => allVarsExp xs a
    | _ => addToList e xs
end.

Ltac reifyExp xs x :=
match x with
    | 0 => constr:(Zero)
    | 1 => constr:(One)
    | ?a + ?b =>
        let e1 := reifyExp xs a in
        let e2 := reifyExp xs b in constr:(Add e1 e2)
    | ?a * ?b =>
        let e1 := reifyExp xs a in
        let e2 := reifyExp xs b in constr:(Mul e1 e2)
    | -?a =>
        let e := reifyExp xs a in constr:(Neg e)
    | ?x =>
        let n := lookup x xs in constr:(Var n)
end.

(* Reification of equalities. *)
Ltac reifyEqv xs a b :=
  let e1 := reifyExp xs a in
  let e2 := reifyExp xs b in constr:(E e1 e2).

(* Reification of formulas. *)
Ltac allVarsFormula xs P :=
match P with
    | ?a = ?b =>
        let xs' := allVarsExp xs b in allVarsExp xs' a
    | ~ ?P' => allVarsFormula xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | _ => xs
end.

Ltac reifyFormula xs P :=
match P with
    | False => constr:(fFalse)
    | True => constr:(fTrue)
    | ?a = ?b =>
        let e1 := reifyExp xs a in
        let e2 := reifyExp xs b in constr:(fEquiv e1 e2)
    | ~ ?P' =>
        let e := reifyFormula xs P' in constr:(fNot e)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fImpl e1 e2)
    | _ => constr:(fVar P)
end.

(* Reflection for equalities in hypotheses and in the goal. *)
Ltac reflect_eq_hyps := repeat
match goal with
    | X : UCRing, H : ?a = ?b |- _ =>
        let xs := allVarsExp constr:(@nil X) b in
        let xs' := allVarsExp xs a in
        let env := functionalize xs' X in
        let H' := reifyEqv xs' a b in
          generalize dependent H;
          match goal with
              | |- _ -> ?P => change (eqExpDenote env H' -> P)
          end;
          let H'' := fresh "H" in intro H'';
          rewrite <- simpHypEq_correct in H''
end; cbn in *.

Ltac reflect_eq_goal := cbn; intros;
match goal with
    | X : UCRing |- ?a = ?b =>
        let xs := allVarsExp constr:(@nil X) b in
        let xs' := allVarsExp xs a in
        let env := functionalize xs' X in
        let H' := reifyEqv xs' a b in
          change (eqExpDenote env H'); apply reflectExp; cbn; try reflexivity
end.

(* Reflection for formulas. *)
Ltac reflectFormula :=
match goal with
    | X : UCRing |- ?P =>
        let xs := allVarsFormula constr:(@nil X) P in
        let env := functionalize xs X in
        let e := reifyFormula xs P in change (formulaDenote env e);
          rewrite <- simpFormula_correct
end.

Ltac ucring_subst := repeat
multimatch goal with
    | H : ?x = ?y |- _ => rewrite <- ?H in *
    | H : ?x = ?x |- _ => clear H
end; subst.

Ltac solve_goal' :=
  cbn; reflectFormula; apply solveFormula_correct; cbn; ucring_subst; eauto.

Ltac solve_goal :=
  try (solve_goal'; fail);
  fail "Cannot solve the goal".

Ltac ucring := intros; repeat reflect_eq_hyps; subst; reflect_eq_goal.

Section Test.

Variable X : UCRing.

Variables a a' b b' c c' d d' e e' : X.

(* Tests for expression simplifier. *)

(* UCRing axioms for [add]. *)
Goal a + (b + c) = (a + b) + c.
Proof. ucring. Qed.

Goal a + b = b + a.
Proof. ucring. rng. Abort.

Goal 0 + a = a.
Proof. ucring. Qed.

Goal a + 0 = a.
Proof. ucring. Qed.

(* UCRing axioms for [neg]. *)
Goal -a + a = 0.
Proof. ucring. rng. Qed.

Goal a + (-a) = 0.
Proof. ucring. Qed.

(* UCRing axioms for [mul]. *)
Goal a * (b * c) = (a * b) * c.
Proof. ucring. Qed.

Goal a * b = b * a.
Proof. ucring. rng. Abort.

Goal 1 * a = a.
Proof. ucring. Qed.

Goal a * 1 = a.
Proof. ucring. Qed.

(* Distributivity *)
Goal a * (b + c) = a * b + a * c.
Proof. ucring. Qed.

Goal (a + b) * c = a * c + b * c.
Proof. ucring. Qed.

(* Identities that aren't axioms. *)
Goal (a + a) - (a + a) = 0.
Proof. ucring.  (* TODO *) Abort.

(* --a = a *)
Goal --a = a.
Proof. ucring. Qed.

(* 0 * a = 0 *)
Goal 0 * a = 0.
Proof. ucring. Qed.

(* a * 0 = 0 *)
Goal a * 0 = 0.
Proof. ucring. Qed.

Goal b = b' -> a + (b + c) = (a + b') + c.
Proof. ucring. Qed.

(* Cancel left and right. *)
Goal a + b = a + b' -> b + c = b' + c.
Proof. ucring. Qed.

Goal a + b = a' + b -> a + c = a' + c.
Proof. ucring. Qed.

Goal -a = -b -> a + c = b + c.
Proof. ucring. Qed.

Goal (a + b) + c = a + (b' + c) -> b = b'.
Proof. ucring. Qed.

Goal False ->  a <> b -> a * a = b * b.
Proof. solve_goal. Qed.

Goal a = b -> b = c -> c = a -> a = c /\ c + c = b + b.
Proof.
  reflectFormula. cbn.
Abort.

Goal a = b \/ a = c -> a = c \/ a + a = b + b.
Proof.
  reflectFormula; cbn.
Abort.

Goal a = b -> c' = b' -> 2 = 2 \/ c * c = c + (a * c').
Proof.
  reflectFormula. cbn.
Abort.

End Test.