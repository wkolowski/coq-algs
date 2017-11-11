Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.
Require Import Permutation.
Require Import Perm.
Require Import InsertionSort.

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Class CMon : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    neutr : carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z;
    neutr_l : forall x : carrier, op neutr x = x;
    neutr_r : forall x : carrier, op x neutr = x;
    comm : forall x y : carrier, op x y = op y x
}.

Coercion carrier : CMon >-> Sortclass.

Inductive exp (X : CMon) : Type :=
    | Id : exp X
    | Var : nat -> exp X
    | Op : exp X -> exp X -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.

Fixpoint expDenote {X : CMon} (env : nat -> X) (e : exp X) : X :=
match e with
    | Id => neutr
    | Var n => env n
    | Op e1 e2 => op (expDenote env e1) (expDenote env e2)
end.

Fixpoint simplifyExp {X : CMon} (e : exp X) : exp X :=
match e with
    | Id => Id
    | Var v => Var v
    | Op e1 e2 =>
        match simplifyExp e1, simplifyExp e2 with
            | Id, e2' => e2'
            | e1', Id => e1'
            | e1', e2' => Op e1' e2'
        end
end.

Theorem simplifyExp_correct :
  forall (X : CMon) (env : nat -> X) (e : exp X),
    expDenote env (simplifyExp e) = expDenote env e.
Proof.
  induction e; cbn.
    reflexivity.
    reflexivity.
    destruct (simplifyExp e1), (simplifyExp e2); cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, ?neutr_l, ?neutr_r; try reflexivity.
Qed.

Fixpoint expDenoteL {X : CMon} (env : nat -> X) (l : list nat) : X :=
match l with
    | [] => neutr
    | h :: t => op (env h) (expDenoteL env t)
end.

Lemma expDenoteL_app :
  forall (X : CMon) (env : nat -> X) (l1 l2 : list nat),
    expDenoteL env (l1 ++ l2) = op (expDenoteL env l1) (expDenoteL env l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Fixpoint flatten {X : CMon} (e : exp X) : list nat :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
end.

Theorem flatten_correct :
  forall (X : CMon) (env : nat -> X) (e : exp X),
    expDenoteL env (flatten e) = expDenote env e.
Proof.
  induction e; simpl.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app. rewrite IHe1, IHe2. reflexivity.
Qed.

Lemma expDenoteL_Permutation :
  forall (X : CMon) (env : nat -> X) (l1 l2 : list nat),
    Permutation l1 l2 -> expDenoteL env l1 = expDenoteL env l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    rewrite !assoc. rewrite (comm (env y)). reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Theorem sort_correct :
  forall (X : CMon) (env : nat -> X) (l : list nat) (s : Sort),
    expDenoteL env (s natle l) = expDenoteL env l.
Proof.
  intros. apply expDenoteL_Permutation. apply (perm_Permutation natle).
  rewrite <- sort_perm. reflexivity.
Qed.

Definition simplify {X : CMon} (e : exp X) : list nat :=
  insertionSort natle (flatten (simplifyExp e)).

Theorem simplify_correct :
  forall (X : CMon) (env : nat -> X) (e1 e2 : exp X),
    expDenoteL env (simplify e1) = expDenoteL env (simplify e2) ->
      expDenote env e1 = expDenote env e2.
Proof.
  unfold simplify. intros.
  rewrite !(sort_correct X env _ Sort_insertionSort) in H.
  rewrite !flatten_correct, !simplifyExp_correct in H.
  assumption.
Qed.

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
    | x :: _ => constr:(0)
    | _ :: ?l' => let n := lookup x l' in constr:(S n)
end.

Ltac allVars xs e :=
match e with
    | op ?e1 ?e2 =>
        let xs' := allVars xs e2 in allVars xs' e1
    | ?f ?e' => allVars xs e'
    | _ => addToList e xs
end.

Ltac reifyTerm env x :=
match x with
    | neutr => constr:(Id)
    | op ?a ?b =>
        let e1 := reifyTerm env a in
        let e2 := reifyTerm env b in constr:(Op e1 e2)
    | _ =>
        let n := lookup x env in constr:(Var n)
end.

Ltac functionalize l X :=
let rec loop n l' :=
    match l' with
        | [] => constr:(fun _ : nat => @neutr X)
        | ?h :: ?t =>
            let f := loop (S n) t in
            constr:(fun m : nat => if m =? n then h else f m)
    end
in loop 0 l.

Ltac reify X :=
match goal with
    | |- ?e1 = ?e2 =>
        let xs := allVars constr:(@nil X) e1 in
        let xs' := allVars xs e2 in
        let r1 := reifyTerm xs' e1 in
        let r2 := reifyTerm xs' e2 in
        let env := functionalize xs' X in
        change (expDenote env r1 = expDenote env r2)
end.

Ltac reifyEqv X env a b :=
    let e1 := reifyTerm env a in
    let e2 := reifyTerm env b in constr:((e1, e2)).

(* TODO : improve reflection *)
Theorem flat_reflect_goal :
  forall (X : CMon) (env : nat -> X) (e1 e2 : exp X),
    flatten (simplifyExp e1) = flatten (simplifyExp e2) ->
      expDenote env e1 = expDenote env e2.
Proof.
  intros. apply simplify_correct. unfold simplify. rewrite H. reflexivity.
Qed.

Theorem flat_reflect_hyp' :
  forall (X : CMon) (env : nat -> X) (e1 e2 : exp X) (s : Sort),
    expDenote env e1 = expDenote env e2 ->
      expDenoteL env (s natle (flatten (simplifyExp e1))) =
      expDenoteL env (s natle (flatten (simplifyExp e2))).
Proof.
  intros.
  rewrite !sort_correct, !flatten_correct, !simplifyExp_correct.
  assumption.
Qed.

Ltac cmon_subst := repeat
multimatch goal with
    | H : ?x = ?y |- _ => rewrite <- ?H in *
    | H : ?x = ?x |- _ => clear H
end.

Ltac reflect_cmon' := cbn; intros; cmon_subst;
match goal with
    | X : CMon |- ?e1 = ?e2 =>
        reify X; apply simplify_correct; cbn; rewrite ?neutr_l, ?neutr_r
end.

Ltac reflect_cmon := reflect_cmon'; try reflexivity.

Ltac reflect_goal := simpl; intros;
match goal with
    | X : CMon |- ?e1 = ?e2 =>
        reify X; apply flat_reflect_goal
end.

Goal forall (X : CMon) (a b c : X),
  op a (op b c) = op (op a b) c.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : CMon) (a b : X),
  op a b = op b a.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : CMon) (a b b' c : X),
  b = b' -> op a (op b c) = op (op a b') c.
Proof.
  reflect_cmon'. reflexivity.
Qed.

Goal forall (X : CMon) (a a' b b' c c' : X),
  op a b = op a b' -> op (op a b) c = op b' (op a c).
Proof.
  reflect_cmon'. rewrite ?assoc. rewrite (comm b').
  rewrite !H. reflect_cmon'. reflexivity.
Qed.

Goal forall (X : CMon) (a a' b b' c c' : X),
  a = b -> b = c -> c = a -> op b (op a c) = op a (op neutr (op b c)).
Proof.
  reflect_cmon'. reflexivity.
Qed.

Inductive formula (X : CMon) : Type :=
    | fVar : Prop -> formula X
    | fEquiv : exp X -> exp X -> formula X
    | fNot : formula X -> formula X
    | fAnd : formula X -> formula X -> formula X
    | fOr : formula X -> formula X -> formula X
    | fImpl : formula X -> formula X -> formula X.

Fixpoint formulaDenote {X : CMon} (env : nat -> X) (p : formula X)
  : Prop :=
match p with
    | fVar P => P
    | fEquiv e1 e2 => expDenote env e1 = expDenote env e2
    | fNot p' => ~ formulaDenote env p'
    | fAnd p1 p2 => formulaDenote env p1 /\ formulaDenote env p2
    | fOr p1 p2 => formulaDenote env p1 \/ formulaDenote env p2
    | fImpl p1 p2 => formulaDenote env p1 -> formulaDenote env p2
end.

Ltac allVarsFormula xs P :=
match P with
    | ?a = ?b => allVars xs P
    | ~ ?P' => allVarsFormula xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | _ => xs
end.

Ltac reifyFormula X xs P :=
match P with
    | ~ ?P' =>
        let e := reifyFormula X xs P' in constr:(fNot e)
    | ?a = ?b =>
        let e1 := reifyTerm xs a in
        let e2 := reifyTerm xs b in constr:(fEquiv e1 e2)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fImpl e1 e2)
    | _ => constr:(fVar X P)
end.

Ltac reifyGoal :=
match goal with
    | X : CMon |- ?P =>
        let xs := allVarsFormula constr:(@nil X) P in
        let env := functionalize xs X in
        let e := reifyFormula X xs P in change (formulaDenote env e)
end.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solveFormula {X : CMon} (env : nat -> X) (f : formula X)
  : option (formulaDenote env f).
Proof.
  destruct f; cbn.
    apply None.
    destruct (list_eq
              (insertionSort natle (flatten (simplifyExp e)))
              (insertionSort natle (flatten (simplifyExp e0)))).
      apply Some. apply simplify_correct. f_equal. assumption.
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

Theorem solveFormula_spec :
  forall (X : CMon) (env : nat -> X) (f : formula X),
    (exists p : formulaDenote env f, solveFormula env f = Some p) ->
      formulaDenote env f.
Proof.
  intros. destruct H. assumption.
Qed.

Ltac solve_goal' :=
  cbn; intros; cmon_subst; reifyGoal;
  apply solveFormula_spec; cbn; eauto.

Ltac solve_goal :=
  try (solve_goal'; fail);
  fail "Cannot solve the goal".

Goal forall (X : CMon) (a a' b b' c c' : X),
  a = b -> b = c -> c = a -> a = c /\ op c c = op b b.
Proof.
  solve_goal.
Qed.

Goal forall (X : CMon) (a a' b b' c c' : X),
  a = b -> b' = c' -> 2 = 2 \/ op c c = op c (op a c').
Proof.
  Require Import Quote.
  intros X a _ b b' c c'.
  match goal with
      | X : CMon |- ?P =>
          let xs := allVarsFormula constr:(@nil X) P in
          let env := functionalize xs X in
          let f := fresh "f" in
          let f' := constr:(@formulaDenote X env) in pose f' as f
  end; cbn in *.
  Print formulaDenote. Print Assumptions simplify_correct.
Abort.