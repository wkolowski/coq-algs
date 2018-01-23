Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export CMon.
Require Export Sorting.InsertionSort.
Require Export Sorting.SortSpec.

Set Implicit Arguments.

Inductive exp (X : CMon) : Type :=
    | Id : exp X
    | Var : nat -> exp X
    | Op : exp X -> exp X -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.

Require Import HSLib.Base.

Fixpoint expDenote {X : CMon} (envX : Env X) (e : exp X) : X -> X :=
match e with
    | Id => id
    | Var n => fun x => op (nth n envX neutr) x
    | Op e1 e2 => expDenote envX e1 .> expDenote envX e2
end.

Definition reify {X : CMon} (f : X -> X) : X := f neutr.

Section test.

Variables
  (X : CMon)
  (a b c : X).

Goal True.
Proof.
  let x := constr:(expDenote[] (Op (Op Id (Var 1)) (Op (Var 2) (Var 3))))
  in pose x.
  cbn in c0. unfold compose in c0.
  let x := constr:(reify c0) in pose x.
  unfold c0, reify in c1. cbn in c1.
Abort.

End test.

(*
Fixpoint flatten {X : CMon} (e : exp X) : list nat :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
end.

Theorem flatten_correct :
  forall (X : CMon) (envX : Env X) (e : exp X),
    expDenoteL envX (flatten e) = expDenote envX e.
Proof.
  induction e; simpl.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app. rewrite IHe1, IHe2. reflexivity.
Qed.

Function list_to_exp {X : CMon} (l : list nat) : exp X :=
match l with
    | [] => Id
    | [x] => Var x
    | h :: t => Op (Var h) (list_to_exp t)
end.

Theorem list_to_exp_correct :
  forall (X : CMon) (envX : Env X) (l : list nat),
    expDenote envX (list_to_exp l) = expDenoteL envX l.
Proof.
  intros. functional induction list_to_exp l; cbn.
    trivial.
    rewrite neutr_r. trivial.
    rewrite IHe. trivial.
Qed.

Theorem flatten_lte :
  forall (X : CMon) (l : list nat),
    flatten (list_to_exp l) = l.
Proof.
  intros. functional induction list_to_exp l; cbn;
  rewrite ?IHe; trivial.
Qed.

Theorem flatten_idempotent :
  forall (X : CMon) (e : exp X),
    flatten (list_to_exp (flatten e)) = flatten e.
Proof.
  intros. rewrite flatten_lte. trivial.
Qed.

Theorem sort_correct :
  forall (X : CMon) (envX : Env X) (l : list nat) (s : Sort),
    expDenoteL envX (s natle l) = expDenoteL envX l.
Proof.
  intros. apply expDenoteL_Permutation. apply (perm_Permutation natle).
  rewrite <- sort_perm. reflexivity.
Qed.

Definition simplify {X : CMon} (e : exp X) : exp X :=
  list_to_exp (insertionSort natle (flatten e)).

Theorem simplify_correct :
  forall (X : CMon) (envX : Env X) (e : exp X),
    expDenote envX (simplify e) = expDenote envX e.
Proof.
  unfold simplify. intros.
  rewrite !list_to_exp_correct.
  rewrite !(sort_correct _ _ _ Sort_insertionSort).
  erewrite ?flatten_correct.
  trivial.
Qed.

Theorem simplify_idempotent :
  forall (X : CMon) (e : exp X),
    simplify (simplify e) = simplify e.
Proof.
  intros. unfold simplify.
  rewrite ?flatten_lte.
  rewrite (sort_idempotent natle (Sort_insertionSort)).
  cbn. trivial.
Qed.

Theorem reflectEq :
  forall (X : CMon) (envX : Env X) (e1 e2 : exp X),
    expDenote envX (simplify e1) = expDenote envX (simplify e2) ->
      expDenote envX e1 = expDenote envX e2.
Proof.
  intros. rewrite !simplify_correct in H. assumption.
Qed.

Ltac allVarsExp xs e :=
match e with
    | op ?e1 ?e2 =>
        let xs' := allVarsExp xs e2 in allVarsExp xs' e1
    | _ => addToList e xs
end.

Ltac reifyExp envX x :=
match x with
    | neutr => constr:(Id)
    | op ?a ?b =>
        let e1 := reifyExp envX a in
        let e2 := reifyExp envX b in constr:(Op e1 e2)
    | _ =>
        let n := lookup x envX in constr:(Var n)
end.

Ltac reifyEq envX a b :=
    let e1 := reifyExp envX a in
    let e2 := reifyExp envX b in
      constr:(expDenote envX e1 = expDenote envX e2).

Ltac cmon_simpl' := cbn; intros;
match goal with
    | X : CMon |- ?a = ?b =>
        let xs := allVarsExp constr:(@nil X) b in
        let xs' := allVarsExp xs a in
        let e := reifyEq xs' a b in
          change e; apply reflectEq; cbn;
          rewrite ?neutr_l, ?neutr_r
end.

Ltac cmon_simpl := subst; cmon_simpl'.

Ltac cmon := cmon_simpl; reflexivity.

(* Formulas. [not f] will be represented as [fImpl f fFalse] and
   [f1 <-> f2] as [fAnd (fImpl f1 f2) (fImpl f2 f1)]. *)
Inductive formula (X : CMon) : Type :=
    | fFalse : formula X
    | fTrue : formula X
    | fEq : exp X -> exp X -> formula X
    | fVar : nat -> formula X
    | fAnd : formula X -> formula X -> formula X
    | fOr : formula X -> formula X -> formula X
    | fImpl : formula X -> formula X -> formula X.

Arguments fFalse [X].
Arguments fTrue [X].
Arguments fEq [X] _ _.
Arguments fVar [X] _.
Arguments fAnd [X] _ _.
Arguments fOr [X] _ _.
Arguments fImpl [X] _ _.

Fixpoint formulaDenote
  {X : CMon} (envX : Env X) (envP : Env Prop) (f : formula X) : Prop :=
match f with
    | fFalse => False
    | fTrue => True
    | fVar i => holds i envP
    | fEq e1 e2 => expDenote envX e1 = expDenote envX e2
    | fAnd f1 f2 => formulaDenote envX envP f1 /\ formulaDenote envX envP f2
    | fOr f1 f2 => formulaDenote envX envP f1 \/ formulaDenote envX envP f2
    | fImpl f1 f2 => formulaDenote envX envP f1 -> formulaDenote envX envP f2
end.

Function subst {X : CMon} (e1 : exp X) (n : nat) (e2 : exp X) : exp X :=
match e1 with
    | Id => Id
    | Var m => if Nat.eq_dec n m then e2 else Var m
    | Op e11 e12 => Op (subst e11 n e2) (subst e12 n e2)
end.

Theorem subst_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (e1 e2 : exp X)
  (i : nat),
    formulaDenote envX envP (fEq (Var i) e2) ->
      expDenote envX (subst e1 i e2) = expDenote envX e1.
Proof.
  intros. functional induction subst e1 i e2; cbn in *;
  try rewrite IHe, IHe0; congruence.
Qed.

Theorem subst_idempotent :
  forall (X : CMon) (envX : Env X) (e1 e2 : exp X) (i : nat),
    nth i envX neutr = expDenote envX e2 ->
      subst (subst e1 i e2) i e2 = subst e1 i e2.
Proof.
  intros. functional induction subst e1 i e2; cbn.
    trivial.
    Focus 2. rewrite e0. trivial.
    Focus 2. erewrite IHe0, IHe; eauto.
    gen e2. induction e2; intros; cbn in *.
      trivial.
      destruct (Nat.eq_dec n n0); trivial.
Abort.

Function substF {X : CMon} (f : formula X) (i : nat) (e : exp X)
  : formula X :=
match f with
    | fEq e1 e2 => fEq (subst e1 i e) (subst e2 i e)
    | fAnd f1 f2 => fAnd (substF f1 i e) (substF f2 i e)
    | fOr f1 f2 => fOr (substF f1 i e) (substF f2 i e)
    | fImpl f1 f2 => fImpl (substF f1 i e) (substF f2 i e)
    | _ => f
end.

Theorem substF_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (f : formula X)
  (i : nat) (e : exp X),
    nth i envX neutr = expDenote envX e ->
    (formulaDenote envX envP (substF f i e) <-> 
      formulaDenote envX envP f).
Proof.
  intros. functional induction substF f i e; cbn in *.
    rewrite !(@subst_correct _ envX envP); cbn; firstorder.
    all: firstorder.
Qed.

Function simplifyEq {X : CMon} (f : formula X) : formula X :=
match f with
    | fEq e1 e2 => fEq (simplify e1) (simplify e2)
    | fAnd f1 f2 => fAnd (simplifyEq f1) (simplifyEq f2)
    | fOr f1 f2 => fOr (simplifyEq f1) (simplifyEq f2)
    | fImpl f1 f2 =>
        let f2' := simplifyEq f2 in
        match simplifyEq f1 with
            | fEq (Var i) e as f1' => fImpl f1' (substF f2' i e)
            | f1' => fImpl f1' f2'
        end
    | _ => f
end.

Theorem simplifyEq_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (f : formula X),
    formulaDenote envX envP (simplifyEq f) <->
    formulaDenote envX envP f.
Proof.
  intros. functional induction simplifyEq f; cbn in *;
  rewrite ?simplify_correct;
  repeat multimatch goal with
      | H : forall _, _ <-> _ |- _ => rewrite ?H
  end; try tauto.
    split; intros.
      rewrite <- IHf0. rewrite substF_correct in H.
        apply H. rewrite e1 in IHf1. cbn in IHf1. rewrite IHf1. assumption.
        rewrite <- IHf1 in H0. rewrite e1 in H0. cbn in H0. assumption.
    rewrite substF_correct.
      rewrite IHf0. apply H. rewrite <- IHf1, e1. cbn. assumption.
      assumption.
Qed.

(* TODO *)
Fixpoint size {X : CMon} (f : formula X) : nat :=
match f with
    | fFalse => 1
    | fTrue => 1
    | fEq _ _ => 1
    | fVar _ => 1
    | fAnd f1 f2 => size f1 + size f2
    | fOr f1 f2 => size f1 + size f2
    | fImpl f1 f2 => size f1 + size f2
end.

Lemma size_gt_0 :
  forall (X : CMon) (f : formula X), 0 < size f.
Proof.
  induction f; cbn; omega.
Qed.

Lemma size_substF :
  forall (X : CMon) (f : formula X) (i : nat) (e : exp X),
    size (substF f i e) = size f.
Proof.
  intros. functional induction substF f i e; cbn; omega.
Qed.

Hint Resolve size_gt_0.

(*Function simplifyEq' {X : CMon} (f : formula X) {measure size f}
  : formula X :=
match f with
    | fEq e1 e2 => fEq (simplify e1) (simplify e2)
    | fAnd f1 f2 => fAnd (simplifyEq' f1) (simplifyEq' f2)
    | fOr f1 f2 => fOr (simplifyEq' f1) (simplifyEq' f2)
    | fImpl f1 f2 =>
        match simplifyEq f1 with
            | fEq (Var i) e as f1' => fImpl f1' (simplifyEq' (substF f2 i e))
            | f1' => fImpl f1' (simplifyEq' f2)
        end
    | _ => f
end.
Proof.
  all: cbn; intros;
  repeat multimatch goal with
      | f : formula _ |- _ =>
          match goal with
              | H : 0 < size f |- _ => idtac
              | _ => pose (size_gt_0 f)
          end
  end; try omega.
    rewrite size_substF. omega.
Defined.

Theorem simplifyEq'_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (f : formula X),
    formulaDenote envX envP (simplifyEq' f) <->
    formulaDenote envX envP f.
Proof.
  intros. functional induction @simplifyEq' X f; cbn in *;
  rewrite ?simplify_correct;
  repeat multimatch goal with
      | H : forall _, _ <-> _ |- _ => rewrite ?H
  end; try tauto.
    split; intros.
      rewrite e1 in H.
      rewrite substF_correct in H.
        apply H.
Qed.
  *)

Function simplifyLogic {X : CMon} (f : formula X) : formula X :=
match f with
    | fAnd f1 f2 =>
        match simplifyLogic f1, simplifyLogic f2 with
            | fOr f11 f12, f2' => fOr (fAnd f11 f2') (fAnd f12 f2')
            | f1', fOr f21 f22 => fOr (fAnd f1' f21) (fAnd f1' f22)
            | fFalse, _ => fFalse
            | _, fFalse => fFalse
            | fTrue, f2' => f2'
            | f1', fTrue => f1'
            | f1', f2' => fAnd f1' f2'
        end
    | fOr f1 f2 =>
        match simplifyLogic f1, simplifyLogic f2 with
            | fAnd f11 f12, f2' => fAnd (fOr f11 f2') (fOr f12 f2')
            | f1', fAnd f21 f22 => fAnd (fOr f1' f21) (fOr f1' f22)
            | fFalse, f2' => f2'
            | f1', fFalse => f1'
            | fTrue, _ => fTrue
            | _, fTrue => fTrue
            | f1', f2' => fOr f1' f2'
        end
    | fImpl f1 f2 =>
        let f2' := simplifyLogic f2 in
        match simplifyLogic f1 with
            | fFalse => fTrue
            | fTrue => f2'
            | fAnd f11 f12 => fImpl f11 (fImpl f12 f2')
            | fOr f11 f12 => fAnd (fImpl f11 f2') (fImpl f12 f2')
            | f1' => fImpl f1' f2'
        end
    | _ => f
end.

Theorem simplifyLogic_correct :
  forall (X : CMon) (f : formula X) (envX : Env X) (envP : Env Prop),
    formulaDenote envX envP (simplifyLogic f) <-> formulaDenote envX envP f.
Proof.
  intros. functional induction simplifyLogic f; cbn.
  Time all:
  repeat match goal with
      | envX : Env _, IH : forall _ : Env _, _ |- _ => specialize (IH envX)
      | e : simplifyLogic ?f = _,
        IH : formulaDenote _ _ (simplifyLogic ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
Qed.

Definition simplifyFormula {X : CMon} (f : formula X) : formula X :=
  simplifyLogic (simplifyEq f).

Theorem simplifyFormula_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (f : formula X),
    formulaDenote envX envP (simplifyFormula f) <->
    formulaDenote envX envP f.
Proof.
  intros. unfold simplifyFormula.
  rewrite simplifyLogic_correct, simplifyEq_correct.
  reflexivity.
Qed.

Definition solveEq
  {X : CMon} (envX : Env X) (envP : Env Prop)
    : forall e1 e2 : exp X, solution (formulaDenote envX envP (fEq e1 e2)).
Proof.
  refine (
  fix solve (e1 e2 : exp X)
    : solution (formulaDenote envX envP (fEq e1 e2)) :=
  match e1, e2 with
      | Id, Id => Yes
      | Var n, Var m => if Nat.eq_dec n m then Yes else No
      | Op e11 e12, Op e21 e22 => solve e11 e21 && solve e12 e22
      | _, _ => No
  end);
  cbn in *; congruence.
Defined.

Definition solveHypothesis {X : CMon} (envX : Env X) (envP : Env Prop) :
  forall (proofs : Proofs) (hyp f : formula X)
    (cont : forall proofs : Proofs,
      solution (allTrue envP proofs -> formulaDenote envX envP f)),
        solution (allTrue envP proofs -> formulaDenote envX envP hyp ->
          formulaDenote envX envP f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (hyp f : formula X)
      (cont : forall proofs : Proofs,
        solution (allTrue envP proofs -> formulaDenote envX envP f)) :
          solution (allTrue envP proofs -> formulaDenote envX envP hyp ->
            formulaDenote envX envP f) :=
  match hyp with
      | fFalse => Yes
      | fTrue => Reduce (cont proofs)
      | fVar i => Reduce (cont (i :: proofs))
      (*| fEq (Var i) e => Reduce (cont proofs)*)
      | fEq _ _ => Reduce (cont proofs)
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

Definition solveGoal {X : CMon} (envX : Env X) (envP : Env Prop)
  : forall (proofs : Proofs) (f : formula X),
      solution (allTrue envP proofs -> formulaDenote envX envP f).
Proof.
  refine (
  fix solve
    (proofs : Proofs) (f : formula X)
      : solution (allTrue envP proofs -> formulaDenote envX envP f) :=
  match f with
      | fFalse => No
      | fTrue => Yes
      | fVar i =>
          match in_dec Nat.eq_dec i proofs with
              | left _ => Yes
              | right _ => No
          end
      | fEq e1 e2 => Reduce (solveEq envX envP e1 e2)
      | fAnd f1 f2 => solve proofs f1 && solve proofs f2
      | fOr f1 f2 => solve proofs f1 || solve proofs f2
      | fImpl f1 f2 =>
          solveHypothesis envX envP proofs f1 f2
            (fun proofs' => solve proofs' f2)
  end).
  all: cbn; try tauto.
    intro. apply find_spec with proofs; assumption.
Defined.

Definition solveFormula
  {X : CMon} (envX : Env X) (envP : Env Prop) (f : formula X)
    : solution (formulaDenote envX envP f).
Proof.
(*  refine (Reduce (solveGoal envX envP [] (simplifyFormula f))).*)
  refine (Reduce (solveGoal envX envP [] f)).
  (*rewrite <- simplifyFormula_correct.*)
  apply f0. cbn. trivial.
Defined.

Theorem solveFormula_correct :
  forall (X : CMon) (envX : Env X) (envP : Env Prop) (f : formula X),
    (exists p : formulaDenote envX envP f,
      solveFormula envX envP f = Yes' p) ->
        formulaDenote envX envP f.
Proof.
  intros. destruct H. assumption.
Qed.

Ltac allVarsX xs P :=
match P with
    | False => xs
    | True => xs
    | ?a = ?b =>
        let xs' := allVarsExp xs b in allVarsExp xs' a
    | ~ ?P' => allVarsX xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsX xs P2 in allVarsX xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsX xs P2 in allVarsX xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsX xs P2 in allVarsX xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVarsX xs P2 in allVarsX xs' P1
    | _ =>
        match type of P with
            | Prop => xs
            | _ => addToList P xs
        end
end.

Ltac allVarsProp xs P :=
match P with
    | False => xs
    | True => xs
    | ?a = ?b => xs
    | ~ ?P' => allVarsProp xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsProp xs P2 in allVarsProp xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsProp xs P2 in allVarsProp xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsProp xs P2 in allVarsProp xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVarsProp xs P2 in allVarsProp xs' P1
    | _ => addToList P xs
end.

Ltac reifyFormula envX envP P :=
match P with
    | False => constr:(fFalse)
    | True => constr:(fTrue)
    | ?a = ?b =>
        let e1 := reifyExp envX a in
        let e2 := reifyExp envX b in constr:(fEq e1 e2)
    | ~ ?P' =>
        let e := reifyFormula envX envP P' in constr:(fImpl e fFalse)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula envX envP P1 in
        let e2 := reifyFormula envX envP P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula envX envP P1 in
        let e2 := reifyFormula envX envP P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula envX envP P1 in
        let e2 := reifyFormula envX envP P2 in constr:(fImpl e1 e2)
    | ?P1 <-> ?P2 =>
        let e1 := reifyFormula envX envP P1 in
        let e2 := reifyFormula envX envP P2 in
          constr:(fAnd (fImpl e1 e2) (fImpl e2 e1))
    | _ =>
        let i := lookup P envP in constr:(fVar i)
end.

Ltac solveGoal' X :=
match goal with
    | |- ?P =>
        let envX := allVarsX constr:(@nil X) P in
        let envP := allVarsProp constr:(@nil Prop) P in
        let f := reifyFormula envX envP P in
          change (formulaDenote envX envP f);
          rewrite <- simplifyFormula_correct; cbn;
          try apply (unwrap (solveFormula envX envP (simplifyFormula f)))
end.

Instance CMon_unit : CMon :=
{
    carrier := unit;
    op := fun _ _ => tt
}.
Proof. all: try destruct x; firstorder. Defined.

Ltac solveGoal :=
match goal with
    | X : CMon |- ?P => solveGoal' X
    | |- ?P => solveGoal' CMon_unit
end.
*)