Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.
Require Import HSLib.Base.
Require Import HSLib.Functor.Functor.

Set Implicit Arguments.

(* Formulas without a fixed signature. *)
Definition Formula (F : Type -> Type) : Type :=
  forall X : Type, (F X -> X) -> X.

Inductive Var (E : Type) : Type :=
    | Var' : Prop -> Var E.

Arguments Var' [E] _.

Inductive And (E : Type) : Type :=
    | And' : E -> E -> And E.

Arguments And' [E] _ _.

Inductive Coproduct (F G : Type -> Type) (E : Type) :=
    | Inl : F E -> Coproduct F G E
    | Inr : G E -> Coproduct F G E.

Arguments Inl {F G E} _.
Arguments Inr {F G E} _.

Notation "F :+: G" := (Coproduct F G) (right associativity, at level 42).

Instance Functor_Var : Functor Var :=
{
    fmap := fun A B f '(Var' P) => Var' P
}.
Proof.
  all: cbn; intros; ext x; destruct x; compute; reflexivity.
Defined.

Instance Functor_And : Functor And :=
{
    fmap := fun A B f '(And' e1 e2) => And' (f e1) (f e2)
}.
Proof.
  all: intros; ext x; destruct x; compute; reflexivity.
Defined.

Instance Functor_Coproduct
  (F G : Type -> Type) (instF : Functor F) (instG : Functor G)
  : Functor (F :+: G) :=
{
    fmap := fun (A B : Type) (f : A -> B) (x : Coproduct F G A) =>
    match x with
        | Inl e => Inl (fmap f e)
        | Inr e => Inr (fmap f e)
    end
}.
Proof.
  all: intros; ext x; destruct x; functor.
Defined.

Class Denote (F : Type -> Type) : Type :=
{
    denoteAlgebra : F Prop -> Prop;
}.

Instance Denote_Var : Denote Var :=
{
    denoteAlgebra := fun '(Var' P) => P
}.

Instance Denote_And : Denote And :=
{
    denoteAlgebra := fun '(And' P Q) => P /\ Q
}.

Instance Denote_Coproduct
  (F G : Type -> Type) (instF : Denote F) (instG : Denote G)
  : Denote (F :+: G) :=
{
    denoteAlgebra := fun x =>
    match x with
        | Inl x => denoteAlgebra x
        | Inr x => denoteAlgebra x
    end
}.

Definition andExample : Formula (Var :+: And) :=
  fun X In => In (Inr (And' (In (Inl (Var' True))) (In (Inl (Var' False))))).

Definition foldExpr
  {F : Type -> Type} {A : Type} (f : F A -> A) (x : Formula F) : A :=
    x _ f.

Definition denote
  {F : Type -> Type} {instE : Denote F}
  (x : Formula F) : Prop := foldExpr denoteAlgebra x.

Compute denote andExample.

(*

Fixpoint formulaDenote (env : Env Prop) (f : formula) : Prop :=
match f with
    | fFalse => False
    | fTrue => True
    | fVar i => holds i env
    | fAnd f1 f2 => formulaDenote env f1 /\ formulaDenote env f2
    | fOr f1 f2 => formulaDenote env f1 \/ formulaDenote env f2
    | fImpl f1 f2 => formulaDenote env f1 -> formulaDenote env f2
end.

Function simplifyFormula (f : formula) : formula :=
match f with
    | fFalse => fFalse
    | fTrue => fTrue
    | fVar P => fVar P
    | fAnd f1 f2 =>
        match simplifyFormula f1, simplifyFormula f2 with
            | fOr f11 f12, f2' => fOr (fAnd f11 f2') (fAnd f12 f2')
            | f1', fOr f21 f22 => fOr (fAnd f1' f21) (fAnd f1' f22)
            | fFalse, _ => fFalse
            | _, fFalse => fFalse
            | fTrue, f2' => f2'
            | f1', fTrue => f1'
            | f1', f2' => fAnd f1' f2'
        end
    | fOr f1 f2 =>
        match simplifyFormula f1, simplifyFormula f2 with
            | fAnd f11 f12, f2' => fAnd (fOr f11 f2') (fOr f12 f2')
            | f1', fAnd f21 f22 => fAnd (fOr f1' f21) (fOr f1' f22)
            | fFalse, f2' => f2'
            | f1', fFalse => f1'
            | fTrue, _ => fTrue
            | _, fTrue => fTrue
            | f1', f2' => fOr f1' f2'
        end
    | fImpl f1 f2 =>
        match simplifyFormula f1 with
            | fFalse => fTrue
            | fTrue => f2
            | fAnd f11 f12 => fImpl f11 (fImpl f12 f2)
            | fOr f11 f12 => fAnd (fImpl f11 f2) (fImpl f12 f2)
            | f1' => fImpl f1' f2
        end
end.

Theorem simplifyFormula_correct :
  forall (f : formula) (env : Env Prop),
    formulaDenote env (simplifyFormula f) <-> formulaDenote env f.
Proof.
  intros. functional induction simplifyFormula f; cbn.
  Time all:
  repeat match goal with
      | e : simplifyFormula ?f = _,
        IH : formulaDenote _ (simplifyFormula ?f) <-> _ |- _ =>
        rewrite <- IH, e; cbn
  end; try (tauto; fail).
Qed.

Definition solveHypothesis (env : Env Prop) :
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

Definition solveGoal (env : Env Prop)
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

Definition solveFormula (env : Env Prop) (f : formula)
  : solution (formulaDenote env f).
Proof.
  refine (Reduce (solveGoal env [] f)). apply f0. cbn. trivial.
Defined.

Theorem solveFormula_correct :
  forall (env : Env Prop) (f : formula),
    (exists p : formulaDenote env f, solveFormula env f = Yes' p) ->
      formulaDenote env f.
Proof.
  intros. destruct H. assumption.
Qed.

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

Ltac reflectFormula :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in
          change (formulaDenote xs f);
          rewrite <- simplifyFormula_correct; cbn
end.

Ltac solveGoal' :=
match goal with
    |- ?P =>
        let xs := allVarsFormula constr:(@nil Prop) P in
        let f := reifyFormula xs P in change (formulaDenote xs f);
          rewrite <- simplifyFormula_correct; cbn;
          try apply (unwrap (solveFormula xs (simplifyFormula f)))
end.

Ltac solveGoal := solveGoal'; fail.*)