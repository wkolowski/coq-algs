Require Import CoqAlgs.Base.

Inductive formula : Set :=
    | FConst : bool -> formula
    | FAnd : formula -> formula -> formula
    | FOr : formula -> formula -> formula
    | FImp : formula -> formula -> formula.

Fixpoint denote (f : formula) : Prop :=
match f with
    | FConst b => if b then True else False
    | FAnd f1 f2 => denote f1 /\ denote f2
    | FOr f1 f2 => denote f1 \/ denote f2
    | FImp f1 f2 => denote f1 -> denote f2
end.

Fixpoint solve (f : formula) : bool :=
match f with
    | FConst b => b
    | FAnd f1 f2 => andb (solve f1) (solve f2)
    | FOr f1 f2 => orb (solve f1) (solve f2)
    | FImp f1 f2 => implb (solve f1) (solve f2)
end.

Class Reify (P : Prop) : Type :=
{
    reify : formula;
    spec : reflect (denote reify) (solve reify)
}.

Arguments reify _ {Reify}.

#[refine]
#[export]
Instance ReifyFalse : Reify False :=
{
    reify := FConst false
}.
Proof. auto. Defined.

#[refine]
#[export]
Instance ReifyTrue : Reify True :=
{
    reify := FConst true
}.
Proof. simpl; auto. Defined.

#[refine]
#[export]
Instance ReifyAnd (P Q : Prop) (RP : Reify P) (RQ : Reify Q)
    : Reify (P /\ Q) :=
{
    reify := FAnd (@reify P RP) (@reify Q RQ)
}.
Proof.
  destruct RP as [fP HP], RQ as [fQ HQ]. simpl.
    destruct HP, HQ; auto; constructor; tauto.
Defined.

#[refine]
#[export]
Instance ReifyOr (P Q : Prop) (RP : Reify P) (RQ : Reify Q)
    : Reify (P \/ Q) :=
{
    reify := FOr (@reify P RP) (@reify Q RQ)
}.
Proof.
  destruct RP as [fP HP], RQ as [fQ HQ]. simpl.
    destruct HP, HQ; auto; constructor; tauto.
Defined.

#[refine]
#[export]
Instance ReifyImp (P Q : Prop) (RP : Reify P) (RQ : Reify Q)
    : Reify (P -> Q) :=
{
    reify := FImp (@reify P RP) (@reify Q RQ)
}.
Proof.
  destruct RP as [fP HP], RQ as [fQ HQ]. simpl.
    destruct HP, HQ; auto; constructor; tauto.
Defined.

Theorem solve_denote :
  forall (P : Prop) (RP : Reify P),
    solve (reify P) = true -> denote (reify P).
Proof.
  destruct RP; simpl; intro. rewrite H in spec0.
  inversion spec0. assumption.
Qed.

Ltac obvious :=
match goal with
    | |- ?P =>
        change (denote (reify P));
        apply solve_denote; reflexivity
end.

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof. tauto. Qed.

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  obvious.
Qed.