Require Export List.
Export ListNotations.

Require Export Bool.Bool.
Require Export Arith.
Require Export Lia.

Class LinDec : Type :=
{
    carrier : Type;
    leq : carrier -> carrier -> Prop;
    leq_refl : forall x : carrier, leq x x;
    leq_antisym : forall x y : carrier, leq x y -> leq y x -> x = y;
    leq_trans : forall x y z : carrier, leq x y -> leq y z -> leq x z;
    leq_total : forall x y : carrier, leq x y \/ leq y x;
    leqb : carrier -> carrier -> bool;
    leqb_spec : forall x y : carrier, reflect (leq x y) (leqb x y)
}.

Coercion carrier : LinDec >-> Sortclass.
Coercion leq : LinDec >-> Funclass.

Infix "≤" := leq (at level 70).
Infix "<=?" := leqb (at level 70).

Hint Resolve leq_refl leq_antisym leq_trans leq_total : core.
Hint Constructors reflect : core.

Definition LinDec_eqb {A : LinDec} (x y : A) : bool :=
    andb (leqb x y) (leqb y x).

Infix "=?" := LinDec_eqb (at level 70).

Theorem LinDec_eqb_spec :
  forall (A : LinDec) (x y : A), reflect (x = y) (x =? y).
Proof.
  unfold LinDec_eqb. intros.
  destruct (leqb_spec x y); cbn.
    destruct (leqb_spec y x); constructor.
      apply leq_antisym; assumption.
      intro. subst. contradiction.
    constructor. intro. subst. apply n, leq_refl.
Defined.

Require Import RCCBase.

Lemma LinDec_not_leq_lt :
  forall (A : LinDec) (x y : A), ~ leq x y -> y ≤ x /\ x <> y.
Proof.
  intros. destruct (leq_total x y).
    contradiction.
    split; [assumption | inv 1].
Defined.

#[refine]
Instance natle : LinDec :=
{
    carrier := nat;
    leq := le;
    leqb := leb
}.
Proof.
  intros. apply le_n.
  intros. apply le_antisym; auto.
  intros. eapply le_trans; eauto.
  intros. destruct (le_gt_dec x y) as [H | H].
    left. auto.
    right. unfold lt in H. apply le_Sn_le. auto.
  intros. case_eq (leb x y); intro.
    apply leb_complete in H. auto.
    apply leb_complete_conv in H. constructor. lia.
Defined.

Ltac dec := cbn; repeat
match goal with
    | |- context [?x =? ?y] =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | |- context [?x <=? ?y] =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
    | H : context [?x =? ?y] |- _ =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | H : context [?x <=? ?y] |- _ =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
    | H : ?a ≤ ?b, H' : ?b ≤ ?a |- _ =>
        let H'' := fresh "H" in
          assert (H'' := leq_antisym _ _ H H'); clear H H'; subst
    | H : ~ ?x ≤ ?y |- _ =>
        apply LinDec_not_leq_lt in H; destruct H
    | |- ?x ≤ ?x => apply leq_refl
end; cbn; try
match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
    | H : True |- _ => clear H
    | H : ?x = ?x |- _ => clear H
end; eauto; try lia; try congruence.

Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].