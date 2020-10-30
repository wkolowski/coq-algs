Require Export RCCBase.

Set Implicit Arguments. 

Class TrichDec : Type :=
{
    carrier : Type;
    trich_lt : carrier -> carrier -> Prop;
    (* trich_lt_antisym :
      forall x y : carrier, trich_lt x y -> ~ trich_lt y x;
     *)trich_lt_trans :
      forall x y z : carrier, trich_lt x y -> trich_lt y z -> trich_lt x z;
    trichb : carrier -> carrier -> comparison;
    trichb_spec :
      forall x y : carrier, CompareSpec (x = y) (trich_lt x y) (trich_lt y x) (trichb x y);
    CompOpp_trichb :
      forall x y : carrier,
        CompOpp (trichb x y) = trichb y x;
}.

Hint Resolve trich_lt_trans : core.

Definition TrichDec_ltb {A : TrichDec} (x y : @carrier A) : bool :=
match trichb x y with
    | Lt => true
    | _ => false
end.

Definition TrichDec_le {A : TrichDec} (x y : @carrier A) : Prop :=
  trich_lt x y \/ x = y.

Definition TrichDec_leb {A : TrichDec} (x y : @carrier A) : bool :=
match trichb x y with
    | Lt | Eq => true
    | Gt      => false
end.

Infix "<?>" := trichb (at level 70).
Infix "<?" := TrichDec_ltb (at level 70).
Infix "x ?> y" := (TrichDec_ltb y x) (at level 70).
Infix "<=?" := TrichDec_leb (at level 70).
Infix "x >=? y" := (TrichDec_leb y x) (at level 70).

Infix "<" := trich_lt (at level 70).
Infix "x > y" := (trich_lt y x) (at level 70).
Infix "<=" := TrichDec_le (at level 70).
Infix "x >= y" := (TrichDec_le y x) (at level 70).

Require Import Equality.

Lemma trich_lt_irrefl' :
  forall (A : TrichDec) (x : carrier),
    ~ trich_lt x x.
Proof.
  intros A x H. Check trichb_spec.
  destruct (trichb_spec x x).
  pose (Hxx := trichb_spec x x). inv Hxx.
    pose (H0' := H0). apply (f_equal CompOpp) in H0'.
      cbn in H0'. rewrite CompOpp_trichb in H0'. congruence.
  destruct (trichb_spec x x) eqn: Hxx.
Qed.


Lemma trich_lt_antisym :
  forall (A : TrichDec) (x y : carrier),
    trich_lt x y -> ~ trich_lt y x.
Proof.
  intros A x y Hxy Hyx.
  remember (trichb_spec x y) as Hxy'.
  remember (trichb_spec y x) as Hyx'.
  dependent destruction Hxy'.
  dependent destruction Hyx'. Focus 4.
  apply (f_equal CompOpp) in x1;
  rewrite CompOpp_trichb in x1; cbn in *.
    all: try congruence.
Admitted.
  
  dependent destruction (trichb_spec x y). eqn: Hxy'.
           (trichb_Spec y x) eqn: Hyx'.
    
Lemma trich_lt_irrefl :
  forall (A : TrichDec) (x : carrier),
    ~ trich_lt x x.
Proof.
  intros A x H. eapply trich_lt_antisym; eassumption.
Qed.

Hint Extern 0 =>
match goal with
    | H : _ < _ |- _ => apply trich_lt_irrefl in H; contradiction
end
  : core.

Lemma trich_lt_antisym' :
  forall (A : TrichDec) (x y : carrier),
    trich_lt x y -> ~ trich_lt y x.
Proof.
  intros A x y.
  intros Hxy Hyx.
  eapply trich_lt_irrefl, trich_lt_trans; eassumption.
Qed.

Lemma trich_lt_comparison :
  forall (A : TrichDec) (x y z : carrier),
    trich_lt x z -> trich_lt x y \/ trich_lt y z.
Proof.
  intros. destruct (trichb_spec x y).
    auto.
    subst. auto.
    right. eapply trich_lt_trans; eassumption.
Qed.

Lemma trich_lt_trans' :
  forall (A : TrichDec) (x y z : carrier),
    trich_lt x y -> trich_lt y z -> trich_lt x z.
Proof.
  intros A x y z Hxy Hyz.
  destruct (trichb_spec x z).
    assumption.
    subst. contradict Hyz. apply trich_lt_antisym. assumption.
    destruct (trich_lt_comparison _ _ z y Hxy).
      assumption.
      contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma trich_lt_connected :
  forall (A : TrichDec) (x y : carrier),
    ~ trich_lt x y -> ~ trich_lt y x -> x = y.
Proof.
  intros. destruct (trichb_spec x y).
    contradiction.
    assumption.
    contradiction.
Qed.

Hint Resolve trich_lt_irrefl trich_lt_comparison trich_lt_trans trich_lt_connected : core.

Lemma trichb_spec1 :
  forall (A : TrichDec) (x y : carrier),
    trichb x y = Lt <-> trich_lt x y.
Proof.
  intros. destruct (trichb_spec x y);
  subst; firstorder; try congruence.
    contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma trichb_spec2 :
  forall (A : TrichDec) (x y : carrier),
    trichb x y = Eq <-> x = y.
Proof.
  intros. destruct (trichb_spec x y);
  firstorder; subst; auto; congruence.
Qed.

Lemma trichb_spec3 :
  forall (A : TrichDec) (x y : carrier),
    trichb x y = Gt <-> trich_lt y x.
Proof.
  intros. destruct (trichb_spec x y);
  firstorder; try congruence.
    contradict H0. apply trich_lt_antisym. assumption.
    contradict H0. subst. apply trich_lt_irrefl.
Qed.

Lemma trich_lt_trich :
  forall (A : TrichDec) (x y : carrier),
    trich_lt x y \/ x = y \/ trich_lt y x.
Proof.
  intros. destruct (trichb_spec x y); auto.
Qed.

Hint Resolve trichb_spec1 trichb_spec2 trichb_spec3 trich_lt_trich : core.