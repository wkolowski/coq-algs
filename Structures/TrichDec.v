Require Export RCCBase.

Require Export LinDec.

Set Implicit Arguments.

Hint Constructors comparison : core.

Class TrichDec : Type :=
{
    carrier : Type;
    trich_lt : carrier -> carrier -> Prop;
    trich_lt_antisym :
      forall x y : carrier, trich_lt x y -> ~ trich_lt y x;
    trich_lt_trans :
      forall x y z : carrier, trich_lt x y -> trich_lt y z -> trich_lt x z;
    trichb : carrier -> carrier -> comparison;
    trichb_spec :
      forall x y : carrier, CompareSpec (x = y) (trich_lt x y) (trich_lt y x) (trichb x y);
}.

Infix "<" := trich_lt (at level 70).
Infix "<?>" := trichb (at level 70).

Hint Resolve trich_lt_antisym trich_lt_trans : core.

Definition TrichDec_ltb {A : TrichDec} (x y : @carrier A) : bool :=
match x <?> y with
    | Lt => true
    | _ => false
end.

Notation "x <? y" := (TrichDec_ltb x y) (at level 70).

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
    subst. auto.
    auto.
    right. eapply trich_lt_trans; eassumption.
Qed.

Lemma trich_lt_trans' :
  forall (A : TrichDec) (x y z : carrier),
    trich_lt x y -> trich_lt y z -> trich_lt x z.
Proof.
  intros A x y z Hxy Hyz.
  destruct (trichb_spec x z).
    subst. contradict Hyz. apply trich_lt_antisym. assumption.
    assumption.
    destruct (trich_lt_comparison _ _ z y Hxy).
      assumption.
      contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma trich_lt_connected :
  forall (A : TrichDec) (x y : carrier),
    ~ trich_lt x y -> ~ trich_lt y x -> x = y.
Proof.
  intros. destruct (trichb_spec x y).
    assumption.
    contradiction.
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
    contradict H0. subst. apply trich_lt_irrefl.
    contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma trich_lt_trich :
  forall (A : TrichDec) (x y : carrier),
    trich_lt x y \/ x = y \/ trich_lt y x.
Proof.
  intros. destruct (trichb_spec x y); auto.
Qed.

Hint Resolve trichb_spec1 trichb_spec2 trichb_spec3 trich_lt_trich : core.

Ltac trich := cbn; unfold TrichDec_ltb; repeat
match goal with
    | H : context [match ?x <?> ?y with | _ => _ end] |- _ =>
        case_eq (x <?> y); intro
    | |- context [match ?x <?> ?y with | _ => _ end] =>
        case_eq (x <?> y); intro
    | H : _ <?> _ = _ |- _ =>
        rewrite ?trichb_spec1, ?trichb_spec2, ?trichb_spec3 in H
    | H : ?x < ?y, H' : ?y < ?x |- _ =>
        pose (trich_lt_antisym x y H); contradiction
end; dec; cbn; subst; try
match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
    | H : ?x < ?x |- _ => pose (trich_lt_irrefl x); contradiction
end; dec.

#[refine]
Instance TrichDec_to_LinDec (A : TrichDec) : LinDec :=
{
    carrier := @carrier A;
    leq x y := ~ trich_lt y x;
    leqb x y :=
      match trichb x y with
          | Gt => false
          | _ => true
      end
}.
Proof.
  apply trich_lt_irrefl.
  intros. apply trich_lt_connected; assumption.
  intros; intro. decompose [or] (trich_lt_trich A z y); trich.
  intros. decompose [or] (trich_lt_trich A x y); trich.
  intros. case_eq (trichb x y); intro; trich.
Defined.

Coercion TrichDec_to_LinDec : TrichDec >-> LinDec.

Fixpoint trichb_nat (n m : nat) : comparison :=
match n, m with
    | 0, 0 => Eq
    | 0, _ => Lt
    | _, 0 => Gt
    | S n', S m' => trichb_nat n' m'
end.

#[refine]
Instance natlt : TrichDec :=
{
    carrier := nat;
    trich_lt := Peano.lt;
    trichb := trichb_nat
}.
Proof.
  1-2: intros; lia.
  induction x as [| x']; destruct y as [| y']; cbn.
    1-3: constructor; lia.
    destruct (IHx' y'); constructor; lia.
Defined.

Lemma trichb_refl :
  forall (A : TrichDec) (x : A),
    x <?> x = Eq.
Proof.
  intros. rewrite trichb_spec2. trivial.
Qed.

Definition flipcomparison (o : comparison) : comparison :=
match o with
    | Lt => Gt
    | Eq => Eq
    | Gt => Lt
end.

Lemma trichb_flipcomparison :
  forall (A : TrichDec) (x y : @carrier A), flipcomparison (x <?> y) = (y <?> x).
Proof.
  intros. destruct (trichb_spec y x), (trichb_spec x y); cbn; trich.
Qed.

Lemma ltb_negb_leqb :
  forall (A : TrichDec) (x y : A), x <? y = negb (y <=? x).
Proof.
  intros. trich.
Qed.