Require Export RCCBase.

Set Implicit Arguments.

Class TrichDec : Type :=
{
    carrier : Type;
    trich_lt : carrier -> carrier -> Prop;
    trich_lt_antisym :
      forall {x y : carrier}, trich_lt x y -> ~ trich_lt y x;
    trich_lt_trans :
      forall {x y z : carrier}, trich_lt x y -> trich_lt y z -> trich_lt x z;
    cmp : carrier -> carrier -> comparison;
    cmp_spec :
      forall x y : carrier, CompareSpec (x = y) (trich_lt x y) (trich_lt y x) (cmp x y);
}.

Coercion carrier : TrichDec >-> Sortclass.

(* Hint Resolve trich_lt_trans : core. *)

Definition trich_ltb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Lt => true
    | _ => false
end.

Definition trich_leb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Lt | Eq => true
    | Gt      => false
end.

Definition trich_eqb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Eq => true
    | _  => false
end.

Definition trich_le {A : TrichDec} (x y : A) : Prop :=
  trich_lt x y \/ x = y.

Infix "<?>" := cmp (at level 30).
Infix "<?" := trich_ltb (at level 70).
Notation "x >? y" := (trich_ltb y x) (at level 30).
Infix "≤?" := trich_leb (at level 30).
Notation "x >=? y" := (trich_leb y x) (at level 30).
Infix "==?" := trich_eqb (at level 30).

Infix "<" := trich_lt (at level 70).
Notation "x > y" := (trich_lt y x) (at level 70, only parsing).
(* Infix "≤" := trich_le (at level 30). *)
Notation "x >= y" := (trich_le y x) (at level 70, only parsing).

Lemma trich_lt_irrefl :
  forall {A : TrichDec} {x : A},
    ~ trich_lt x x.
Proof.
  intros A x H. eapply trich_lt_antisym; eassumption.
Qed.

Lemma trich_lt_connected :
  forall {A : TrichDec} {x y : A},
    ~ trich_lt x y -> ~ trich_lt y x -> x = y.
Proof.
  intros. destruct (cmp_spec x y).
    assumption.
    contradiction.
    contradiction.
Qed.

Lemma trich_lt_comparison :
  forall {A : TrichDec} {x z : A},
    trich_lt x z -> forall y : A, trich_lt x y \/ trich_lt y z.
Proof.
  intros. destruct (cmp_spec x y).
    subst. auto.
    auto.
    right. eapply trich_lt_trans; eassumption.
Qed.

(** comparison properties *)

Lemma cmp_spec1 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Lt <-> trich_lt x y.
Proof.
  intros. destruct (cmp_spec x y).
    subst. split.
      inv 1.
      intro. contradict H. apply trich_lt_irrefl.
    firstorder.
    split.
      inv 1.
      intro. contradict H. apply trich_lt_antisym. assumption.
Qed.

Lemma cmp_spec2 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Eq <-> x = y.
Proof.
  intros. destruct (cmp_spec x y).
    firstorder.
    split; inv 1. contradict H. apply trich_lt_irrefl.
    split; inv 1. contradict H. apply trich_lt_irrefl.
Qed.

Lemma cmp_spec3 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Gt <-> trich_lt y x.
Proof.
  intros. destruct (cmp_spec x y);
  firstorder; try congruence.
    contradict H0. subst. apply trich_lt_irrefl.
    contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma CompOpp_cmp :
  forall {A : TrichDec} {x y : A},
    CompOpp (x <?> y) = (y <?> x).
Proof.
  intros.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : ?x < ?y |- _ =>
          pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma cmp_refl :
  forall {A : TrichDec} (x : A),
    x <?> x = Eq.
Proof.
  intros.
  destruct (cmp_spec x x).
    reflexivity.
    apply trich_lt_irrefl in H. contradiction.
    apply trich_lt_irrefl in H. contradiction.
Qed.

Lemma trich_ltb_irrefl :
  forall {A : TrichDec} (x : A),
    x <? x = false.
Proof.
  intros.
  unfold trich_ltb.
  rewrite cmp_refl.
  reflexivity.
Qed.

Lemma negb_trich_ltb :
  forall {A : TrichDec} (x y : A),
    negb (x <? y) = x >=? y.
Proof.
  intros.
  unfold trich_ltb, trich_leb.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : _ < _ |- _ => pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma trich_leb_refl :
  forall {A : TrichDec} (x : A),
    x ≤? x = true.
Proof.
  intros.
  unfold trich_leb.
  rewrite cmp_refl.
  reflexivity.
Qed.

Lemma negb_trich_leb :
  forall {A : TrichDec} (x y : A),
    negb (x ≤? y) = x >? y.
Proof.
  intros.
  unfold trich_ltb, trich_leb.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : _ < _ |- _ => pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma trich_eqb_refl :
  forall {A : TrichDec} (x : A),
    x ==? x = true.
Proof.
  intros.
  unfold trich_eqb.
  rewrite cmp_refl.
  reflexivity.
Qed.

(* Newest lemmas *)

Lemma trichb_Gt_to_Lt :
  forall {A : TrichDec} {x y : A},
    x <?> y = Gt -> y <?> x = Lt.
Proof.
  intros A x y Hxy.
  rewrite ?cmp_spec1, <- ?cmp_spec3 in *.
  assumption.
Qed.

Lemma trichb_trans_Lt :
  forall {A : TrichDec} {x y z : A},
    x <?> y = Lt -> y <?> z = Lt -> x <?> z = Lt.
Proof.
  intros A x y z Hxy Hyz.
  rewrite cmp_spec1 in *.
  eapply trich_lt_trans; eassumption.
Qed.

(* Specs *)

Lemma trich_eqb_spec :
  forall {A : TrichDec} (x y : A),
    BoolSpec (x = y) (x <> y) (trich_eqb x y).
Proof.
  intros.
  unfold trich_eqb.
  destruct (cmp_spec x y); constructor.
    assumption.
    inv 1. apply trich_lt_irrefl in H. assumption.
    inv 1. apply trich_lt_irrefl in H. assumption.
Qed.

Ltac trich :=
  cbn;
  unfold trich_ltb, trich_leb, trich_eqb;
repeat match goal with
(* General contradictions *)
    | H : False |- _ => contradiction
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
(* Easy contradictions from TrichDec properties *)
    | H : ?x < ?x |- _ => apply trich_lt_irrefl in H; contradiction
    | H : ?x < ?y, H' : ?y < ?x |- _ =>
        pose (trich_lt_antisym x y H); contradiction
(* Deduce equality and substitute *)
    | H : _ <?> _ = Eq |- _ => rewrite cmp_spec2 in H; subst
    | H : ~ ?x < ?y, H' : ~ ?y < ?x |- _ =>
        pose (trich_lt_connected H H'); subst; clear H H'
(* Computational properties of cmp *)
    | H : context [?x <?> ?x] |- _ =>
        rewrite cmp_refl in H
    | |- context [?x <?> ?x] =>
        rewrite cmp_refl
    | H : context [CompOpp (_ <?> _)] |- _ =>
        rewrite CompOpp_cmp in H
    | |- context [CompOpp (_ <?> _)] =>
        rewrite CompOpp_cmp
(* Computational properties of derived operations *)
    | H : context [?x <? ?x] |- _ =>
        rewrite trich_ltb_irrefl in H
    | |- context [?x <? ?x] =>
        rewrite trich_ltb_irrefl
    | H : context [?x ≤? ?x] |- _ =>
        rewrite trich_leb_refl in H
    | |- context [?x ≤? ?x] =>
        rewrite trich_leb_refl
    | H : context [?x ==? ?x] |- _ =>
        rewrite trich_eqb_refl in H
    | |- context [?x ==? ?x] =>
        rewrite trich_eqb_refl
(* Transitivity *)
    | Hxy : ?x < ?y, Hyz : ?y < ?z |- _ =>
        assert (x < z) by (eapply trich_lt_trans; eauto)
    | Hxy : _ <?> _ = Gt |- _ => apply trichb_Gt_to_Lt in Hxy
    | Hxy : ?x <?> ?y = Lt, Hyz : ?y <?> ?z = Lt |- _ =>
        match goal with
            | Hyz : x <?> z = Lt |- _ => idtac
            | _ => pose (Hxz := trichb_trans_Lt Hxy Hyz); clearbody Hxz
        end
(* Case analysis *)
    | H : context [match ?x <?> ?y with | _ => _ end] |- _ =>
        destruct (cmp_spec x y)
    | |- context [match ?x <?> ?y with | _ => _ end] =>
        destruct (cmp_spec x y)
(* reverse cases *)
(*     | H : _ <?> _ = _ |- _ =>
        rewrite ?cmp_spec1, ?cmp_spec3 in H
 *)    | _ => subst; auto; try congruence
end;
  subst; auto; try congruence.

Ltac trich_aggresive :=
repeat match goal with
    | H : context [?x <?> ?y] |- _ => destruct (cmp_spec x y); subst
    | |- context [?x <?> ?y] => destruct (cmp_spec x y); subst
end.

Ltac trich' := trich; try (trich_aggresive; trich; fail).

Fixpoint cmp_nat (n m : nat) : comparison :=
match n, m with
    | 0, 0 => Eq
    | 0, _ => Lt
    | _, 0 => Gt
    | S n', S m' => cmp_nat n' m'
end.

#[refine]
Instance natlt : TrichDec :=
{
    carrier := nat;
    trich_lt := Peano.lt;
    cmp := cmp_nat
}.
Proof.
  1-2: intros; lia.
  induction x as [| x']; destruct y as [| y']; cbn.
    1-3: constructor; lia.
    destruct (IHx' y'); constructor; lia.
Defined.


Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].