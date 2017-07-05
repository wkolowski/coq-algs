Require Export List.
Export ListNotations.

Require Export Bool.Bool.
Require Export Arith.
Require Export Omega.

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

Infix "≤" := leq (at level 70).
Infix "<=?" := leqb (at level 70).

Hint Resolve leq_refl leq_antisym leq_trans leq_total.
Hint Constructors reflect.

Definition LinDec_eqb {A : LinDec} (x y : A) : bool :=
    andb (leqb x y) (leqb y x).

Infix "=?" := LinDec_eqb (at level 70).

Definition LinDec_eq_dec : forall {A : LinDec} (x y : A),
    {x = y} + {x <> y}.
Proof.
  intros. destruct (leqb_spec x y) as [H1 | H1], (leqb_spec y x) as [H2 | H2].
    left; apply leq_antisym; auto.
    right. intro. apply H2. subst. auto.
    right. intro. apply H1. subst. auto.
    cut False.
      inversion 1.
      destruct (leq_total x y); contradiction.
Defined.

Theorem LinDec_eqb_spec :
  forall (A : LinDec) (x y : A), reflect (x = y) (x =? y).
Proof.
  unfold LinDec_eqb. intros.
  destruct (LinDec_eq_dec x y); subst.
    destruct (leqb_spec y y); simpl; auto.
    destruct (leqb_spec x y); simpl; auto.
      destruct (leqb_spec y x); simpl; auto.
Defined.

Ltac dec := simpl; repeat
match goal with
    | |- context [?x =? ?y] => destruct (LinDec_eqb_spec _ x y); subst; intros
    | |- context [?x <=? ?y] => destruct (leqb_spec x y); intros
end; simpl; try
match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
end; auto; try omega.

Lemma LinDec_not_leq : forall (A : LinDec) (x y : A),
    ~ leq x y -> leq y x.
Proof.
  intros. destruct (leqb_spec y x).
    assumption.
    cut False.
      inversion 1.
      destruct (leq_total x y); contradiction.
Defined.

Hint Resolve LinDec_not_leq.

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
    apply leb_complete_conv in H. constructor. omega.
Defined.

Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].

Definition min_dflt (A : LinDec) (d : A) (l : list A) : A :=
    fold_right (fun x y => if x <=? y then x else y) d l.

Theorem min_In :
  forall (A : LinDec) (h : A) (t : list A),
    In (min_dflt A h t) (h :: t).
Proof.
  induction t as [| h' t'].
    simpl. left. reflexivity.
    inversion IHt'.
      simpl. destruct (h' <=? _).
        right. left. reflexivity.
        left. assumption.
      simpl. destruct (h' <=? _).
        right. left. reflexivity.
        right. right. assumption.
Qed.