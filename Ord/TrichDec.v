Require Export List.
Export ListNotations.

Require Export Bool.Bool.
Require Export Arith.
Require Export Omega.

Set Implicit Arguments.

Inductive Ord : Type :=
    | Lt : Ord
    | Eq : Ord
    | Gt : Ord.

Hint Constructors reflect Ord.

Class TrichDec : Type :=
{
    carrier : Type;
    lt : carrier -> carrier -> Prop;
    lt_irrefl : forall x : carrier, ~ lt x x;
    lt_antisym : forall x y : carrier, lt x y -> ~ lt y x;
    lt_trans : forall x y z : carrier, lt x y -> lt y z -> lt x z;
    lt_trich : forall x y : carrier, lt x y \/ x = y \/ lt y x;
    trichb : carrier -> carrier -> Ord;
    trichb_spec1 : forall x y : carrier,
        trichb x y = Lt <-> lt x y;
    trichb_spec2 : forall x y : carrier,
        trichb x y = Eq <-> x = y;
    trichb_spec3 : forall x y : carrier,
        trichb x y = Gt <-> lt y x;
}.

Coercion carrier : TrichDec >-> Sortclass.

Infix "<" := lt (at level 70).
Infix "<?>" := trichb (at level 70).

Hint Resolve lt_irrefl lt_antisym lt_trans lt_trich.

Lemma trichb_refl :
  forall (A : TrichDec) (x : A),
    x <?> x = Eq.
Proof.
  intros. rewrite trichb_spec2. trivial.
Qed.

Definition TrichDec_eqb {A : TrichDec} (x y : A) : bool :=
match x <?> y with
    | Eq => true
    | _ => false
end.

Infix "=?" := TrichDec_eqb (at level 70).

Definition TrichDec_eq_dec :
  forall {A : TrichDec} (x y : A), {x = y} + {x <> y}.
Proof.
  intros. case_eq (trichb x y); intro.
    right. intro. subst. destruct (trichb_spec2 y y).
      rewrite H1 in H; congruence.
    left. apply trichb_spec2. assumption.
    right. intro. subst. destruct (trichb_spec2 y y).
      rewrite H1 in H; congruence.
Defined.

Theorem TrichDec_eqb_spec :
  forall (A : TrichDec) (x y : A), reflect (x = y) (x =? y).
Proof.
  unfold TrichDec_eqb. intros.
  case_eq (x <?> y); constructor; try intro; subst.
    rewrite trichb_refl in H. congruence.
    rewrite trichb_spec2 in H. assumption.
    rewrite trichb_refl in H. congruence.
Defined.

(*Lemma TrichDec_not_lt :
  forall (A : TrichDec) (x y : A),
    ~ lt x y -> lt y x.
Proof.
  intros. destruct (leb_spec y x).
    assumption.
    cut False.
      inversion 1.
      destruct (le_total x y); contradiction.
Defined.

Hint Resolve TrichDec_not_le.*)

Definition trichb_leb {A : TrichDec} (x y : A) : bool :=
match x <?> y with
    | Gt => false
    | _ => true
end.

Notation "x <=? y" := (trichb_leb x y) (at level 70).

Definition trichb_ltb {A : TrichDec} (x y : A) : bool :=
match x <?> y with
    | Lt => true
    | _ => false
end.

Notation "x <? y" := (trichb_ltb x y) (at level 70).

(*Notation "x >? y" := (trichb_ltb y x) (at level 70).*)

Ltac trich :=
  simpl; unfold TrichDec_eqb, trichb_leb, trichb_ltb in *; repeat
match goal with
    | H : context [match ?x <?> ?y with | _ => _ end] |- _ =>
        case_eq (x <?> y); intro
    | |- context [match ?x <?> ?y with | _ => _ end] =>
        case_eq (x <?> y); intro
    | H : _ <?> _ = _ |- _ =>
        rewrite ?trichb_spec1, ?trichb_spec2, ?trichb_spec3 in H
    | H : ?x < ?y, H' : ?y < ?x |- _ =>
        pose (lt_antisym x y H); contradiction
end; simpl; subst; try
match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
    | H : ?x < ?x |- _ => pose (lt_irrefl x); contradiction
end; eauto; try omega; try congruence.

Fixpoint trichb_nat (n m : nat) : Ord :=
match n, m with
    | 0, 0 => Eq
    | 0, _ => Lt
    | _, 0 => Gt
    | S n', S m' => trichb_nat n' m'
end.

Instance natlt : TrichDec :=
{
    carrier := nat;
    lt := Peano.lt;
    trichb := trichb_nat
}.
Proof.
  1-4: intros; omega.
  induction x as [| x']; destruct y as [| y']; cbn;
  split; try (trich; fail).
    intros. apply lt_n_S. apply IHx'. assumption.
    rewrite IHx'. apply lt_S_n.
  induction x as [| x']; destruct y as [| y']; cbn;
  split; try (trich; fail); intros.
    f_equal. apply IHx'. assumption.
    rewrite IHx'. congruence.
  induction x as [| x']; destruct y as [| y']; cbn;
  split; try (trich; fail).
    intros. apply lt_n_S. apply IHx'. assumption.
    rewrite IHx'. apply lt_S_n.
Defined.

Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].

(*Definition min_dflt (A : TrichDec) (d : A) (l : list A) : A :=
  fold_right (fun x y => if x <=? y then x else y) d l.

Lemma min_spec :
  forall (A : TrichDec) (x h : A) (t : list A),
    In x (h :: t) -> min_dflt A h t ≤ x.
Proof.
  induction t as [| h' t']; simpl in *.
    destruct 1; subst; auto.
    destruct 1 as [H1 | [H2 | H3]]; subst; dec.
Qed.

Theorem min_In :
  forall (A : TrichDec) (h : A) (t : list A),
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

Theorem TrichDec_le_dec :
  forall (A : TrichDec) (x y : A), {x ≤ y} + {y ≤ x}.
Proof.
  intros. destruct (leb_spec x y).
    left. assumption.
    right. apply TrichDec_not_le. assumption.
Defined.*)