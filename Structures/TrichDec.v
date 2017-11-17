Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Export LinDec.

Set Implicit Arguments.

Inductive Ord : Type :=
    | Lt : Ord
    | Eq : Ord
    | Gt : Ord.

Hint Constructors Ord.

Class TrichDec : Type :=
{
    carrier : Type;
    trich_lt : carrier -> carrier -> Prop;
    trich_lt_irrefl :
      forall x : carrier, ~ trich_lt x x;
    trich_lt_antisym :
      forall x y : carrier, trich_lt x y -> ~ trich_lt y x;
    trich_lt_trans :
      forall x y z : carrier, trich_lt x y -> trich_lt y z -> trich_lt x z;
    trich_lt_trich :
      forall x y : carrier, trich_lt x y \/ x = y \/ trich_lt y x;
    trichb : carrier -> carrier -> Ord;
    trichb_spec1 :
      forall x y : carrier, trichb x y = Lt <-> trich_lt x y;
    trichb_spec2 :
      forall x y : carrier, trichb x y = Eq <-> x = y;
    trichb_spec3 :
      forall x y : carrier, trichb x y = Gt <-> trich_lt y x;
}.

Infix "<" := trich_lt (at level 70).
Infix "<?>" := trichb (at level 70).

Hint Resolve trich_lt_irrefl trich_lt_antisym trich_lt_trans trich_lt_trich.

Hint Extern 0 =>
match goal with
    | H : _ < _ |- _ => apply trich_lt_irrefl in H; contradiction
end.

Definition TrichDec_ltb {A : TrichDec} (x y : @carrier A) : bool :=
match x <?> y with
    | Lt => true
    | _ => false
end.

Notation "x <? y" := (TrichDec_ltb x y) (at level 70).

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
  intros. decompose [or] (trich_lt_trich x y); trich.
  intros; intro. decompose [or] (trich_lt_trich z y); trich.
  intros. decompose [or] (trich_lt_trich x y); trich.
  intros. case_eq (trichb x y); intro; trich.
Defined.

Coercion TrichDec_to_LinDec : TrichDec >-> LinDec.

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
    trich_lt := Peano.lt;
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

Lemma trichb_refl :
  forall (A : TrichDec) (x : A),
    x <?> x = Eq.
Proof.
  intros. rewrite trichb_spec2. trivial.
Qed.

(*Definition flipOrd (o : Ord) : Ord :=
match o with
    | Lt => Gt
    | Eq => Eq
    | Gt => Lt
end.

Lemma trichb_flipOrd :
  forall (A : TrichDec) (x y : @carrier A), flipOrd (x <?> y) = (y <?> x).
Proof.
  intros. unfold flipOrd.
*)

Lemma ltb_negb_leqb :
  forall (A : TrichDec) (x y : A), x <? y = negb (y <=? x).
Proof.
  intros. trich.
Qed.