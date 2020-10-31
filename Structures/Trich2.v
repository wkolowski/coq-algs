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