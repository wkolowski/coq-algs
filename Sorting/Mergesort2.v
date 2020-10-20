Require Export Recdef.

Require Export Sorting.Sort.
Require Export ListLemmas.

Class msArgs : Type :=
{
    A : Type;
    small : list A -> bool;
    adhoc : list A -> list A;
    split : list A -> list A * list A;
    merge : list A -> list A -> list A;

    split_spec_l :
      forall l : list A,
        small l = false -> length (fst (split l)) < length l;
    split_spec_r :
      forall l : list A,
        small l = false -> length (snd (split l)) < length l;

    R : A -> A -> Prop;

    Sorted_adhoc :
      forall l : list A,
        small l = true -> Sorted R (adhoc l);

    Sorted_merge :
      forall l l1 l2 : list A,
        Sorted R l1 -> Sorted R l2 -> Sorted R (merge l1 l2);

    perm_adhoc :
      forall l : list A,
        small l = true -> perm (adhoc l) l;

    perm_split :
      forall l l1 l2 : list A,
        split l = (l1, l2) -> perm (l1 ++ l2) l;

    perm_merge :
      forall l1 l2 : list A,
        perm (merge l1 l2) (l1 ++ l2);
}.

Coercion A : msArgs >-> Sortclass.

Function ms (args : msArgs) (l : list A) {measure length l} : list A :=
  if small l
  then adhoc l
  else
    let
      (l1, l2) := split l
    in
      merge (ms args l1)
            (ms args l2).
Proof.
  all: intros.
    apply split_spec_r in teq. rewrite teq0 in teq. cbn in teq. assumption.
    apply split_spec_l in teq. rewrite teq0 in teq. cbn in teq. assumption.
Time Defined.


Theorem Sorted_ms :
  forall (args : msArgs) (l : list A),
    Sorted R (ms args l).
Proof.
  intros. functional induction ms args l.
    apply Sorted_adhoc. assumption.
    apply Sorted_merge; assumption.
Qed.

Theorem perm_ms :
  forall (args : msArgs) (l : list A),
    perm (ms args l) l.
Proof.
  intros. functional induction ms args l.
    apply perm_adhoc. assumption.
    rewrite perm_merge, <- (perm_split l l1 l2).
      apply perm_app; assumption.
      assumption.
Qed.

Theorem Permutation_ms :
  forall (args : msArgs) (l : list A),
    Permutation (ms args l) l.
Proof.
  intros. apply perm_Permutation, perm_ms.
Qed.


#[refine]
Instance Sort_ghms
  (args : msArgs) : Sort R :=
{
    sort := ms args
}.
Proof.
  apply Sorted_ms.
  apply Permutation_ms.
Defined.