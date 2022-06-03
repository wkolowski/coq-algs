Require Import List.
Import ListNotations.

From CoqAlgs Require Export Sorting.Sort.

Set Implicit Arguments.

Class ISArgs : Type :=
{
    A : Type;
    S : Type;

    empty  : S;
    insert : A -> S -> S;

    toList : S -> list A;

    R : A -> A -> Prop;

    Sorted_toList :
      forall s : S, Sorted R (toList s);

    countS : (A -> bool) -> S -> nat;

    countS_empty :
      forall p : A -> bool,
        countS p empty = 0;

    countS_insert :
      forall (p : A -> bool) (x : A) (s : S),
        countS p (insert x s) =
          (if p x then 1 else 0) + countS p s;

    countS_toList :
      forall (p : A -> bool) (s : S),
        countS p s = count p (toList s);
}.

Fixpoint fromList (args : ISArgs) (l : list A) : S :=
match l with
    | [] => empty
    | h :: t => insert h (fromList args t)
end.

Definition insSort (args : ISArgs) (l : list A) : list A := toList (fromList args l).

Lemma countS_fromList :
  forall (args : ISArgs) (p : A -> bool) (l : list A),
    countS p (fromList args l) = count p l.
Proof.
  induction l as [| h t]; cbn.
    rewrite countS_empty. reflexivity.
    rewrite countS_insert, IHt. reflexivity.
Qed.

Lemma perm_insSort :
  forall (args : ISArgs) (l : list A),
    perm (insSort args l) l.
Proof.
  unfold perm, insSort. intros.
  rewrite <- countS_toList, <- countS_fromList.
  reflexivity.
Qed.

