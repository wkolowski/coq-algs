Class QSArgs (A : Type) : Type :=
{
    short : list A -> bool;
    adhoc : list A -> list A;
    choosePivot : list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Unset Guard Checking.
Fixpoint qs
  {A : Type} (args : QSArgs A) (l : list A) {struct l} : list A :=
    if short l
    then adhoc l
    else
      let '(pivot, rest) := choosePivot l in
      let '(lt, eq, gt)  := partition pivot rest in
        qs args lt ++ pivot :: eq ++ qs args gt.
Set Guard Checking.



Function uqs
  (A : Type)
  (args : QSArgs A)
  (l : list A)
  {measure length l} : list A :=
match small l with
    | inl l' => adhoc l'
    | inr (h, t) =>
        let
          '(pivot, rest) := choosePivot h t
        in
        let
          '(lo, eq, hi) := partition pivot rest
        in
          uqs args lo ++ pivot :: eq ++ uqs args hi
end.
Proof.
  all: intros;
    apply small_inr, Permutation_length in teq;
    apply choosePivot_spec, Permutation_length in teq1.
  1: apply len_hi in teq2.
  2: apply len_lo in teq2.
  all: cbn in *; omega. Show Proof.
Defined.

Class VerifiedQSArgs (A : Type) : Type :=
{
    args :> QSArgs A;
    rel : A -> A -> Prop;
    Sorted_adhoc :
      forall l1 l2 : list A,
        small l1 = inl l2 -> Sorted rel (adhoc l2);
(*    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm l' (adhoc l');*)
}.

Arguments rel {A} _.
