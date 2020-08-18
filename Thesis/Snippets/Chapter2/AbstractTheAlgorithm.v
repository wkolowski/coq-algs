Require Import List Arith.
Import ListNotations.

Module FirstTry.

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

Instance QS_nat : QSArgs nat :=
{
    short l :=
      match l with
          | [] => true
          | _ => false
      end;
    adhoc _ := [];
    choosePivot l :=
      match l with
          | [] => (42, []) (* Wut? *)
          | h :: t => (h, t)
      end;
    partition p l :=
      (filter (fun x => leb x p) l,
       [],
       filter (fun x => negb (leb x p)) l)
}.

Compute qs QS_nat [5; 4; 3; 2; 1; 0].
(* ===> = [0; 1; 2; 3; 4; 5]
        : list nat *)

End FirstTry.

Class QSArgs (A : Type) : Type :=
{
    short : list A -> option (A * list A);
    adhoc : list A -> list A;
    choosePivot : A -> list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Unset Guard Checking.
Fixpoint qs
  {A : Type} (args : QSArgs A) (l : list A) {struct l} : list A :=
    match short l with
        | None => adhoc l
        | Some (h, t) =>
            let '(pivot, rest) := choosePivot h t in
            let '(lt, eq, gt)  := partition pivot rest in
              qs args lt ++ pivot :: eq ++ qs args gt
    end.
Set Guard Checking.

Instance QS_nat : QSArgs nat :=
{
    short l :=
      match l with
          | [] => None
          | h :: t => Some (h, t)
      end;
    adhoc _ := [];
    choosePivot h t := (h, t);
    partition p l :=
      (filter (fun x => leb x p) l,
       [],
       filter (fun x => negb (leb x p)) l)
}.

Compute qs QS_nat [5; 4; 3; 2; 1; 0].
(* ===> = [0; 1; 2; 3; 4; 5]
        : list nat *)


(*
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
*)

Require Import ImprovingPatchworkDefinitions.
Import M3.

Module wuud.

Class QSArgs (A : Type) : Type :=
{
    short : list A -> list A + A * list A;
    adhoc : list A -> list A;
    choosePivot : A * list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Class VerifiedQSArgs (A : Type) : Type :=
{
    args :> QSArgs A;
    rel : A -> A -> Prop;
    Sorted_adhoc :
      forall l1 l2 : list A,
        short l1 = inl l2 -> Sorted rel (adhoc l2);
(*    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm l' (adhoc l');*)
}.

End wuud.

Module wuud2.

Class QSArgs : Type :=
{
    A : Type;
    short : list A -> list A + A * list A;
    adhoc : list A -> list A;
    choosePivot : A * list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Class VerifiedQSArgs : Type :=
{
    args :> QSArgs;
    rel : A -> A -> Prop;
    Sorted_adhoc :
      forall l1 l2 : list A,
        short l1 = inl l2 -> Sorted rel (adhoc l2);
(*    adhoc_perm :
      forall l l' : list A,
        small l = inl l' -> perm l' (adhoc l');*)
}.

Print VerifiedQSArgs.

Arguments rel {A} _.
