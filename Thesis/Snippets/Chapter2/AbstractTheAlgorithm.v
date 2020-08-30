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

Module Unbundled.

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

End Unbundled.

Module Bundled.

Class QSArgs : Type :=
{
    A : Type;
    short : list A -> option (A * list A);
    adhoc : list A -> list A;
    choosePivot : A -> list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Coercion A : QSArgs >-> Sortclass.

Unset Guard Checking.
Fixpoint qs (A : QSArgs) (l : list A) {struct l} : list A :=
match short l with
    | None => adhoc l
    | Some (h, t) =>
        let '(pivot, rest) := choosePivot h t in
        let '(lt, eq, gt)  := partition pivot rest in
          qs A lt ++ pivot :: eq ++ qs A gt
end.
Set Guard Checking.

End Bundled.

Class QSArgs : Type :=
{
    A : Type;
    short : list A -> option (A * list A);
    adhoc : list A -> list A;
    choosePivot : A -> list A -> A * list A;
    partition : A -> list A -> list A * list A * list A;
}.

Coercion A : QSArgs >-> Sortclass.

Inductive QSDom (A : QSArgs) : list A -> Type :=
    | Short :
        forall l : list A, short l = None -> QSDom A l
    | Long :
        forall {l : list A},
          forall {h : A} {t : list A},
            short l = Some (h, t) ->
          forall (pivot : A) {rest : list A},
            choosePivot h t = (pivot, rest) ->
          forall (eq : list A) {lt gt : list A},
            partition pivot rest = (lt, eq, gt) ->
          QSDom A lt -> QSDom A gt -> QSDom A l.

Arguments Short {A0 l}.

Fixpoint qs {A : QSArgs} {l : list A} (d : QSDom A l) : list A :=
match d with
    | Short _ => adhoc l
    | Long _ _ pivot _ eq _ ltd gtd => qs ltd ++ pivot :: eq ++ qs gtd
end.

Unset Guard Checking.
Definition QSDom_all :
  forall (A : QSArgs) (l : list A), QSDom A l :=
    fun A : QSArgs =>
      fix f (l : list A) : QSDom A l := f l.
Set Guard Checking.

Instance QSArgs_nat : QSArgs :=
{
    A := nat;
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

Compute qs (QSDom_all QSArgs_nat [4; 3; 2; 1]).