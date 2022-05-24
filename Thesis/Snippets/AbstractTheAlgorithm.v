Require Export SpecifyTheProblem.

(** * Top-down is better than bottom-up *)

Module FirstTry.

Class QSArgs (T : Type) : Type :=
{
    short : list T -> bool;
    adhoc : list T -> list T;
    choosePivot : list T -> T * list T;
    partition : T -> list T -> list T * list T * list T;
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

(** * User experience: concerete algorithm as a sanity check *)

#[export] Instance QS_nat : QSArgs nat :=
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

Module SecondTry.

Class QSArgs (T : Type) : Type :=
{
    short : list T -> option (T * list T);
    adhoc : list T -> list T;
    choosePivot : T -> list T -> T * list T;
    partition : T -> list T -> list T * list T * list T;
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

#[export] Instance QSA_nat : QSArgs nat :=
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

Compute qs QSA_nat [5; 4; 3; 2; 1; 0].
(* ===> = [0; 1; 2; 3; 4; 5]
        : list nat *)

End SecondTry.

(** * Remarks on (un)bundling and (lack of) sharing *)

Class QSArgs : Type :=
{
    T : Type;
    short : list T -> option (T * list T);
    adhoc : list T -> list T;
    choosePivot : T -> list T -> T * list T;
    partition : T -> list T -> list T * list T * list T;
}.

Coercion T : QSArgs >-> Sortclass.

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

#[export] Instance QSA_nat : QSArgs :=
{
    T := nat;
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

Compute qs QSA_nat [5; 4; 3; 2; 1; 0].
(* ===> = [0; 1; 2; 3; 4; 5]
        : list QSA_nat *)