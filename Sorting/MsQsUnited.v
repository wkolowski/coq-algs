Require Import List Nat.
Import ListNotations.

Class MsArgs : Type :=
{
    A : Type;

    small : list A -> option (A * list A);
    adhoc : list A -> list A;

    split : A -> list A -> list (list A);
    join : list (list A) -> list A;
}.

Coercion A : MsArgs >-> Sortclass.

Unset Guard Checking.
Fixpoint qms (A : MsArgs) (l : list A) {struct l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | h :: t =>
        let ls := split h t in
        let ls' := map (qms A) ls in
          join ls'
end.

Fixpoint qms' (A : MsArgs) (l : list A) {struct l} : list A :=
match small l with
    | None        => adhoc l
    | Some (h, t) => join (map (qms' A) (split h t))
end.
Set Guard Checking.

#[export]
Instance MsArgs_nat : MsArgs :=
{
    A := nat;

    small l :=
      match l with
          | [] => None
          | h :: t => Some (h, t)
      end;

    adhoc := id;

    split h t :=
       [ filter (fun x => leb x h) t
       ; [h]
       ; filter (fun x => negb (leb x h)) t
       ];

    join := @concat nat
}.

(* Compute qms MsArgs_nat [3; 2; 1; 0]. *)