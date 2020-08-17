Require Import List Nat.
Import ListNotations.

Class MsArgs : Type :=
{
    A : Type;
    split : A -> list A -> list (list A);
    join : list (list A) -> list A;
}.

Coercion A : MsArgs >-> Sortclass.

Unset Guard Checking.
Fixpoint ms (A : MsArgs) (l : list A) {struct l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | h :: t =>
        let ls := split h t in
        let ls' := map (ms A) ls in
          join ls'
end.
Set Guard Checking.

Instance MsArgs_nat : MsArgs :=
{
    A := nat;
    split h t :=
       [ filter (fun x => leb x h) t
       ; [h]
       ; filter (fun x => negb (leb x h)) t
       ];
    join := @concat nat
}.

Compute ms MsArgs_nat [1; 5; 2; 6; 3; 7].

