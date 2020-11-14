Require Import RCCBase.

(* Class Monoid : Type :=
{
    carrier : Type;
    neutr : carrier;
    op : carrier -> carrier -> carrier;
}.*)

Class FTArgs : Type :=
{
    M       : Type;
    neutr   : M;
    op      : M -> M -> M;

    A       : Type;
    measure : A -> M;
}.

Inductive Digit (A : Type) : Type :=
    | D1 : A -> Digit A
    | D2 : A -> A -> Digit A
    | D3 : A -> A -> A -> Digit A
    | D4 : A -> A -> A -> A -> Digit A.

Arguments D1 {A} _.
Arguments D2 {A} _ _.
Arguments D3 {A} _ _ _.
Arguments D4 {A} _ _ _ _.

Inductive Node (M A : Type) : Type :=
    | N2 : M -> A -> A -> Node M A
    | N3 : M -> A -> A -> A -> Node M A.

Arguments N2 {M A} _ _ _.
Arguments N3 {M A} _ _ _ _.

Inductive FingerTree (M A : Type) : Type :=
    | Empty  : FingerTree M A
    | Single : A -> FingerTree M A
    | Deep   : M -> Digit A -> FingerTree M (Node M A) -> Digit A -> FingerTree M A.

Arguments Empty  {M A}.
Arguments Single {M A} _.
Arguments Deep   {M A} _ _ _ _.

(* Function cons {args : FTArgs} (x : A) (t : FingerTree M A) : FingerTree M A :=
match t with
    | Empty        => Single x
    | Single y     => Deep (op (measure x) (measure y)) (D1 x) Empty (D1 y)
    | Deep m l c r =>
        match l with
            | D1 y       => Deep (op (measure x) m) (D2 x y)     c                   r
            | D2 y z     => Deep (op (measure x) m) (D3 x y z)   c                   r
            | D3 y z w   => Deep (op (measure x) m) (D4 x y z w) c                   r
            | D4 y z w q => Deep (m               ) (D2 x y)    (cons (N3 m z w q) c) r
        end
end. *)