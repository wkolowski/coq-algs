Require Import RCCBase.

Require Import TrichDec.

Module Type FinSet.

Parameter S : TrichDec -> Type.

Parameter empty :
  forall {A : TrichDec}, S A.

Parameter isEmpty :
  forall {A : TrichDec}, S A -> bool.

Parameter insert :
  forall {A : TrichDec}, A -> S A -> S A.

Parameter remove :
  forall {A : TrichDec}, A -> S A -> S A.

Parameter member :
  forall {A : TrichDec}, A -> S A -> bool.

(** Properties of [member]. *)

Parameter member_insert :
  forall (A : TrichDec) (x : A) (s : S A),
    member x (insert x s) = true.

Parameter member_insert' :
  forall (A : TrichDec) (x y : A) (s : S A),
    member x (insert y s) =
    if x =? y then true else member x s.

Parameter member_remove :
  forall (A : TrichDec) (x : A) (s : S A),
    member x (remove x s) = false.

Parameter member_remove' :
  forall (A : TrichDec) (x y : A) (s : S A),
    member x (remove y s) =
    if x =? y then false else member x s.

(** Definition of equivalent sets. *)

Definition equiv {A : TrichDec} (s1 s2 : S A) : Prop :=
  forall x : A, member x s1 = member x s2.

Parameter remove_insert_equiv :
  forall (A : TrichDec) (x : A) (s : S A),
    equiv (remove x (insert x s)) s.

End FinSet.