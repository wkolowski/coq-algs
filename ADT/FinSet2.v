Require Import CoqAlgs.Base.

Module Type FinSet.

Parameters E S : Type.

Parameter empty : S.

Parameter insert : E -> S -> S.

Parameter remove : E -> S -> S.

Parameter isEmpty : S -> bool.

Parameter member : E -> S -> bool.

(** Properties of [member]. *)

Parameter member_insert :
  forall (x : E) (s : S),
    member x (insert x s) = true.

Parameter member_remove :
  forall (x : E) (s : S),
    member x (remove x s) = false.

Parameter member_insert' :
  forall (x y : E) (s : S),
    x <> y -> member x (insert y s) = member x s.

Parameter member_remove' :
  forall (x y : E) (s : S),
    x <> y -> member x (remove y s) = member x s.

(** Definition of equivalent sets. *)

Definition equiv (s1 s2 : S) : Prop :=
  forall x : E, member x s1 = member x s2.

Parameter remove_insert_equiv :
  forall (x : E) (s : S),
    equiv (remove x (insert x s)) s.

End FinSet.