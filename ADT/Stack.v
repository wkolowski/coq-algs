From CoqAlgs Require Import Base.

Module Type StackSpec.

Parameter Stack : Type -> Type.

(** Basic stack-building operations. *)

Parameter empty :
  forall {A : Type}, Stack A.

Parameter push :
  forall {A : Type}, A -> Stack A -> Stack A.

Parameter top :
  forall {A : Type}, Stack A -> option A.

Parameter pop :
  forall {A : Type}, Stack A -> option (Stack A).

Definition unpush {A : Type} (s : Stack A) : option (A * Stack A) :=
match top s, pop s with
    | None, _ => None
    | _, None => None
    | Some x, Some s' => Some (x, s')
end.

(** Secondary operations. *)
Parameter isEmpty :
  forall {A : Type}, Stack A -> bool.

Parameter size :
  forall {A : Type}, Stack A -> nat.

Parameter fmap :
  forall {A B : Type}, (A -> B) -> Stack A -> Stack B.

(** Properties of the basic operations. *)

Parameter top_empty :
  forall {A : Type}, top (@empty A) = None.

Parameter top_push :
  forall {A : Type} (x : A) (s : Stack A),
    top (push x s) = Some x.

Parameter pop_empty :
  forall {A : Type}, pop (@empty A) = None.

Parameter pop_push :
  forall {A : Type} (x : A) (s : Stack A),
    pop (push x s) = Some s.

(** Properties of [isEmpty]. *)

Parameter isEmpty_empty :
  forall {A : Type}, isEmpty (@empty A) = true.

Parameter isEmpty_push :
  forall {A : Type} (x : A) (s : Stack A),
    isEmpty (push x s) = false.

Parameter isEmpty_top :
  forall {A : Type} (s : Stack A),
    isEmpty s = true -> top s = None.

Parameter isEmpty_pop :
  forall {A : Type} (s : Stack A),
    isEmpty s = true -> pop s = None.

(** Properties of [size]. *)

Parameter size_empty :
  forall {A : Type}, size (@empty A) = 0.

Parameter size_push :
  forall {A : Type} (x : A) (s : Stack A),
    size (push x s) = 1 + size s.

End StackSpec.