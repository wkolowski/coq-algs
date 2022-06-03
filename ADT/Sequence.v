From CoqAlgs Require Import Base.

(** A LIFO sequence. The most obvious implementation is intended to be a
    list. *)
Module Type Sequence.

Parameter Seq : Type -> Type.

Parameter empty :
  forall {A : Type}, Seq A.

Parameter cons :
  forall {A : Type}, A -> Seq A -> Seq A.

Parameter uncons :
  forall {A : Type}, Seq A -> option (A * Seq A).

Parameter head :
  forall {A : Type}, Seq A -> option A.

Parameter tail :
  forall {A : Type}, Seq A -> option (Seq A).

Parameter uncons_head_tail :
  forall {A : Type} (s : Seq A),
    uncons s =
    match head s, tail s with
        | None, _ => None
        | _, None => None
        | Some h, Some t => Some (h, t)
    end.

Parameter head_cons :
  forall {A : Type} (h : A) (t : Seq A),
    head (cons h t) = Some h.

Parameter tail_cons :
  forall {A : Type} (h : A) (t : Seq A),
    tail (cons h t) = Some t.

Parameter uncons_cons :
  forall {A : Type} (h : A) (t : Seq A),
    uncons (cons h t) = Some (h, t).

End Sequence.

Module Type Sequence_with_len (Sequence : Sequence).

Import Sequence.

Parameter len :
  forall {A : Type}, Seq A -> nat.

Parameter len_cons :
  forall {A : Type} (h : A) (t : Seq A),
    len (cons h t) = 1 + len t.

Parameter len_uncons :
  forall {A : Type} (h : A) (s t : Seq A),
    uncons s = Some (h, t) -> len s = 1 + len t.

Function foldr
  {A B : Type} (x : A) (f : B -> A -> A) (s : Seq B) {measure len s}: A :=
match uncons s with
    | None => x
    | Some (h, t) => f h (foldr x f t)
end.
Proof.
  intros. apply len_uncons in teq. rewrite teq. apply le_n.
Defined.

Arguments foldr {x x0} _ _ _.

Definition toList {A : Type} (s : Seq A) : list A :=
  foldr [] (fun h t => h :: t) s.

End Sequence_with_len.