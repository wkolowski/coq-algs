

Require Import RCCBase.

Module Type Deque.

Parameter Deque : Type -> Type.

Parameter empty :
  forall {A : Type}, Deque A.

Parameter isEmpty :
  forall {A : Type}, Deque A -> bool.

Parameter cons :
  forall {A : Type}, A -> Deque A -> Deque A.

Parameter head :
  forall {A : Type}, Deque A -> option A.

Parameter tail :
  forall {A : Type}, Deque A -> option (Deque A).

Parameter snoc :
  forall {A : Type}, A -> Deque A -> Deque A.

Parameter last :
  forall {A : Type}, Deque A -> option A.

Parameter init :
  forall {A : Type}, Deque A -> option (Deque A).

(* Properties of [isEmpty]. *)
Parameter isEmpty_empty :
  forall A : Type, isEmpty (@empty A) = true.

Parameter isEmpty_cons :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty (cons x d) = false.

Parameter isEmpty_head_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true <-> head d = None.

Parameter isEmpty_head_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = false <-> exists h : A, head d = Some h.

Parameter isEmpty_tail_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = false <-> exists d' : Deque A, tail d = Some d'.

Parameter isEmpty_tail_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true <-> tail d = None.

Parameter isEmpty_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty (snoc x d) = false.

Parameter isEmpty_last_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true <-> last d = None.

Parameter isEmpty_last_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = false <-> exists h : A, last d = Some h.

Parameter isEmpty_init_false :
  forall (A : Type) (d : Deque A),
    isEmpty d = false <-> exists d' : Deque A, init d = Some d'.

Parameter isEmpty_init_true :
  forall (A : Type) (d : Deque A),
    isEmpty d = true <-> init d = None.

(* Properties of [head]. *)
Parameter head_empty :
  forall A : Type, head (@empty A) = None.

Parameter head_cons :
  forall (A : Type) (x : A) (d : Deque A),
    head (cons x d) = Some x.

Parameter head_snoc_false :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = false -> head (snoc x d) = head d.

Parameter head_snoc_true :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = true -> head (snoc x d) = Some x.

(* Properties of [last]. *)
Parameter last_empty :
  forall A : Type, last (@empty A) = None.

Parameter last_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    last (snoc x d) = Some x.

Parameter last_cons_false :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = false -> last (cons x d) = last d.

Parameter last_cons_true :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = true -> last (cons x d) = Some x.

(* Properties of [tail]. *)
Parameter tail_empty :
  forall A : Type, tail (@empty A) = None.

Parameter tail_cons :
  forall (A : Type) (x : A) (d : Deque A),
    tail (cons x d) = Some d.

(*Require Import CoqMTL.#[refine]
Instances.Option.

Parameter tail_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = false -> tail (snoc x d) = fmap_Option (snoc x) (tail d).*)

(* Properties of [init]. *)
Parameter init_empty :
  forall A : Type, init (@empty A) = None.

Parameter init_snoc :
  forall (A : Type) (x : A) (d : Deque A),
    init (snoc x d) = Some d.

(*Parameter init_cons :
  forall (A : Type) (x : A) (d : Deque A),
    isEmpty d = false -> init (cons x d) = fmap_Option (cons x) (init d).*)


(*Hint Rewrite isEmpty_empty isEmpty_snoc last_empty last_singl
             tail_empty tail_singl : Deque.*)

End Deque.