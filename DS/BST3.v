Require Import BTree.

(** The [Ok]-based definition is inherently wrong, because it doesn't relate vertices
    connected by a zig-zag path. This contrasts with a similar approach to defining
    [Sorted], which is correct with an [Ok]-based approach, even though it differs a
    little from the [All]-based definition (but they are equivalent when the relation
    is transitive. *)

Inductive Ok {A : Type} (R : A -> A -> Prop) (x : A) : BTree A -> Prop :=
    | Ok_empty : Ok R x empty
    | Ok_node  :
        forall (y : A) (l r : BTree A),
          R y x -> Ok R x (node y l r).

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison}
  : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          Ok (fun x y : A => cmp x y = Lt) v l ->
          Ok (fun x y : A => cmp x y = Gt) v r ->
            isBST l -> isBST r -> isBST (node v l r).

Arguments isBST {A} _ _.

Definition Bad :=
  node 5
    (node 3
      empty
      (node 6 empty empty))
    empty.

Lemma isBST_Bad : isBST Nat.compare Bad.
Proof.
  repeat constructor.
Qed.