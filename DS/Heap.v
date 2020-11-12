Require Export Tree.

Inductive isHeap {A : Type} (R : A -> A -> Prop) : Tree A -> Prop :=
    | isHeap_E : isHeap R E
    | isHeap_T :
        forall (v : A) (l : list (Tree A)),
          Forall (fun t : Tree A => forall x : A, Elem x t -> R v x) l ->
          Forall (isHeap R) l ->
            isHeap R (T v l).

Hint Constructors isHeap : core.

Ltac isHeap :=
repeat match goal with
    | H : isHeap _ E        |- _ => clear H
    | H : isHeap _ (T _ _)  |- _ => inv H
    | H : Forall _ []       |- _ => clear H
    | H : Forall _ (_ :: _) |- _ => inv H
    |                       |- isHeap _ E      => constructor
    |                       |- isHeap _ _ -> _ => intro
    |                       |- Forall _ _ -> _  => intro
end; auto.

Ltac isHeap' :=
repeat match goal with
    | H : isHeap _ E        |- _ => clear H
    | H : isHeap _ (T _ _)  |- _ => inv H
    | H : Forall _ []       |- _ => clear H
    | H : Forall _ (_ :: _) |- _ => inv H
    |                       |- isHeap _ E       => constructor
    |                       |- isHeap _ (T _ _) => constructor
    |                       |- Forall _ []       => constructor
    |                       |- Forall _ (_ :: _) => constructor
    |                       |- isHeap _ _ -> _  => intro
    |                       |- Forall _ _ -> _  => intro
end; eauto.

Inductive OK {A : Type} (R : A -> A -> Prop) (x : A) : Tree A -> Prop :=
    | OK_E : OK R x E
    | OK_N :
        forall (v : A) (l : list (Tree A)),
          R x v -> OK R x (T v l).

Inductive isHeap2 {A : Type} (R : A -> A -> Prop) : Tree A -> Prop :=
    | isHeap2_E : isHeap2 R E
    | isHeap2_T :
        forall (v : A) (l : list (Tree A)),
          Forall (fun t : Tree A => OK R v t) l ->
            Forall (isHeap2 R) l -> isHeap2 R (T v l).

Hint Constructors isHeap OK isHeap2 : core.

Ltac isHeap2 :=
repeat match goal with
    | H : isHeap2 _ E       |- _ => clear H
    | H : isHeap2 _ (T _ _) |- _ => inv H
    | H : Forall _ []       |- _ => clear H
    | H : Forall _ (_ :: _) |- _ => inv H
    |                       |- isHeap2 _ E      => constructor
    |                       |- isHeap2 _ _ -> _ => intro
    |                       |- Forall _ _ -> _  => intro
end; auto.

Ltac isHeap2' :=
repeat match goal with
    | H : isHeap2 _ E       |- _ => clear H
    | H : isHeap2 _ (T _ _) |- _ => inv H
    | H : Forall _ []       |- _ => clear H
    | H : Forall _ (_ :: _) |- _ => inv H
    |                       |- isHeap2 _ E       => constructor
    |                       |- isHeap2 _ (T _ _) => constructor
    |                       |- Forall _ []       => constructor
    |                       |- Forall _ (_ :: _) => constructor
    |                       |- isHeap2 _ _ -> _  => intro
    |                       |- Forall _ _ -> _  => intro
end; eauto.

Lemma isHeap_isEmpty :
  forall (A : Type) (R : A -> A -> Prop) (t : Tree A),
    isEmpty t = true -> isHeap R t.
Proof. Tree_ind. Qed.