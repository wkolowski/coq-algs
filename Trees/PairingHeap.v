Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export LinDec.
Require Import Sorting.Sort.

Set Implicit Arguments.

Inductive Tree (A : Type) : Type :=
    | E : Tree A
    | T : A -> list (Tree A) -> Tree A.

Arguments E [A].
Arguments T [A] _ _.

Fixpoint Tree_rect'
  (A : Type) (P : Tree A -> Type) (Q : list (Tree A) -> Type)
  (HE : P E)
  (Hnil : Q [])
  (Hcons : forall (h : Tree A) (t : list (Tree A)), P h -> Q t -> Q (h :: t))
  (Htrans : forall (x : A) (l : list (Tree A)), Q l -> P (T x l))
  (t : Tree A) : P t.
Proof.
  destruct t.
    assumption.
    apply Htrans. induction l as [| h t].
      assumption.
      apply Hcons.
        eapply Tree_rect'; eauto.
        assumption.
Defined.

Theorem Tree_ind_proper
  (A : Type) (P : Tree A -> Prop)
  (HE : P E)
  (HT : forall (x : A) (l : list (Tree A)), Forall P l -> P (T x l))
  (t : Tree A) : P t.
Proof.
  induction t using Tree_rect' with (Q := Forall P); auto.
Qed.

Definition PairingHeap (A : LinDec) : Type := Tree A.

Definition empty {A : LinDec} : PairingHeap A := E.

Definition singleton {A : LinDec} (x : A) : PairingHeap A := T x [].

Definition findMin {A : LinDec} (h : PairingHeap A) : option A :=
match h with
    | E => None
    | T m _ => Some m
end.

Definition merge
  {A : LinDec} (h1 h2 : PairingHeap A) : PairingHeap A :=
match h1, h2 with
    | E, _ => h2
    | _, E => h1
    | T m1 l1, T m2 l2 =>
        if m1 <=? m2
        then T m1 (h2 :: l1)
        else T m2 (h1 :: l2)
end.

Definition insert
  {A : LinDec} (x : A) (h : PairingHeap A) : PairingHeap A :=
    merge (singleton x) h.

Function mergePairs {A : LinDec} (hs : list (PairingHeap A))
  : PairingHeap A :=
match hs with
    | [] => E
    | [h] => h
    | h1 :: h2 :: hs' => merge (merge h1 h2) (mergePairs hs')
end.

Definition deleteMin {A : LinDec} (h : PairingHeap A)
  : PairingHeap A :=
match h with
    | E => E
    | T _ hs => mergePairs hs
end.