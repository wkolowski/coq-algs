Require Export CoqAlgs.Base.
Require Import Data.BTree.
Require Import Ord.
Require Import Sorting.Sort.

(** * Definitions of the bst property. *)

Inductive isBST2
  {A : Type} {cmp : A -> A -> comparison} : BTree A -> Prop :=
    | isBST2_empty : isBST2 empty
    | isBST2_node :
        forall (v : A) (l r : BTree A),
          All (fun x : A => cmp x v = Lt) l ->
          All (fun x : A => cmp x v = Gt) r ->
            isBST2 l -> isBST2 r -> isBST2 (node v l r).

Arguments isBST2 {A} _ _.

Global Hint Constructors All isBST2 : core.

Ltac isBST2 :=
repeat match goal with
    |                          |- isBST2 _ empty  => constructor
    |                          |- isBST2 _ _ -> _ => intro
    | H : isBST2 _ empty        |- _              => clear H
    | H : isBST2 _ (node _ _ _) |- _              => inv H
end; auto.

Ltac isBST2' :=
repeat match goal with
    |                           |- isBST2 _ _      => constructor; auto
    |                           |- isBST2 _ _ -> _ => intro
    | H : isBST2 _ empty        |- _               => clear H
    | H : isBST2 _ (node _ _ _) |- _               => inv H
end; auto.

(** * BST functions *)

Fixpoint partition
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A)
  : BTree A * bool * BTree A :=
match t with
    | empty      => (empty, false, empty)
    | node v l r =>
        match cmp x v with
            | Lt =>
                match partition cmp x l with
                    | (l1, b, l2) => (l1, b, node v l2 r)
                end
            | Eq => (l, true, r)
            | Gt =>
                match partition cmp x r with
                    | (r1, b, r2) => (node v l r1, b, r2)
                end
        end
end.

Functional Scheme partition_ind := Induction for partition Sort Prop.

Function union {A : Type} (cmp : A -> A -> comparison) (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => t2
    | node v1 l1 r1 =>
        match partition cmp v1 t2 with
            | (l, _, r) => node v1 (union cmp l1 l) (union cmp r1 r)
        end
end.

Function intersection {A : Type} (cmp : A -> A -> comparison) (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => empty
    | node v1 l1 r1 =>
        match partition cmp v1 t2 with
            | (l, b, r)  =>
                let l' := intersection cmp l1 l in
                let r' := intersection cmp r1 r in
                  if b
                  then node v1 l' r'
                  else union cmp l' r'
        end
end.

Function difference {A : Type} (cmp : A -> A -> comparison) (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => empty
    | node v1 l1 r1 =>
        let '(l, b, r) := partition cmp v1 t2 in
        let l' := difference cmp l1 l in
        let r' := difference cmp r1 r in
          if b
          then union cmp l' r'
          else
            node v1 l' r'
end.

Definition insert
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
    union cmp (singleton x) t.

Definition remove
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
    difference cmp t (singleton x).

Definition test : BTree nat :=
  node 50
    (node 25
      (node 10 empty empty)
      (node 40 empty empty))
    (node 75
      (node 60 empty empty)
      (node 100 empty empty)).

Definition test' : BTree nat :=
  node 100
    (node 75
      (node 60
        (node 25
          (node 10 empty empty)
          (node 40 empty empty))
        empty)
      empty)
    empty.

(*
Compute union Nat.compare test test'.
Compute intersection Nat.compare test test'.
Compute difference Nat.compare test test'.
Compute insert Nat.compare 123 test.
Compute remove Nat.compare 50 test.
*)

(** * Properties of partition *)

Lemma partition_spec :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) ->
      isBST2 cmp t ->
        All (fun x : A => cmp x v = Lt) t1 /\
        All (fun x : A => cmp x v = Gt) t2.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; isBST2.
    trich.
    edestruct IHp; eauto. repeat constructor; auto.
      trich.
      induction H4; constructor; isBST2. trich.
    edestruct IHp; eauto. split; repeat constructor; auto.
      trich.
      induction H3; constructor; isBST2. trich.
Qed.

Lemma All_partition :
  forall {A : Type} {P : A -> Prop} {cmp : A -> A -> comparison} {v : A} {t l r : BTree A} {b : bool},
    partition cmp v t = (l, b, r) ->
      All P t -> All P l /\ All P r.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; inv 1; edestruct IHp; eauto.
Qed.

Lemma isBST2_partition :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t l r : BTree A} {b : bool},
    partition cmp v t = (l, b, r) ->
      isBST2 cmp t -> isBST2 cmp l /\ isBST2 cmp r.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; isBST2.
    destruct (All_partition e1 H3). edestruct IHp; eauto.
    destruct (All_partition e1 H4). edestruct IHp; eauto.
Qed.

Lemma All_union :
  forall {A : Ord} {P : A -> Prop} {cmp : A -> A -> comparison} {t1 t2 : BTree A},
    All P t1 -> All P t2 -> All P (union cmp t1 t2).
Proof.
  intros until t2.
  functional induction union cmp t1 t2;
  inv 1.
  intro. destruct (All_partition e0 H). constructor; auto.
Qed.

Lemma isBST2_union :
  forall {A : Ord} (t1 t2 : BTree A),
    isBST2 cmp t1 -> isBST2 cmp t2 -> isBST2 cmp (union cmp t1 t2).
Proof.
  intros until t2.
  functional induction union cmp t1 t2;
  isBST2.
  {
    destruct (isBST2_partition e0 H0).
    destruct (partition_spec e0); auto.
    isBST2'; apply All_union; auto.
  }
Qed.

Lemma All_intersection :
  forall {A : Ord} {P : A -> Prop} {t1 t2 : BTree A},
    isBST2 cmp t2 ->
      All P t1 -> All P t2 ->
        All P (intersection cmp t1 t2).
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  inv 2; intro.
    destruct (isBST2_partition e0), (partition_spec e0); auto. constructor.
      assumption.
      apply IHb; auto. admit.
      apply IHb0; auto. admit.
    destruct (isBST2_partition e0), (partition_spec e0); auto. apply All_union.
      apply IHb; auto. admit.
      apply IHb0; auto. admit.
Admitted.

Lemma All_intersection_Lt :
  forall {A : Ord} {P : A -> Prop} {t1 t2 : BTree A} {v : A},
    isBST2 cmp t2 ->
      All (fun x : A => cmp x v = Lt) t1 ->
      All (fun x : A => cmp x v = Lt) t2 ->
        All (fun x : A => cmp x v = Lt) (intersection cmp t1 t2).
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  inv 2; intro.
    destruct (isBST2_partition e0), (partition_spec e0); auto. constructor.
      assumption.
      apply IHb; auto. clear e0 IHb IHb0. induction H3; constructor; isBST2; trich.
      admit.
    destruct (isBST2_partition e0), (partition_spec e0); auto. apply All_union.
      apply IHb; auto. clear e0 IHb IHb0. induction H3; constructor; isBST2; trich.
      clear IHb IHb0. induction H0; inv e0; isBST2; intros.
        admit.
        trich.
          destruct (partition cmp v1 l), p; inv H9.
Admitted.

Lemma isBST_intersection :
  forall {A : Ord} {t1 t2 : BTree A},
    isBST2 cmp t1 -> isBST2 cmp t2 ->
      isBST2 cmp (intersection cmp t1 t2).
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  isBST2.
    destruct (isBST2_partition e0), (partition_spec e0); auto. constructor.
      apply All_intersection; auto.
      apply All_intersection; auto.
      apply IHb; auto.
      apply IHb0; auto.
    destruct (isBST2_partition e0); auto. apply isBST2_union.
      apply IHb; auto.
      apply IHb0; auto.
Qed.

Lemma All_difference :
  forall {A : Ord} {P : A -> Prop} {t1 t2 : BTree A},
    isBST2 cmp t2 ->
      All P t1 -> All P t2 ->
        All P (difference cmp t1 t2).
Proof.
  intros until t2.
  functional induction difference cmp t1 t2;
  inv 2; intro.
    destruct (isBST2_partition e0), (partition_spec e0); auto. apply All_union.
      apply IHb; auto. admit.
      apply IHb0; auto. admit.
    destruct (isBST2_partition e0), (partition_spec e0); auto. constructor.
      assumption.
      apply IHb; auto. admit.
      apply IHb0; auto. admit.
Admitted.

Lemma isBST2_difference :
  forall {A : Ord} {t1 t2 : BTree A},
    isBST2 cmp t1 -> isBST2 cmp t2 ->
      isBST2 cmp (difference cmp t1 t2).
Proof.
  intros until t2.
  functional induction difference cmp t1 t2;
  isBST2.
    destruct (isBST2_partition e0); auto. apply isBST2_union.
      apply IHb; auto.
      apply IHb0; auto.
    destruct (isBST2_partition e0), (partition_spec e0); auto. constructor.
      apply All_difference; auto.
      apply All_difference; auto.
      apply IHb; auto.
      apply IHb0; auto.
Qed.