Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Inductive isBST
  {A : Type} {cmp : A -> A -> comparison}
  : BTree A -> Prop :=
    | isBST_empty : isBST empty
    | isBST_node :
        forall (v : A) (l r : BTree A),
          isBST l -> (forall x : A, Elem x l -> cmp x v = Lt) ->
          isBST r -> (forall x : A, Elem x r -> cmp x v = Gt) ->
            isBST (node v l r).

Arguments isBST {A} _ _.

Hint Constructors Elem isBST : core.

Record BST {A : Type} (cmp : A -> A -> comparison) : Type :=
{
    tree :> BTree A;
    prop : isBST cmp tree
}.

Function insert
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => node x empty empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (insert cmp x l) r
            | Eq => node x l r
            | Gt => node v l (insert cmp x r)
        end
end.

Function removeMin
  {A : Type} (cmp : A -> A -> comparison)
  (t : BTree A) : option (A * BTree A) :=
match t with
    | empty => None
    | node x l r =>
        match removeMin cmp l with
            | None => Some (x, r)
            | Some (m, l') => Some (m, node x l' r)
        end
end.

Function remove
  {A : Type} (cmp : A -> A -> comparison)
  (x : A) (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        match cmp x v with
            | Lt => node v (remove cmp x l) r
            | Gt => node v l (remove cmp x r)
            | Eq =>
                match removeMin cmp l with
                    | None => r
                    | Some (m, l') => node m l' r
                end
        end
end.

Function elem
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A) : bool :=
match t with
    | empty => false
    | node v l r =>
        match cmp x v with
            | Lt => elem cmp x l
            | Eq => true
            | Gt => elem cmp x r
        end
end.

(*
Class TotalPreordDec : Type :=
{
    carrier : Type;
    lt : carrier -> carrier -> Prop;
    lt_antirefl :
      forall x : carrier, ~ lt x x;
    lt_trans :
      forall x y z : carrier, lt x y -> lt y z -> lt x z;
    
}.
*)
(*
Class cmp_spec {A : Type} (cmp : A -> A -> comparison) : Prop :=
{
    cmp_spec1 :
      forall x y : A, cmp x y = Eq -> x = y;
    cmp_spec2 :
      forall x y : A, cmp x y = Lt <-> cmp y x = Gt;
    cmp_spec3 :
      forall x : A, cmp x x = Eq;
}.
*)
Class cmp_spec (A : Type) : Type :=
{
    cmpr : A -> A -> comparison;
    cmp_spec1 :
      forall x y : A, cmpr x y = Eq -> x = y;
    cmp_spec2 :
      forall x y : A, cmpr x y = Lt <-> cmpr y x = Gt;
    cmp_spec3 :
      forall x : A, cmpr x x = Eq;
}.

Coercion cmpr : cmp_spec >-> Funclass.

(*
Class BSTOrd : Type :=
{
    carrier : Type;
    cmpr : carrier -> carrier -> comparison;
    spec : cmp_spec cmpr;
}.
*)

Hint Extern 0 =>
  intros;
match goal with
    | H : Elem _ empty |- _ => inversion H
    | H : isBST _ (node _ ?l _) |- isBST _ ?l => inversion H; auto
    | H : isBST _ (node _ _ ?r) |- isBST _ ?r => inversion H; auto
end
  : core.

Lemma Elem_insert :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp y t) -> x = y \/ Elem x t.
Proof.
  intros A cmp x y t H.
  functional induction (insert cmp y t).
    inversion 1; subst; auto.
    inversion H; subst. inversion 1; firstorder.
    inversion 1; firstorder.
    inversion H; subst. inversion 1; subst; firstorder.
Qed.

Lemma Elem_removeMin :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x m : A) (t t' : BTree A),
      isBST cmp t -> removeMin cmp t = Some (m, t') ->
        Elem x t <-> x = m \/ x <> m /\ Elem x t'.
Proof.
  intros A cmp x m t t' H.
  revert x m t' H.
  functional induction (removeMin cmp t); intros.
    inversion H0.
    inversion H0; subst. split; inversion 1; subst.
      left. reflexivity.
      destruct l; cbn in *.
        inversion H3.
        destruct (removeMin cmp l1) as [[] |]; inversion e0.
      right. split.
        intro. inversion H; subst. specialize (H10 _ H3).
          rewrite cmp_spec3 in H10. congruence.
        assumption.
      constructor.
      destruct H2, H1 as [H11 | [H11 H12]]; auto.
    inversion H0; subst; clear H0. split; inversion 1; subst; auto.
Abort.
(*
      inversion H; subst. destruct (IHo x0 _ _ H5 e0).
        destruct (H1 H2); auto.
      inversion H; subst. specialize (IHo x _ _ H4 e0).
      destruct l; cbn in *.
        inversion e0.
        destruct (removeMin cmp l1) as [[] |]; inversion e0; subst.
      inversion H; subst. destruct (IHo x _ _ H4 e0).
        destruct (H1 
*)

Lemma Elem_remove :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (remove cmp y t) -> x <> y /\ Elem x t.
Proof.
Admitted.

Lemma isBST_insert :
  forall
    {A : Type} {cmp : cmp_spec A} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t).
    auto.
    constructor; auto; intros.
      inversion H; subst. destruct (Elem_insert _ _ _ H4 H0); subst.
        assumption.
        apply H5. assumption.
      inversion H; subst. apply H7. assumption.
    apply cmp_spec1 in e0. subst. assumption.
    constructor; auto; intros.
      inversion H; subst. apply H5. assumption.
      inversion H; subst. destruct (Elem_insert _ _ _ H6 H0); subst.
        assumption.
        apply H7. assumption.
Qed.

Lemma isBST_removeMin :
  forall
    {A : Type} (cmp : cmp_spec A)
    (t t' : BTree A) (x : A),
      isBST cmp t -> removeMin cmp t = Some (x, t') -> isBST cmp t'.
Proof.
  intros. revert t' x H0.
  functional induction (removeMin cmp t); intros.
    inversion H0.
    inversion H0; subst. inversion H; subst. assumption.
    inversion H0; subst. inversion H; subst.
      specialize (IHo H4 l' x0 e0). constructor; auto.
        intros. apply H5. admit.
Admitted.

Lemma isBST_remove :
  forall (A : Type) (cmp : cmp_spec A) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (remove cmp x t).
Proof.
  intros.
  functional induction (remove cmp x t); auto.
    constructor; auto; intros.
      inversion H; subst. destruct (Elem_remove cmp _ _ _ H4 H0).
        apply H5. assumption.
      inversion H; subst. apply H7. assumption.
    constructor; auto; intros.
      inversion H; subst. apply H5. assumption.
      inversion H; subst. destruct (Elem_remove cmp _ _ _ H6 H0).
        apply H7. assumption.
    inversion H; subst. constructor; auto; intros.
      eapply isBST_removeMin.
        exact H3.
        apply e1.
Abort.

Lemma elem_spec :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x : A) (t : BTree A),
      isBST cmp t -> BoolSpec (Elem x t) (~ Elem x t) (elem cmp x t).
Proof.
  intros A cmp x t H.
  functional induction (elem cmp x t).
    constructor. inversion 1.
    inversion H; subst. specialize (IHb H3). destruct IHb.
      constructor. constructor 2. assumption.
      constructor. inversion 1; subst.
        rewrite cmp_spec3 in e0. congruence.
        contradiction.
        specialize (H6 _ H7). congruence.
    constructor. apply cmp_spec1 in e0. subst. constructor.
    inversion H; subst. specialize (IHb H5). destruct IHb.
      constructor. constructor 3. assumption.
      constructor. inversion 1; subst.
        rewrite cmp_spec3 in e0. congruence.
        specialize (H4 _ H7). congruence.
        contradiction.
Qed.

Lemma elem_insert :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x : A) (t : BTree A),
      isBST cmp t -> elem cmp x (insert cmp x t) = true.
Proof.
  intros A cmp x t H.
  functional induction (insert cmp x t); cbn.
    rewrite cmp_spec3. reflexivity.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    rewrite cmp_spec3. reflexivity.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
Qed.

Lemma elem_remove :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x : A) (t : BTree A),
      isBST cmp t -> elem cmp x (remove cmp x t) = false.
Proof.
  intros A cmp x t H.
  functional induction (remove cmp x t); cbn.
    reflexivity.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    rewrite e0, IHb.
      reflexivity.
      inversion H; assumption.
    inversion H; subst. destruct (elem_spec cmp x r).
      inversion H; assumption.
      specialize (H6 _ H0). apply cmp_spec1 in e0. subst.
        rewrite cmp_spec3 in H6. congruence.
      reflexivity.
    apply cmp_spec1 in e0. subst.
Abort.

Lemma elem_insert' :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    x <> y -> elem cmp x (insert cmp y t) = elem cmp x t.
Proof.
  intros.
  functional induction (insert cmp y t); cbn.
    admit.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x y) eqn: Hxy, (cmp x v) eqn: Hxv.
      all: try reflexivity.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
Admitted.

Lemma elem_remove' :
  forall {A : Type} (cmp : A -> A -> comparison) (x y : A) (t : BTree A),
    x <> y -> elem cmp x (remove cmp y t) = elem cmp x t.
Proof.
  intros.
  functional induction (remove cmp y t); cbn.
    reflexivity.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x v); rewrite ?IHb; reflexivity.
    destruct (cmp x v) eqn: Hxv.
      admit.
      admit.
      reflexivity.
    destruct (cmp x m) eqn: Hxm, (cmp x v) eqn: Hxv.
      all: try reflexivity.
Admitted.

(* TODO theorems:

    min_spec
    forall (A : LinDec) (m : A) (bst : BTree A),
      is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.

    count
    count_ins

    Sortedness for TreeSort
*)

(** [fromList] and its variants. *)
Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

Fixpoint fromList
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.