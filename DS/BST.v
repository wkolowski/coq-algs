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
            | Eq => node v l r
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
                match removeMin cmp r with
                    | None => l
                    | Some (m, r') => node m l r'
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

Inductive Reflect_cmp (P Q R : Prop) : comparison -> Prop :=
    | Reflect_Lt : P -> Reflect_cmp P Q R Lt
    | Reflect_Eq : Q -> Reflect_cmp P Q R Eq
    | Reflect_Gt : R -> Reflect_cmp P Q R Gt.

Class cmp_spec (A : Type) : Type :=
{
    cmpr      : A -> A -> comparison;
    cmpr_spec :
      forall x y : A, Reflect_cmp (cmpr y x = Gt) (x = y) (cmpr y x = Lt) (cmpr x y);
    cmp_spec1 :
      forall x y : A, cmpr x y = Eq -> x = y;
    cmp_spec2 :
      forall x y : A, cmpr x y = Lt <-> cmpr y x = Gt;
    cmp_spec3 :
      forall x : A, cmpr x x = Eq;
}.

Coercion cmpr : cmp_spec >-> Funclass.

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

Lemma Elem_insert_conv :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x t -> Elem x (insert cmp y t).
Proof.
  intros A cmp x y t H1 H2. revert x H2 H1.
  functional induction (insert cmp y t);
  inv 1; inv 1; inv 1.
Qed.

Lemma Elem_insert_conv' :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp x t).
Proof.
  intros A cmp x t.
  functional induction (insert cmp x t);
  intros; auto.
  destruct (cmpr_spec x v); subst; try congruence; auto.
Qed.

Lemma Elem_insert_ultimate :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp y t) <-> x = y \/ Elem x t.
Proof.
  split; intros.
    apply Elem_insert; assumption.
    inv H0.
      apply Elem_insert_conv'; assumption.
      apply Elem_insert_conv; assumption.
Qed.

Lemma Elem_removeMin :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x m : A) (t t' : BTree A),
      isBST cmp t -> removeMin cmp t = Some (m, t') ->
        Elem x t' -> Elem x t.
Proof.
  intros A cmp x m t t' H1 H2.
  revert x m t' H2 H1.
  functional induction (removeMin cmp t);
  inv 1; inv 1; inv 1; eauto.
Qed.

Lemma Elem_removeMin_conv :
  forall
    {A : Type} {cmp : cmp_spec A}
    (x m : A) (t t' : BTree A),
      isBST cmp t -> removeMin cmp t = Some (m, t') ->
        Elem x t -> x = m \/ Elem x t'.
Proof.
  intros A cmp x m t t' H.
  revert x m t' H.
  functional induction (removeMin cmp t);
  inv 1; inv 1; inv 1.
    functional inversion e0. subst. inv H1.
    edestruct IHo; eauto.
Qed.

Lemma Elem_removeMin_v2 :
  forall
    {A : Type} {cmp : cmp_spec A}
    (m : A) (t t' : BTree A),
      isBST cmp t -> removeMin cmp t = Some (m, t') ->
        Elem m t.
Proof.
  intros A cmp m t t' H.
  revert m t' H.
  functional induction (removeMin cmp t);
  inv 1; inv 1; eauto.
Qed.

Lemma Elem_remove :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (remove cmp y t) -> Elem x t.
Proof.
  intros A cmp x y t. revert x.
  functional induction remove cmp y t;
  inv 1; inv 1; constructor 3.
    eapply Elem_removeMin_v2; eauto.
    eapply Elem_removeMin; eauto.
Qed.

Lemma Elem_remove_conv :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x t -> cmp y x = Eq \/ Elem x (remove cmp y t).
Proof.
  intros A cmp x y t. revert x.
  functional induction remove cmp y t;
  inv 1; inv 1.
    edestruct IHb; eauto.
    edestruct IHb; eauto.
    functional inversion e1; subst. inv H1.
    edestruct Elem_removeMin_conv; eauto; subst; eauto.
Qed.

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
  intros. revert t' x H0 H.
  functional induction (removeMin cmp t);
  inv 1; inv 1.
  constructor; eauto; intros.
  apply H4. eapply Elem_removeMin; eauto.
Qed.

Lemma isBST_remove :
  forall (A : Type) (cmp : cmp_spec A) (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (remove cmp x t).
Proof.
  intros. revert H.
  functional induction (remove cmp x t); inv 1.
    constructor; auto; intros. apply Elem_remove in H; auto.
    constructor; auto; intros. apply Elem_remove in H; auto.
    constructor; auto; intros.
      {
        assert (cmp x0 v = Lt) by auto.
        assert (cmp m v = Gt).
          apply H6. eapply Elem_removeMin_v2; eauto.
        (* transitivity *) admit.
      }
      eapply isBST_removeMin; eauto.
      assert (Elem x0 r) by apply (Elem_removeMin x0 _ _ _ H5 e1 H). admit. (* doable *)
Admitted.

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
  intros. destruct (elem_spec cmp x (insert cmp x t) (isBST_insert x t H)).
    reflexivity.
    contradiction H0. apply Elem_insert_conv'. assumption.
Qed.

Definition eql {A : Type} (cmp : cmp_spec A) (x y : A) : bool :=
match cmp x y with
    | Eq => true
    | _  => false
end.

Lemma elem_insert' :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x y : A) (t : BTree A),
      isBST cmp t -> elem cmp x (insert cmp y t) = eql cmp x y || elem cmp x t.
Proof.
  intros. destruct (elem_spec cmp x (insert cmp y t) (isBST_insert y t H)).
    rewrite Elem_insert_ultimate in H0.
      destruct H0; subst.
        unfold eql. rewrite cmp_spec3. cbn. reflexivity.
        destruct (elem_spec cmp x t H).
          rewrite orb_true_r. reflexivity.
          contradiction.
      assumption.
    unfold eql. destruct (cmpr_spec x y); cbn.
      destruct (elem_spec cmp x t); auto. contradiction H0.
        apply Elem_insert_conv; assumption.
      subst. contradiction H0. apply Elem_insert_conv'; assumption.
      destruct (elem_spec cmp x t); auto. contradiction H0.
        apply Elem_insert_conv; assumption.
Qed.

Fixpoint min {A : Type} (t : BTree A) : option A :=
match t with
    | empty => None
    | node v empty _ => Some v
    | node _ l _ => min l
end.

Lemma Sorted_BTree_toList :
  forall (A : Type) (p : A -> A -> comparison) (t : BTree A),
    isBST p t -> Sorted p (BTree_toList t).
Proof.
  induction t; inv 1; cbn.
    constructor.
    apply Sorted_app.
      apply IHt1. assumption.
      destruct (BTree_toList t2) eqn: Heq.
        constructor.
        constructor.
          red. unfold comparison2bool. destruct (p a a0) eqn: Hp.
            1-2: reflexivity.
            admit. (* TODO *)
          apply IHt2. assumption.
      admit.
Admitted.

(** [fromList] and its variants. *)
Fixpoint fromList
  {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.

Lemma isBST_fromList :
  forall {A : Type} (cmp : cmp_spec A) (l : list A),
    isBST cmp (fromList cmp l).
Proof.
  induction l as [| h t]; cbn.
    constructor.
    apply isBST_insert. assumption.
Qed.

Lemma count_BTree_insert :
  forall (A : Type) (cmp : cmp_spec A) (p : A -> bool) (x : A) (t : BTree A),
    count_BTree p (insert cmp x t) =
      if p x then 1 + count_BTree p t else count_BTree p t.
Proof.
  induction t; cbn.
    reflexivity.
    destruct (cmpr_spec x a); cbn;
      rewrite ?IHt1, ?IHt2;
      destruct (p x) eqn: Hpx, (p a) eqn: Hpa; cbn; try lia.

(* TODO theorems:

    elem_remove
    min_spec
    forall (A : LinDec) (m : A) (bst : BTree A),
      is_bst bst -> min bst = Some m -> forall x : A, elem x bst -> leq m x.
*)