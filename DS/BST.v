Require Export RCCBase.
Require Export Data.BTree.
Require Import Ord.
Require Import Sorting.Sort.

(** * Definitions of the bst property. *)

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

Ltac isBST :=
repeat match goal with
    | H : isBST _ empty        |- _              => clear H
    | H : isBST _ (node _ _ _) |- _              => inv H
    |                          |- isBST _ _ -> _ => intro
    |                          |- isBST _ empty  => constructor
end.

Ltac isBST' :=
repeat match goal with
    | H : isBST _ empty        |- _              => clear H
    | H : isBST _ (node _ _ _) |- _              => inv H
    |                          |- isBST _ _ -> _ => intro
    |                          |- isBST _ _  => constructor
end.

Inductive isBST2
  {A : Type} {cmp : A -> A -> comparison} : BTree A -> Prop :=
    | isBST2_empty : isBST2 empty
    | isBST2_node :
        forall (v : A) (l r : BTree A),
          All (fun x : A => cmp x v = Lt) l ->
          All (fun x : A => cmp x v = Gt) r ->
            isBST2 l -> isBST2 r -> isBST2 (node v l r).

Arguments isBST2 {A} _ _.

Hint Constructors All isBST2 : core.

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

Module Wrong.

Inductive OK {A : Type} (R : A -> A -> Prop) (x : A) : BTree A -> Prop :=
    | OK_empty : OK R x empty
    | OK_node  :
        forall (y : A) (l r : BTree A),
          R y x -> OK R x (node y l r).

Inductive isBST3
  {A : Type} {cmp : A -> A -> comparison}
  : BTree A -> Prop :=
    | isBST3_empty : isBST3 empty
    | isBST3_node :
        forall (v : A) (l r : BTree A),
          OK (fun x y : A => cmp x y = Lt) v l ->
          OK (fun x y : A => cmp x y = Gt) v r ->
            isBST3 l -> isBST3 r -> isBST3 (node v l r).

Arguments isBST3 {A} _ _.

Definition Bad :=
  node 5
    (node 3
      empty
      (node 6 empty empty))
    empty.

Lemma isBST3_Bad : isBST3 Nat.compare Bad.
Proof.
  repeat constructor.
Qed.

End Wrong.

(** BST functions *)

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
                match removeMin r with
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

Lemma Elem_insert :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp y t) -> x = y \/ Elem x t.
Proof.
  intros A x y t H.
  functional induction (insert cmp y t); inv 1.
    inv H. firstorder.
    inv H. firstorder.
Qed.

Lemma Elem_insert_conv :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> Elem x t -> Elem x (insert cmp y t).
Proof.
  intros A x y t H1 H2. revert x H2 H1.
  functional induction (insert cmp y t);
  inv 1; inv 1; inv 1.
Qed.

Lemma Elem_insert_conv' :
  forall
    {A : Ord} (x : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp x t).
Proof.
  intros A x t.
  functional induction (insert cmp x t);
  intros; inv H.
  trich.
Qed.

Lemma Elem_insert_ultimate :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (insert cmp y t) <-> x = y \/ Elem x t.
Proof.
  intros A x y t. revert x.
  functional induction insert cmp y t;
  inv 1; rewrite ?Elem_node; firstorder.
  trich.
Qed.

Lemma Elem_remove :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (remove cmp y t) -> Elem x t.
Proof.
  intros A x y t. revert x.
  functional induction remove cmp y t;
  inv 1; inv 1; constructor 3;
  eapply Elem_removeMin; eauto.
Qed.

Lemma Elem_remove_conv :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> Elem x t -> cmp y x = Eq \/ Elem x (remove cmp y t).
Proof.
  intros A x y t. revert x.
  functional induction remove cmp y t;
  inv 1; inv 1.
    edestruct IHb; eauto.
    edestruct IHb; eauto.
    functional inversion e1; subst. inv H1.
    rewrite Elem_node. destruct (Elem_removeMin e1 x). firstorder.
Qed.

Lemma isBST_singleton :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A),
    isBST cmp (node x empty empty).
Proof.
  constructor; auto; inv 1.
Qed.

Hint Resolve isBST_singleton : core.

Lemma isBST_insert :
  forall
    {A : Ord} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros until t.
  functional induction (insert cmp x t); inv 1.
    constructor; auto; intros.
      rewrite Elem_insert_ultimate in H; inv H.
    constructor; auto; intros.
      rewrite Elem_insert_ultimate in H; inv H.
Qed.

Lemma All_insert :
  forall
    {A : Ord} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST2 cmp t -> All P (insert cmp x t) <-> P x /\ All P t.
Proof.
  intros A P x t H.
  functional induction (insert cmp x t);
  rewrite ?All_node', ?IHb; firstorder; inv H.
  trich.
Qed.

Lemma isBST2_insert :
  forall
    {A : Ord} (x : A) (t : BTree A),
    isBST2 cmp t -> isBST2 cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t); inv H;
  constructor; try apply All_insert; auto.
Qed.

Lemma isBST_removeMin :
  forall
    {A : Ord} (t t' : BTree A) (x : A),
      isBST cmp t -> removeMin t = Some (x, t') -> isBST cmp t'.
Proof.
  intros. revert t' x H0 H.
  functional induction removeMin t;
  inv 1; inv 1.
  constructor; eauto; intros.
  apply H4. eapply Elem_removeMin; eauto.
Qed.

Lemma All_removeMin :
  forall
    {A : Type} {t t' : BTree A} {m : A},
    removeMin t = Some (m, t') ->
        forall {P : A -> Prop}, All P t <-> P m /\ All P t'.
Proof.
  intros until t.
  functional induction removeMin t;
  inv 1; intros; rewrite ?All_node'.
    functional inversion e0. firstorder.
    rewrite IHo; firstorder eauto.
Qed.

Lemma isBST2_removeMin :
  forall
    {A : Ord} (t t' : BTree A) (x : A),
      isBST2 cmp t -> removeMin t = Some (x, t') -> isBST2 cmp t'.
Proof.
  intros. revert t' x H0 H.
  functional induction (removeMin t);
  inv 1; inv 1.
  erewrite All_removeMin in H3; firstorder eauto.
Qed.

Ltac Elems :=
  Elem;
repeat match goal with
    | H1 : forall _, Elem _ _ -> _, H2 : Elem _ _ |- _ =>
        specialize (H1 _ H2)
end; trich.

Ltac Elems' :=
  Elem';
repeat match goal with
    | |- _ /\ _ => split
    | H : _ \/ _ |- _ => destruct H
    | |- ~ _    => intro
    | H1 : forall _, Elem _ _ -> _, H2 : Elem _ _ |- _ =>
        specialize (H1 _ H2)
end; trich.

Ltac Elems'' :=
  Elem';
repeat match goal with
    | |- _ /\ _ => split
    | |- ~ _    => intro
    | H1 : forall _, Elem _ _ -> _, H2 : Elem _ _ |- _ =>(*  idtac H1 H2; *)
        let H1H2 := fresh H1 H2 in
        let H1H2 := constr:(H1 _ H2) in (* idtac x; *)
        match type of H1H2 with
            | ?T => (* idtac T; *)
                lazymatch goal with
                    | t : T |- _ => (* idtac "fail" t; *) fail
                    |       |- _ => pose H1H2
                end
        end
end; trich.

Lemma removeMin_spec :
  forall {A : Ord} {t t' : BTree A} {m : A},
    removeMin t = Some (m, t') ->
      isBST cmp t -> forall x : A, Elem x t -> cmp m x = Lt \/ m = x.
Proof.
  intros A t.
  functional induction removeMin t;
  inv 1; isBST.
    functional inversion e0; subst.
    intro. inv 1. inv H1. left. specialize (H6 _ H1). trich.
    inv 1.
      left. apply H4. apply (Elem_removeMin e0). left. reflexivity.
      apply (IHo _ _ e0 H3). assumption.
      left. specialize (H6 _ H1). assert (m0 <?> x = Lt).
        apply H4. rewrite (Elem_removeMin e0). left. reflexivity.
        trich.
Qed.

Lemma removeMin_spec2 :
  forall {A : Ord} {t t' : BTree A} {m : A},
    removeMin t = Some (m, t') ->
      isBST2 cmp t -> All (fun x : A => m <?> x = Lt) t'.
Proof.
  intros A t.
  functional induction removeMin t;
  inv 1; isBST2.
    induction H4; constructor; trich; isBST2.
    specialize (IHo _ _ e0 H5).
    assert (m0 <?> x = Lt).
      apply (All_Elem H3). rewrite (Elem_removeMin e0). left. reflexivity.
      constructor; auto. induction H4; constructor; trich; isBST2.
Qed.

Lemma removeMin_spec' :
  forall {A : Ord} {t1 t2 : BTree A} {m : A},
    removeMin t1 = Some (m, t2) ->
      isBST cmp t1 -> ~ Elem m t2.
Proof.
  intros until t1.
  functional induction removeMin t1;
  inv 1; isBST.
    Elems.
    specialize (IHo _ _ e0 H3). assert (Elem m0 l).
      rewrite (Elem_removeMin e0). auto.
      Elems'.
Qed.

Lemma isBST_remove :
  forall {A : Ord} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (remove cmp x t).
Proof.
  intros until t.
  functional induction (remove cmp x t); inv 1.
    constructor; auto; intros. apply Elem_remove in H; auto.
    constructor; auto; intros. apply Elem_remove in H; auto.
    constructor; auto; intros.
      {
        assert (cmp x0 v = Lt) by auto.
        assert (cmp m v = Gt).
          apply H6. eapply Elem_removeMin; eauto.
        trich.
      }
      eapply isBST_removeMin; eauto.
      trich.
      assert (x0 <?> v = Gt).
        apply H6. erewrite Elem_removeMin; eauto.
        assert (m <?> v = Gt).
          apply H6. erewrite Elem_removeMin.
            left. reflexivity.
            eassumption.
          destruct (removeMin_spec e1 H5 x0).
            rewrite (Elem_removeMin e1). auto.
            trich.
            trich. apply removeMin_spec' in e1.
              contradiction.
              assumption.
Qed.

Lemma All_remove :
  forall
    {A : Ord} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST2 cmp t -> All P t -> All P (remove cmp x t).
Proof.
  intros until t.
  functional induction remove cmp x t.
    1-4: inv 1; rewrite ?All_node', ?IHb; firstorder.
    inv 1; inv 1. rewrite ?All_node'.
      eapply All_removeMin with P in e1; firstorder eauto.
Qed.

Lemma All_remove_conv :
  forall
    {A : Ord} (P : A -> Prop)
    (x : A) (t : BTree A),
      isBST2 cmp t -> All P (remove cmp x t) -> (P x -> All P t).
Proof.
  intros until t.
  functional induction remove cmp x t;
  inv 1; rewrite ?All_node'; firstorder.
    trich.
    functional inversion e1; subst. constructor.
    trich.
    eapply All_removeMin with P in e1; firstorder eauto.
Qed.

Lemma isBST2_remove :
  forall {A : Ord} (x : A) (t : BTree A),
    isBST2 cmp t -> isBST2 cmp (remove cmp x t).
Proof.
  intros until t.
  functional induction (remove cmp x t);
  isBST2.
    constructor; auto. apply All_remove; auto.
    constructor; auto. apply All_remove; auto.
    constructor; auto.
      assert (m <?> v = Gt).
        apply (All_Elem H4). rewrite (Elem_removeMin e1). left. reflexivity.
        induction H3; constructor; trich; isBST2.
      apply removeMin_spec2 in e1.
        2: assumption.
        induction e1; constructor; trich.
      eapply isBST2_removeMin; eassumption.
Qed.

Lemma elem_spec :
  forall
    {A : Ord} (x : A) (t : BTree A),
      isBST cmp t -> BoolSpec (Elem x t) (~ Elem x t) (elem cmp x t).
Proof.
  intros A x t.
  functional induction (elem cmp x t);
  isBST.
    constructor; Elems'.
    destruct (IHb H3); constructor; Elems'.
    trich.
    destruct (IHb H5); constructor; Elems'.
Qed.

Lemma elem_spec' :
  forall
    {A : Ord} (x : A) (t : BTree A),
      isBST2 cmp t -> BoolSpec (Elem x t) (~ Elem x t) (elem cmp x t).
Proof.
  intros A x t.
  functional induction (elem cmp x t);
  isBST2.
    constructor. inv 1.
    destruct (IHb H5); constructor; Elems'.
      apply (All_Elem H4) in H2. trich.
    trich.
    destruct (IHb H6); constructor; Elems'.
      apply (All_Elem H3) in H2. trich.
Qed.

Lemma elem_insert :
  forall
    {A : Ord} (x : A) (t : BTree A),
      isBST cmp t -> elem cmp x (insert cmp x t) = true.
Proof.
  intros. destruct (elem_spec x (insert cmp x t) (isBST_insert x t H)).
    reflexivity.
    contradiction H0. rewrite Elem_insert_ultimate; auto.
Qed.

Lemma elem_insert' :
  forall
    {A : Ord} (x y : A) (t : BTree A),
      isBST cmp t -> elem cmp x (insert cmp y t) = (x =? y) || elem cmp x t.
Proof.
  intros. destruct (elem_spec x (insert cmp y t) (isBST_insert y t H)).
    rewrite Elem_insert_ultimate in H0.
      destruct H0; subst.
        trich.
        destruct (elem_spec x t H).
          rewrite orb_true_r. reflexivity.
          contradiction.
      assumption.
    unfold orb. trich.
      contradiction H0. apply Elem_insert_conv'; assumption.
      destruct (elem_spec x t); auto. contradiction H0.
        apply Elem_insert_conv; assumption.
Qed.

Lemma Sorted_inorder :
  forall {A : Ord} (t : BTree A),
    isBST cmp t -> Sorted cmp (inorder t).
Proof.
  induction t; inv 1; cbn.
    constructor.
    apply Sorted_app.
      apply IHt1. assumption.
      destruct (inorder t2) eqn: Heq.
        constructor.
        constructor.
          assert (Elem c t2).
            rewrite <- toList_In_Elem, Heq. left. reflexivity.
            Elems. red. rewrite H6. reflexivity.
          apply IHt2. assumption.
      inv 2.
        red. rewrite H4.
          reflexivity.
          rewrite <- toList_In_Elem. assumption.
        red. rewrite toList_In_Elem in H. rewrite toList_In_Elem in H1.
          Elems'. rewrite Hxz. reflexivity.
Qed.

Hint Constructors All : core.

Lemma Elem_leftmost :
  forall {A : Type} (t : BTree A) (x : A),
    leftmost t = Some x -> Elem x t.
Proof.
  intros until t.
  functional induction leftmost t; inv 1.
Qed.

Lemma leftmost_spec :
  forall {A : Ord} (t : BTree A) (m : A),
    leftmost t = Some m ->
      isBST cmp t -> All (fun x => cmp m x = Lt \/ x = m) t.
Proof.
  intros until t.
  functional induction leftmost t;
  inv 1; isBST.
    constructor; auto. rewrite All_spec. Elems.
    constructor; auto.
      left. apply H5. apply Elem_leftmost. assumption.
      apply All_spec. Elems. apply Elem_leftmost in H1. Elems.
Qed.

(** [partition] *)

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
        let '((l, _), r) := partition cmp v1 t2 in
          node v1 (union cmp l1 l) (union cmp r1 r)
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
                  else
                    match removeMin r' with
                        | None => l'
                        | Some (m, r'') => node m l' r''
                    end
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
          then
            match removeMin r' with
                | None => l'
                | Some (m, r'') => node m l' r''
            end
          else
            node v1 l' r'
end.

Lemma Elem_partition :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) ->
      forall x : A, Elem x t -> x = v \/ Elem x t1 \/ Elem x t2.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; inv 1; try edestruct IHp; eauto; Elems'.
Qed.

Lemma Elem_partition_conv :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) ->
      forall x : A, Elem x t1 \/ Elem x t2 -> Elem x t.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; intro; rewrite ?Elem_node; firstorder.
Qed.

Lemma partition_spec :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) -> isBST cmp t ->
      (forall x : A, Elem x t1 -> cmp x v = Lt) /\
      (forall x : A, Elem x t2 -> cmp x v = Gt).
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; isBST.
    split; Elem.
    split; Elems.
    edestruct IHp; eauto. split; Elems'.
    edestruct IHp; eauto. split; Elems'.
Qed.

Lemma partition_spec' :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) ->
      isBST2 cmp t ->
        All (fun x : A => cmp x v = Lt) t1
          /\
        All (fun x : A => cmp x v = Gt) t2.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; isBST2.
    trich.
    destruct (IHp _ _ _ e1 H5). split; auto. constructor; trich.
      induction H4; isBST2. constructor; trich.
    destruct (IHp _ _ _ e1 H6). split; auto. constructor; trich.
      induction H3; isBST2. constructor; trich.
Qed.

Lemma Elem_partition_rw' :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) ->
      forall x : A,
        Elem x t
          <->
        (if b
         then x = v \/ Elem x t1 \/ Elem x t2
         else Elem x t1 \/ Elem x t2).
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1.
    split; Elem.
    split; Elems'.
    intros. rewrite Elem_node, (IHp _ _ _ e1 x). destruct b0; split; Elems'.
    intros. rewrite Elem_node, (IHp _ _ _ e1 x). destruct b0; split; Elems'.
Qed.

Lemma Elem_partition_rw'' :
  forall {A : Ord} {v : A} {t t1 t2 : BTree A} {b : bool},
    partition cmp v t = (t1, b, t2) -> isBST cmp t ->
      forall x : A,
        Elem x t
          <->
        (if b
         then x = v \/ Elem x t1 \/ Elem x t2
         else (Elem x t1 /\ ~ Elem x t2) \/ (~ Elem x t1 /\ Elem x t2)).
Proof.
  intros.
  destruct (partition_spec H H0).
  destruct (Elem_partition_rw' H x).
  destruct b.
    split; Elems.
    split; Elems'. intro. firstorder Elems.
Qed.

Lemma isBST_partition :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t l r : BTree A} {b : bool},
    partition cmp v t = (l, b, r) ->
      isBST cmp t -> isBST cmp l /\ isBST cmp r.
Proof.
  intros until t.
  functional induction partition cmp v t;
  inv 1; inv 1; repeat constructor; firstorder;
  [apply H4 | apply H6]; eapply Elem_partition_conv; eauto.
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

(** * [union] *)

Lemma union_empty_l :
  forall {A : Type} {cmp : A -> A -> comparison} (t : BTree A),
    union cmp empty t = t.
Proof.
  reflexivity.
Qed.

Lemma union_empty_r :
  forall {A : Type} {cmp : A -> A -> comparison} (t : BTree A),
    union cmp t empty = t.
Proof.
  intros. remember empty as t'. revert Heqt'.
  functional induction union cmp t t';
  intros ->.
    reflexivity.
    inv e0. rewrite (IHb eq_refl), (IHb0 eq_refl). reflexivity.
Qed.

Lemma Elem_union :
  forall {A : Ord} (x : A) (t1 t2 : BTree A),
    Elem x (union cmp t1 t2) <-> Elem x t1 \/ Elem x t2.
Proof.
  intros. revert x.
  functional induction union cmp t1 t2;
  intro.
    firstorder. inv H.
    pose (H := Elem_partition_conv e0 x). pose (H' := Elem_partition e0 x).
      rewrite ?Elem_node, IHb, IHb0. split; Elems'. specialize (H' H0). Elems'.
Qed.

Lemma Elem_union_poor :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t1 t2 : BTree A),
    Elem x (union cmp t1 t2) -> Elem x t1 \/ Elem x t2.
Proof.
  intros until t2.
  functional induction union cmp t1 t2;
  intro.
    right. assumption.
    inv H.
      specialize (IHb H1). inv IHb. right. destruct (Elem_partition_conv e0 x); auto.
      specialize (IHb0 H1). inv IHb0. right. destruct (Elem_partition_conv e0 x); auto.
Qed.

Lemma isBST_union :
  forall {A : Ord} (t1 t2 : BTree A),
    isBST cmp t1 -> isBST cmp t2 -> isBST cmp (union cmp t1 t2).
Proof.
  intros until t2.
  functional induction union cmp t1 t2;
  isBST.
    assumption.
    destruct (isBST_partition e0 H). constructor; intros; auto.
      apply Elem_union_poor in H2. inv H2. destruct (partition_spec e0 H). auto.
      apply Elem_union_poor in H2. inv H2. destruct (partition_spec e0 H). auto.
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
  destruct (isBST2_partition e0 H0), (partition_spec' e0 H0). constructor; auto.
    apply All_union; auto.
    apply All_union; auto.
Qed.

(** * Properties of [intersection *)

Lemma intersection_empty_l :
  forall {A : Type} {cmp : A -> A -> comparison} (t : BTree A),
    intersection cmp empty t = empty.
Proof.
  reflexivity.
Qed.

Lemma intersection_empty_r :
  forall {A : Type} {cmp : A -> A -> comparison} (t : BTree A),
    intersection cmp t empty = empty.
Proof.
  intros. remember empty as t'. revert Heqt'.
  functional induction intersection cmp t t';
  intros ->.
    reflexivity.
    1-3: inv e0. rewrite IHb0 in e2; inv e2.
Qed.

Lemma Elem_intersection :
  forall {A : Ord} {t1 t2 : BTree A} (x : A),
    isBST cmp t1 -> isBST cmp t2 ->
      Elem x (intersection cmp t1 t2) <-> Elem x t1 /\ Elem x t2.
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  inv 1; intros; rewrite ?Elem_node, ?IHb, ?IHb0;
  try (edestruct (isBST_partition e0); eauto; fail).
    split; Elem.
    {
      rewrite (Elem_partition_rw'' e0 H).
      destruct (partition_spec e0 H).
      split; Elems'.
    }
    rewrite (Elem_partition_rw'' e0 H). destruct (partition_spec e0 H). split.
      split; Elems. left. split; try intro; Elems.
      {
        functional inversion e2; subst.
        destruct (isBST_partition e0 H), (partition_spec e0 H).
        Elems'.
          cut (Elem x empty).
            inv 1.
            rewrite H2, IHb0; auto.
          cut (Elem x empty).
            inv 1.
            rewrite H2, IHb0; auto.
      }
    {
      destruct (isBST_partition e0 H).
      destruct (partition_spec e0 H).

      assert (Elem m r1 /\ Elem m r).
        rewrite <- IHb0, (Elem_removeMin e2); auto.

      rewrite (Elem_partition_rw'' e0 H). destruct H8. split.
        intro. decompose [and or] H10; clear H10; subst; auto.
          Elems'. right. split; Elems'.
          split; auto. left. split; Elems'.
          assert (Elem x r1 /\ Elem x r).
            rewrite <- IHb0, (Elem_removeMin e2); auto.
            Elems'. right. split; Elems'.
        intro. decompose [and or] H10; clear H10; subst.
          1-5: Elems.
          assert (x = m \/ Elem x r'').
            rewrite <- (Elem_removeMin e2), IHb0; auto.
            destruct H10; auto.
      }
Qed.

Lemma isBST_intersection :
  forall {A : Ord} {t1 t2 : BTree A},
    isBST cmp t1 -> isBST cmp t2 ->
      isBST cmp (intersection cmp t1 t2).
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  isBST; destruct (isBST_partition e0); auto.
    isBST'; auto; intros.
      apply Elem_intersection in H2; auto. destruct H2. Elems.
      apply Elem_intersection in H2; auto. destruct H2. Elems.
    specialize (IHb H3 H0). specialize (IHb0 H5 H1). isBST'; auto; intros.
      apply Elem_intersection in H2; auto. destruct H2. assert (Elem m r1 /\ Elem m r).
        rewrite <- Elem_intersection, (Elem_removeMin e2); auto.
        Elems.
      apply isBST_removeMin in e2; auto.
      {
        edestruct (removeMin_spec e2); auto.
          rewrite (Elem_removeMin e2). right. eassumption.
          trich.
          subst. apply removeMin_spec' in e2; auto. contradiction.
      }
Qed.

Lemma Elem_difference :
  forall {A : Ord} {t1 t2 : BTree A},
    isBST cmp t1 -> isBST cmp t2 ->
      forall x : A, Elem x (difference cmp t1 t2) <-> Elem x t1 /\ ~ Elem x t2.
Proof.
  intros until t2.
  functional induction difference cmp t1 t2;
  isBST; intros.
    split; Elems'.
    destruct (isBST_partition e0 H). rewrite IHb; auto. split.
      Elems'. pose (Elem_partition e0 x H8). destruct (partition_spec e0 H). Elems'.
      {
        functional inversion e2. inv 1.
        rewrite (Elem_partition_rw'' e0 H) in H10.
        split; inv H9.
          contradiction H10. auto.
          cut (Elem x empty).
            inv 1.
            rewrite H2, IHb0; auto. split; auto.
      }
    {
      assert (Elem v1 t2).
        rewrite (Elem_partition_rw' e0). left. reflexivity.
      destruct (isBST_partition e0 H).
      destruct (partition_spec e0 H).
      pose (Elem_removeMin e2).
      rewrite ?Elem_node, IHb, (Elem_partition_rw' e0); auto.
      assert (Elem m r1 /\ ~ Elem m r).
        rewrite <- IHb0, i; auto.
      destruct H9.
      split.
        intro. decompose [and or] H11; clear H11; subst.
          Elems'.
          Elems'.
          assert (Elem x r1 /\ ~ Elem x r).
            rewrite <- IHb0, i; auto.
            Elems'.
        intro. decompose [and or] H11; clear H11; subst; auto.
          contradiction H13. auto.
          right. left. split; auto.
          assert (x = m \/ Elem x r'').
            rewrite <- i, IHb0; try split; auto.
            inv H11.
    }
    {
      destruct (isBST_partition e0 H).
      destruct (partition_spec e0 H).
      rewrite ?Elem_node, IHb, IHb0; auto.
      rewrite (Elem_partition_rw' e0).
      split.
        Elems'.
        Elems'.
          right. left. Elems'.
          right. right. Elems'.
    }
Qed.

Lemma isBST_difference :
  forall {A : Ord} {t1 t2 : BTree A},
    isBST cmp t1 -> isBST cmp t2 ->
      isBST cmp (difference cmp t1 t2).
Proof.
  intros until t2.
  functional induction difference cmp t1 t2;
  isBST; destruct (isBST_partition e0); auto.
    specialize (IHb H3 H0). specialize (IHb0 H5 H1). isBST'; auto; intros.
      apply Elem_difference in H2; auto. destruct H2. assert (Elem m r1 /\ ~ Elem m r).
        rewrite <- Elem_difference, (Elem_removeMin e2); auto.
        Elems''.
      apply isBST_removeMin in e2; auto.
      {
        edestruct (removeMin_spec e2); auto.
          rewrite (Elem_removeMin e2). right. eassumption.
          trich.
          subst. apply removeMin_spec' in e2; auto. contradiction.
      }
    isBST'; auto; intros.
      apply Elem_difference in H2; auto. destruct H2. Elems.
      apply Elem_difference in H2; auto. destruct H2. Elems.
Qed.

Fixpoint fromList {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.

(*
Compute fromList Nat.compare [1; 2; 3; 4; 5].
Compute fromList Nat.compare [3; 4; 5; 6; 7].
Compute union Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute intersection Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute difference Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute difference Nat.compare (fromList Nat.compare [3; 4; 5; 6; 7]) (fromList Nat.compare [1; 2; 3; 4; 5]).
 *)