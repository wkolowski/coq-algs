Require Export RCCBase.
Require Import BTree.
(* Require Export LinDec. *)
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

Hint Extern 0 =>
  intros;
match goal with
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
  functional induction (insert cmp y t); inv 1.
    inv H. firstorder.
    inv H. firstorder.
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
  intros A cmp x y t. revert x.
  functional induction insert cmp y t;
  inv 1; rewrite ?Elem_node; firstorder.
  destruct (cmpr_spec y v); subst; auto; congruence.
Qed.

(* Lemma Elem_removeMin :
  forall
    {A : Type} {t t' : BTree A} {m : A},
      removeMin t = Some (m, t') ->
        forall [x : A], Elem x t' -> Elem x t.
Proof.
  intros until t.
  functional induction removeMin t;
  inv 1; inv 1; eauto.
Qed.

Lemma Elem_removeMin_conv :
  forall
    {A : Type} {t t' : BTree A} {m : A},
      removeMin t = Some (m, t') ->
        forall [x : A], Elem x t -> x = m \/ Elem x t'.
Proof.
  intros A t.
  functional induction removeMin t;
  inv 1; inv 1.
    functional inversion e0. subst. inv H1.
    edestruct IHo; eauto.
Qed.

Lemma Elem_removeMin_v2 :
  forall
    {A : Type} {cmp : cmp_spec A}
    (m : A) (t t' : BTree A),
      isBST cmp t -> removeMin t = Some (m, t') ->
        Elem m t.
Proof.
  intros A cmp m t t' H.
  revert m t' H.
  functional induction removeMin t;
  inv 1; inv 1; eauto.
Qed.
 *)

Lemma Elem_remove :
  forall
    {A : Type} (cmp : cmp_spec A)
    (x y : A) (t : BTree A),
      isBST cmp t -> Elem x (remove cmp y t) -> Elem x t.
Proof.
  intros A cmp x y t. revert x.
  functional induction remove cmp y t;
  inv 1; inv 1; constructor 3;
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
    rewrite Elem_node. destruct (Elem_removeMin e1 x). firstorder.
Qed.

Lemma isBST_insert :
  forall
    {A : Type} {cmp : cmp_spec A} (x : A) (t : BTree A),
    isBST cmp t -> isBST cmp (insert cmp x t).
Proof.
  intros.
  functional induction (insert cmp x t); auto.
    constructor; auto; intros; inv H.
      rewrite Elem_insert_ultimate in H0; inv H0.
    constructor; auto; intros; inv H.
      rewrite Elem_insert_ultimate in H0; inv H0.
Qed.

Lemma isBST_removeMin :
  forall
    {A : Type} (cmp : cmp_spec A)
    (t t' : BTree A) (x : A),
      isBST cmp t -> removeMin t = Some (x, t') -> isBST cmp t'.
Proof.
  intros. revert t' x H0 H.
  functional induction removeMin t;
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
          apply H6. eapply Elem_removeMin; eauto.
        (* transitivity *) admit.
      }
      eapply isBST_removeMin; eauto.
      assert (Elem x0 r).
        apply (Elem_removeMin e1). auto.
        admit. (* doable *)
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
    contradiction H0. rewrite Elem_insert_ultimate; auto.
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

Hint Constructors All : core.

Lemma leftmost_spec :
  forall {A : Type} (cmp : A -> A -> comparison) (t : BTree A) (m : A),
    isBST cmp t -> leftmost t = Some m -> All (fun x => cmp m x = Lt \/ x = m) t.
Proof.
  intros until t.
  functional induction leftmost t; inv 1; inv 1.
    constructor; auto. admit. (* H6 *)
    constructor; auto.
      left. apply H4. admit. (* Elem_leftmost *)
      admit. (* All_spec, H4 *)
Admitted.

(** [split] *)

Function split
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A)
  : BTree A * BTree A :=
match t with
    | empty      => (empty, empty)
    | node v l r =>
        match cmp x v with
            | Lt => let (l1, l2) := split cmp x l in (l1, node v l2 r)
            | Eq => (l, r)
            | Gt => let (r1, r2) := split cmp x r in (node v l r1, r2)
        end
end.

Function union {A : Type} (cmp : A -> A -> comparison) (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => t2
    | node v1 l1 r1 =>
        let (l, r) := split cmp v1 t2 in
          node v1 (union cmp l1 l) (union cmp r1 r)
end.

Fixpoint split'
  {A : Type} (cmp : A -> A -> comparison) (x : A) (t : BTree A)
  : BTree A * bool * BTree A :=
match t with
    | empty      => (empty, false, empty)
    | node v l r =>
        match cmp x v with
            | Lt =>
                match split' cmp x l with
                    | (l1, b, l2) => (l1, b, node v l2 r)
                end
            | Eq => (l, true, r)
            | Gt =>
                match split' cmp x r with
                    | (r1, b, r2) => (node v l r1, b, r2)
                end
        end
end.

Functional Scheme split'_ind := Induction for split' Sort Prop.

Function intersection {A : Type} (cmp : A -> A -> comparison) (t1 t2 : BTree A) : BTree A :=
match t1 with
    | empty => empty
    | node v1 l1 r1 =>
        match split' cmp v1 t2 with
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
        let '(l, b, r) := split' cmp v1 t2 in
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

Lemma Elem_split :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t t1 t2 : BTree A},
    split cmp v t = (t1, t2) ->
      forall x : A, Elem x t -> x = v \/ Elem x t1 \/ Elem x t2.
Proof.
  intros until t.
  functional induction split cmp v t;
  inv 1; inv 1; try edestruct IHp; firstorder eauto.
Admitted.

Lemma Elem_split_conv :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t t1 t2 : BTree A},
    split cmp v t = (t1, t2) ->
      forall x : A, Elem x t1 \/ Elem x t2 -> Elem x t.
Proof.
  intros until t.
  functional induction split cmp v t;
  inv 1; intro; rewrite ?Elem_node; firstorder.
Qed.

Lemma Elem_union :
  forall {A : Type} (cmp : A -> A -> comparison) (x : A) (t1 t2 : BTree A),
    Elem x (union cmp t1 t2) <-> Elem x t1 \/ Elem x t2.
Proof.
  intros. revert x.
  functional induction union cmp t1 t2;
  intro.
    firstorder.
    pose (H := Elem_split_conv e0 x). pose (H' := Elem_split e0 x).
      rewrite ?Elem_node, IHb, IHb0. firstorder.
Qed.

Lemma isBST_split :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t l r : BTree A},
    split cmp v t = (l, r) ->
      isBST cmp t -> isBST cmp l /\ isBST cmp r.
Proof.
  intros until t.
  functional induction split cmp v t;
  inv 1; inv 1; repeat constructor; firstorder;
  [apply H4 | apply H6]; eapply Elem_split_conv; eauto.
Qed.

Lemma Elem_split' :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t t1 t2 : BTree A} {b : bool},
    split' cmp v t = (t1, b, t2) ->
      forall x : A, Elem x t -> x = v \/ Elem x t1 \/ Elem x t2.
Proof.
  intros until t.
  functional induction split' cmp v t;
  inv 1; inv 1; try edestruct IHp; firstorder eauto.
Admitted.

Lemma Elem_split'_conv :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t t1 t2 : BTree A} {b : bool},
    split' cmp v t = (t1, b, t2) ->
      forall x : A, Elem x t1 \/ Elem x t2 -> Elem x t.
Proof.
  intros until t.
  functional induction split' cmp v t;
  inv 1; intro; rewrite ?Elem_node; firstorder.
Qed.

Lemma isBST_split' :
  forall {A : Type} {cmp : A -> A -> comparison} {v : A} {t l r : BTree A} {b : bool},
    split' cmp v t = (l, b, r) ->
      isBST cmp t -> isBST cmp l /\ isBST cmp r.
Proof.
  intros until t.
  functional induction split' cmp v t;
  inv 1; inv 1; repeat constructor; firstorder;
  [apply H4 | apply H6]; eapply Elem_split'_conv; eauto.
Qed.

Lemma Elem_intersection :
  forall {A : Type} {cmp : A -> A -> comparison} {t1 t2 : BTree A} (x : A),
    isBST cmp t1 -> isBST cmp t2 ->
      Elem x (intersection cmp t1 t2) <-> Elem x t1 /\ Elem x t2.
Proof.
  intros until t2.
  functional induction intersection cmp t1 t2;
  inv 1; intros; rewrite ?Elem_node, ?IHb, ?IHb0;
  try (edestruct (isBST_split' e0); eauto; fail);
  try pose (H := Elem_split'_conv e0 x);
  try pose (H' := Elem_split' e0 x).
    firstorder.
    firstorder; subst.
      admit.
      pose (Elem_split'_conv e0 x). auto.
      pose (Elem_split'_conv e0 x). auto.
      right.
Abort.

Fixpoint fromList {A : Type} (cmp : A -> A -> comparison) (l : list A) : BTree A :=
match l with
    | [] => empty
    | h :: t => insert cmp h (fromList cmp t)
end.

Compute fromList Nat.compare [1; 2; 3; 4; 5].
Compute fromList Nat.compare [3; 4; 5; 6; 7].
Compute union Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute intersection Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute difference Nat.compare (fromList Nat.compare [1; 2; 3; 4; 5]) (fromList Nat.compare [3; 4; 5; 6; 7]).
Compute difference Nat.compare (fromList Nat.compare [3; 4; 5; 6; 7]) (fromList Nat.compare [1; 2; 3; 4; 5]).