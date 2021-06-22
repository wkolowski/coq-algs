Require Export CoqAlgs.Base.
Require Export Ord.
Require Export EBTree.

Class BalanceArgs (A : Ord) : Type :=
{
    B : Type;
    default : B;
    balance :
      forall (b : B) (l : EBTree B A) (v : A) (r : EBTree B A),
        EBTree B A;
    isEmpty_balance :
      forall (b : B) (l : EBTree B A) (v : A) (r : EBTree B A),
        isEmpty (balance b l v r) = false;
    Elem_balance :
      forall (b : B) (x v : A) (l r : EBTree B A),
        Elem x (balance b l v r) <-> Elem x l \/ x = v \/ Elem x r;
    isBST_balance :
      forall (b : B) (v : A) (l r : EBTree B A),
        isBST (N b l v r) -> isBST (balance b l v r);
}.

(* Coercion A : BalanceArgs >-> Ord. *)
(* Coercion A : BalanceArgs >-> Sortclass. *)

Definition BalancedBTree {A : Ord} (args : BalanceArgs A) : Type := EBTree B A.

Definition leaf
  {A : Ord} {args : BalanceArgs A}
  (x : A) : BalancedBTree args :=
    N default E x E.

Function insert
  {A : Ord} {args : BalanceArgs A}
  (x : A) (t : BalancedBTree args) : BalancedBTree args :=
match t with
    | E => N default E x E
    | N b l v r =>
        if x ≤? v
        then balance b (insert x l) v r
        else balance b l v (insert x r)
end.

Function removeMin
  {A : Ord} {args : BalanceArgs A}
  (t : BalancedBTree args)
    : option (A * BalancedBTree args) :=
match t with
    | E         => None
    | N b l v r =>
        match removeMin l with
            | None => Some (v, r)
            | Some (m, l') => Some (m, balance b l' v r)
        end
end.

Function remove
  {A : Ord} {args : BalanceArgs A}
  (x : A) (t : BalancedBTree args)
    : BalancedBTree args :=
match t with
    | E         => E
    | N b l v r =>
        match cmp x v with
            | Lt => balance b (remove x l) v r
            | Gt => balance b l v (remove x r)
            | Eq => 
                match removeMin r with
                    | None         => l
                    | Some (m, r') => balance b l m r'
                end
        end
end.

Fixpoint fromList
  {A : Ord} {args : BalanceArgs A}
  (l : list A) : BalancedBTree args :=
match l with
    | [] => E
    | h :: t => insert h (fromList t)
end.

(** Properties of [leaf]. *)

Lemma Elem_leaf :
  forall {A : Ord} {args : BalanceArgs A} (x y : A),
    Elem x (leaf y) <-> x = y.
Proof.
  unfold leaf. split.
    inv 1; inv H1.
    intros ->. auto.
Qed.

Lemma isBST_leaf :
  forall {A : Ord} {args : BalanceArgs A} (x : A),
    isBST (leaf x).
Proof.
  unfold leaf. intros. constructor; auto; inv 1.
Qed.

Lemma isBST2_leaf :
  forall {A : Ord} {args : BalanceArgs A} (x : A),
    isBST2 (leaf x).
Proof.
  constructor; auto.
Qed.

(** Properties of [insert]. *)

Lemma isEmpty_insert :
  forall
    {A : Ord} {args : BalanceArgs A}
    (x : A) (t : BalancedBTree args),
      isEmpty (insert x t) = false.
Proof.
  intros.
  functional induction insert x t;
  cbn.
    reflexivity.
    apply isEmpty_balance.
    apply isEmpty_balance.
Qed.

Lemma Elem_insert :
  forall
    {A : Ord} {args : BalanceArgs A}
    (x y : A) (t : BalancedBTree args),
      Elem x (insert y t) <-> x = y \/ Elem x t.
Proof.
  intros until t. revert x.
  functional induction insert y t;
  intros.
    split; inv 1.
    rewrite Elem_balance, IHb, Elem_N. split; firstorder.
    rewrite Elem_balance, IHb, Elem_N. split; firstorder.
Qed.

Lemma isBST_insert :
  forall
    {A : Ord} {args : BalanceArgs A}
    (x : A) (t : BalancedBTree args),
      isBST t -> isBST (insert x t).
Proof.
  intros until t.
  functional induction insert x t;
  inv 1.
    apply isBST_leaf.
    apply isBST_balance. constructor; auto.
      intros. rewrite Elem_insert in H. inv H. trich.
    apply isBST_balance. constructor; auto.
      intros. rewrite Elem_insert in H. inv H. trich.
Qed.

(* Lemma isBST2_insert :
  forall
    {A : Ord} {args : BalanceArgs A}
    (x : A) (t : BalancedBTree args),
      isBST2 t -> isBST2 (insert x t).
Proof.
  intros until t.
  functional induction insert x t;
  inv 1.
    apply isBST2_balance. constructor; auto.
      intros. rewrite Elem_insert in H. inv H. trich.
    apply isBST2_balance. constructor; auto.
      intros. rewrite Elem_insert in H. inv H. trich.
Qed.
 *)

(** * Properties of [removeMin]. *)

Lemma Elem_removeMin :
  forall
    {A : Ord} {args : BalanceArgs A}
    {t t' : BalancedBTree args} {m : A},
      removeMin t = Some (m, t') ->
        forall x : A, Elem x t <-> x = m \/ Elem x t'.
Proof.
  intros until t.
  functional induction removeMin t;
  inv 1; intro.
    functional inversion e0; subst.
      rewrite Elem_N. split; inv 1. inv H0. inv H.
    rewrite Elem_N, Elem_balance, (IHo _ _ e0).
      split; intro H; decompose [or] H; clear H; auto.
Qed.

Lemma isBST_removeMin :
  forall
    {A : Ord} {args : BalanceArgs A}
    (t t' : BalancedBTree args) (m : A),
      removeMin t = Some (m, t') ->
        isBST t -> isBST t'.
Proof.
  intros until t.
  functional induction removeMin t;
  inv 1; inv 1.
  {
    specialize (IHo _ _ e0 H5).
    apply isBST_balance.
    constructor; auto.
    intros. apply H4.
    rewrite (Elem_removeMin e0).
    right. assumption.
  }
Qed.

Lemma removeMin_spec :
  forall
    {A : Ord} {args : BalanceArgs A}
    {t t' : BalancedBTree args} {m : A},
      removeMin t = Some (m, t') ->
        isBST t -> forall x : A, Elem x t -> m ≤ x.
Proof.
  intros until t.
  functional induction removeMin t;
  inv 1; inv 1; intro x.
    functional inversion e0; subst. inv 1.
      trich.
      inv H1.
    inv 1.
      apply H4. rewrite (Elem_removeMin e0). auto.
      specialize (H4 _ H1). specialize (IHo _ _ e0 H5 _ H1). trich.
      specialize (H6 _ H1). assert (m0 ≤ v).
        apply H4. rewrite (Elem_removeMin e0). auto.
        trich.
Qed.

(** * Properties of [remove] *)

Lemma Elem_remove :
  forall
    {A : Ord} {args : BalanceArgs A}
    {t : BalancedBTree args} {x : A},
      isBST t ->
        forall y : A, Elem y (remove x t) -> Elem y t.
Proof.
  intros until x.
  functional induction remove x t;
  inv 1; intros y;
  rewrite Elem_balance, Elem_N.
    specialize (IHb H5 y). firstorder.
    specialize (IHb H7 y). firstorder.
    pose (Elem_removeMin e1 y). firstorder.
Qed.

Lemma isBST_remove :
  forall
    {A : Ord} {args : BalanceArgs A}
    (t : BalancedBTree args) (x : A),
      isBST t -> isBST (remove x t).
Proof.
  intros until x.
  functional induction remove x t;
  inv 1.
    apply isBST_balance. constructor; auto.
      intros. apply H4. eapply Elem_remove; eassumption.
    apply isBST_balance. constructor; auto.
      intros. apply H6. eapply Elem_remove; eassumption.
    apply isBST_balance. constructor; trich; intros.
      specialize (H4 _ H). assert (v ≤ m).
        apply H6. rewrite (Elem_removeMin e1). auto.
        trich.
      apply (removeMin_spec e1); auto. rewrite (Elem_removeMin e1). auto.
      eapply isBST_removeMin; eassumption.
Qed.

Module RB.

Require Import DS.BST.RedBlack.

#[refine]
Instance BalanceArgs_Redblack (A : Ord) : BalanceArgs A :=
{
    B := color;
    default := Red;
    balance := balance;
}.
Proof.
  intros. apply isEmpty_balance.
  intros. apply Elem_balance.
  intros. apply isBST_balance. assumption.
Defined.

End RB.