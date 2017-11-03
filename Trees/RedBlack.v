Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Inductive color : Set :=
    | Red : color
    | Black : color.

Inductive RBTree (A : Type) : Type :=
    | E : RBTree A
    | T : color -> RBTree A -> A -> RBTree A -> RBTree A.

Arguments E [A].
Arguments T [A] _ _ _.

Inductive elem {A : Type} (x : A) : RBTree A -> Prop :=
    | elem_root : forall (c : color) (l r : RBTree A),
        elem x (T c l x r)
    | elem_left : forall (c : color) (v : A) (l r : RBTree A),
        elem x l -> elem x (T c l v r)
    | elem_right : forall  (c : color) (v : A) (l r : RBTree A),
        elem x r -> elem x (T c l v r).

Hint Constructors color RBTree elem.

Ltac inv H := inversion H; clear H; subst; cbn; auto.

Lemma elem_color :
  forall (A : Type) (c c' : color) (x v : A) (l r : RBTree A),
    elem x (T c l v r) -> elem x (T c' l v r).
Proof.
  intros; inv H.
Qed.

Function balance {A : Type} (c : color)
  (l : RBTree A) (v : A) (r : RBTree A) : RBTree A :=
match c with
    | Red => T Red l v r
    | Black =>
        match l, v, r with
            | T Red (T Red a xv b) yv c, zv, d
            | T Red a xv (T Red b yv c), zv, d
            | a, xv, T Red (T Red b yv c) zv d
            | a, xv, T Red b yv (T Red c zv d) =>
                T Red (T Black a xv b) yv (T Black c zv d)
            | l, v, r => T Black l v r
        end
end.

Definition makeBlack {A : Type} (t : RBTree A) :=
match t with
    | E => E
    | T _ l v r => T Black l v r
end.

(*Function ins {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => T Red E x E
    | T c l v r =>
        if x <=? v
        then balance c (ins x l) v r
        else if v <=? x
          then balance c l v (ins x r)
          else T c l x r
end.*)

Function ins {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
match t with
    | E => T Red E x E
    | T c l v r =>
        if x <=? v
        then balance c (ins x l) v r
        else balance c l v (ins x r)
end.

Definition insert {A : LinDec} (x : A) (t : RBTree A) : RBTree A :=
  makeBlack (ins x t).

Require Import Coq.Logic.FunctionalExtensionality.

Lemma T_not_E :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    T c l v r <> E.
Proof.
  inversion 1.
Qed.

Lemma balance_not_E :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    balance c l v r <> E.
Proof.
  intros. functional induction @balance A c l v r; apply T_not_E.
Qed.

Lemma balance_is_T :
  forall (A : Type) (c : color) (v : A) (l r : RBTree A),
    exists (c' : color) (v' : A) (l' r' : RBTree A),
      balance c l v r = T c' l' v' r'.
Proof.
  intros. functional induction @balance A c l v r; eauto 6.
Qed.

(*Ltac dst := repeat
match goal with
    | |- context [if ?x then _ else _] => destruct x
    | |- context [match ?x with _ => _ end] => destruct x
end; try apply T_not_E.*)

Lemma ins_not_E :
  forall (A : LinDec) (x : A) (t : RBTree A),
    ins x t <> E.
Proof.
  intros. functional induction @ins A x t;
  try apply T_not_E; apply balance_not_E.
Qed.

Inductive is_bst {A : LinDec} : RBTree A -> Prop :=
    | is_bst_E : is_bst E
    | is_bst_T : forall (c : color) (v : A) (l r : RBTree A),
        (forall x : A, elem x l -> leq x v) -> is_bst l ->
        (forall x : A, elem x r -> leq v x) -> is_bst r ->
        is_bst (T c l v r).

Hint Constructors is_bst.

Lemma color_is_bst :
  forall (A : LinDec) (c c' : color) (v : A) (l r : RBTree A),
    is_bst (T c l v r) <-> is_bst (T c' l v r).
Proof.
  split; intros; inv H.
Qed.

Hint Resolve elem_color.

(*Lemma balance_is_bst :
  forall (A : LinDec) (c : color) (v : A) (l r : RBTree A),
    is_bst (T c l v r) -> is_bst (balance c l v r).
Proof.
  intros. functional induction @balance (@carrier A) c l v r;
  try assumption.
    inv H. inv H5. inv H8. constructor; intros; auto.
      apply H3. eapply elem_color. eauto.
      inv H.
      apply H3.
      apply *)

(*Ltac bd := intros; repeat (match goal with
    | |- context [if ?x then _ else _] =>
        bdestruct (x); subst; cbn in *; try discriminate; auto
    | H : (?x <? ?y) = _ |- _ => destruct (blt_reflect x y); try congruence
    | H : ?x <> ?x |- _ => contradiction
    | H : ?x = ?x |- _ => clear H
    | H : ~ ?x < ?y, H' : ~ ?y < ?x |- _ =>
        assert (x = y) by (unfold key in *; omega); subst; clear H; clear H'
    | H : Abs E _ |- _ => inv H    
    | H : Abs (T _ _ _ _ _) _ |- _ => inv H
    | _ => auto; omega
end; st; cbn in *)

Ltac ext x := extensionality x.

Fixpoint toList' {A : Type} (t : RBTree A) (acc : list A) : list A :=
match t with
    | E => acc
    | T _ l v r => toList' l (v :: toList' r acc)
end.

Definition toList {A : Type} (t : RBTree A) : list A := toList' t [].

Function slow_toList {A : Type} (t : RBTree A) : list A :=
match t with
    | E => []
    | T _ l v r => slow_toList l ++ v :: slow_toList r
end.

Lemma aux :
  forall (A : Type) (t : RBTree A) (acc : list A),
    toList' t acc = slow_toList t ++ acc.
Proof.
  induction t; cbn; intros.
    trivial.
    rewrite IHt1, IHt2, <- app_assoc, <- app_comm_cons. trivial.
Qed.

Theorem toList_is_slow: @toList = @slow_toList.
Proof.
  ext A. ext t. unfold toList. rewrite aux. rewrite app_nil_r. trivial.
Qed.

Ltac gen H := generalize dependent H.

Fixpoint fromList {A : LinDec} (l : list A) : RBTree A :=
match l with
    | [] => E
    | h :: t => ins h (fromList t)
end.

Print fold_left.

Definition fromList' {A : LinDec} (l : list A) : RBTree A :=
  fold_left (fun t x => ins x t) l E.

Definition redblackSort (A : LinDec) (l : list A) : list A :=
  toList (fromList l).

Definition redblackSort' (A : LinDec) (l : list A) : list A :=
  toList (fromList' l).

Definition redblackSort'' (A : LinDec) (l : list A) : list A :=
  slow_toList (fromList' l).


Require Import ListLemmas.

Time Compute redblackSort natle (cycle 200 testl).
Time Compute redblackSort' natle (cycle 200 testl).
Time Compute redblackSort'' natle (cycle 200 testl).

(*
Lemma list2map_app_left :
  forall (al bl : list (key * V)) (i : key) v,
    In (i, v) al -> list2map (al ++ bl) (int2Z i) = list2map al (int2Z i).
Proof.
  induction al as [| h t]; cbn; intros; inv H.
    rewrite !t_update_eq. trivial.
    destruct h. destruct (Z.eq_dec (int2Z k) (int2Z i)).
      rewrite e. rewrite !t_update_eq. trivial.
      rewrite !t_update_neq; try inversion 1; auto. eauto.
Qed.

Lemma list2map_app_right :
  forall (al bl : list (key * V)) (i : Z),
    ~ (exists k v, int2Z k = i /\ In (k, v) al) ->
      list2map (al ++ bl) i = list2map bl i.
Proof.
  induction al as [| h t]; cbn; intros.
    trivial.
    destruct h. destruct (Z.eq_dec (int2Z k) i).
      subst. contradiction H. eauto.
      rewrite t_update_neq; auto.
        apply IHt. contradict H. decompose [ex and] H. eauto.
Qed.

Lemma list2map_app_not_in_default :
  forall (al : list (key * V)) (i : Z),
    ~ (exists k v, int2Z k = i /\ In (k, v) al) ->
      list2map al i = default.
Proof.
  induction al as [| h t]; cbn; intros.
    compute. trivial.
    destruct h. destruct (Z.eq_dec (int2Z k) i).
      subst. contradiction H. eauto.
      rewrite t_update_neq; auto.
        apply IHt. contradict H. decompose [ex and] H. eauto.
Qed.

Lemma no_elem_nil :
  forall (A : Type) (l : list A),
    ~ (exists x : A, In x l) -> l = [].
Proof.
  induction l as [| h t]; cbn; intro.
    trivial.
    cut False; [inversion 1 |]. apply H. eauto.
Qed.

Lemma no_elem_nil' :
  forall l : list (key * V),
    (forall k : key, ~ (exists v : V, In (k, v) l)) -> l = [].
Proof.
  intros. apply no_elem_nil. intro. destruct H0 as [[k v] H'].
  specialize (H k). firstorder.
Qed.

Theorem elements_relate :
  forall t m,
    SearchTree t -> Abs t m -> list2map (elements t) = m.
Proof.
  rewrite elements_slow_elements.
  intros until 1. inv H. gen m.
  induction H0; intros; bd.
  specialize (IHSearchTree'1 _ H6); clear H6.
  specialize (IHSearchTree'2 _ H7); clear H7.
  ext k'.
  destruct (In_decidable (slow_elements l) k') as [[k'' [v' [Heq Hin]]] |].
    rewrite <- Heq, list2map_app_left with (v := v'); auto. subst.
      assert (H' := slow_elements_range _ _ _ _ _ H0_ Hin).
      unfold t_update, combine; cbn. bd.
    destruct (In_decidable (slow_elements r) k') as [[k'' [v' [Heq Hin]]] |].
      rewrite -> list2map_app_right; auto.
        assert (H'' := slow_elements_range _ _ _ _ _ H0_0 Hin).
        unfold t_update, combine; subst; cbn. bd. rewrite t_update_neq; auto.
      subst.
        rewrite -> list2map_app_right; auto; cbn.
        apply list2map_app_not_in_default in H.
        apply list2map_app_not_in_default in H0.
        unfold t_update, combine; cbn. bd.
        destruct (Z_ltb_reflect k' (int2Z k)); bd.
Qed.

(* Ex. is_redblack *)
Inductive is_redblack : RBTree -> color -> nat -> Prop :=
    | IsRB_leaf : forall c, is_redblack E c 0
    | IsRB_r : forall l k v r n,
        is_redblack l Red n -> is_redblack r Red n ->
        is_redblack (T Red l k v r) Black n
    | IsRB_b : forall c l k v r n,
        is_redblack l Black n -> is_redblack r Black n ->
        is_redblack (T Black l k v r) c (S n).

Hint Constructors is_redblack.

Lemma is_redblack_toblack :
  forall t n, is_redblack t Red n -> is_redblack t Black n.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve is_redblack_toblack.

Inductive nearly_redblack : RBTree -> nat -> Prop :=
    | nrRB_r : forall l k v r n,
        is_redblack l Black n -> is_redblack r Black n ->
        nearly_redblack (T Red l k v r) n
    | nrRB_b : forall l k v r n,
        is_redblack l Black n -> is_redblack r Black n ->
        nearly_redblack (T Black l k v r) (S n).

Hint Constructors nearly_redblack.

Ltac irb := repeat
match goal with
    | H : is_redblack E _ _ |- _ => inv H
    | H : is_redblack (T _ _ _ _ _) _ _ |- _ => inv H
(*    | H : is_redblack (T _ _ _ _ _) _ (S _) |- _ => inv H*)
    | H : nearly_redblack E _ |- _ => inv H
    | H : nearly_redblack (T _ _ _ _ _) _ |- _ => inv H
end.

Lemma ins_is_redblack :
  forall k v t n,
    (is_redblack t Black n -> nearly_redblack (ins k v t) n) /\
    (is_redblack t Red n -> is_redblack (ins k v t) Black n).
Proof.
  Time induction t; cbn; split; intros; irb; bd;
  repeat match goal with
      | n : nat, IH : forall _ : nat, _ |- _ =>
          decompose [and] (IH n); clear IH
      | x : ?A, f : ?A -> _ |- _ => specialize (f x)
  end;
  dst; irb; st; repeat constructor; auto.
Qed.

Lemma insert_is_redblack :
  forall k v t n, is_redblack t Red n ->
    exists n', is_redblack (insert k v t) Red n'.
Proof.
  unfold insert.
  intros k v t. functional induction (ins k v t); cbn; intros; irb; st.
    exists 1%nat. eauto.
    decompose [ex] (balance_is_T Black (ins k v l) k0 v0 r).
      rewrite H. cbn. exists (S n0). econstructor. eauto.

Restart.
Ltac omg := repeat (cbn in *; match goal with
    | H : is_redblack E _ _ |- _ => inv H
    | H : is_redblack _ _ 0 |- _ => inv H
    | H : is_redblack (T _ _ _ _ _) _ _ |- _ => inv H
    | |- context [ltb ?x ?y] =>
        destruct (int_blt_reflect x y); try congruence
    | H : context [ltb ?x ?y] |- _ =>
        destruct (int_blt_reflect x y); try congruence; clear H
    | |- context [match (ins ?k ?v ?t) with _ => _ end] =>
        case_eq (ins k v t); intros
    | H : context [match (ins ?k ?v ?t) with _ => _ end] |- _ =>
        case_eq (ins k v t); intros
    | H : ins _ _ _ = E |- _ => apply ins_not_E in H; inv H
    | H : ins ?k ?v ?t = _, H' : context [ins ?k ?v ?t] |- _ =>
        rewrite H in H'
    | |- context [match ?x with _ => _ end] => destruct x
    | c : color |- _ => destruct c
    | H : context [match ?x with _ => _ end] |- _ => destruct x
    | H : ~ ?x < ?y, H' : ~ ?y < ?x |- _ =>
        assert (x = y) by (unfold key in *; omega); subst; clear H; clear H'
    | H : int2Z _ = int2Z _ |- _ => rewrite ?H in *
    | _ => try congruence; try omega; eauto
end).


  unfold insert. intros k v t n H. gen v; gen k.
  induction H; try (cbn; eauto; fail); intros.
    destruct
    (IHis_redblack1 k v) as [n1 H1],
    (IHis_redblack2 k v) as [n2 H2]. exists (S n). cbn. bd; constructor.
        apply ins_is_redblack. assumption.
        apply is_redblack_toblack. assumption.
        apply is_redblack_toblack. assumption.
        apply ins_is_redblack. assumption.
    destruct
    (IHis_redblack1 k v) as [n1 H1],
    (IHis_redblack2 k v) as [n2 H2]. exists (S n). cbn.
Admitted.

End TREES.
*)