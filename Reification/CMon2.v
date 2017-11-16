Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import ReificationBase.

Set Implicit Arguments.

Class CMon : Type :=
{
    carrier : Type;
    op : carrier -> carrier -> carrier;
    neutr : carrier;
    assoc : forall x y z : carrier, op x (op y z) = op (op x y) z;
    neutr_l : forall x : carrier, op neutr x = x;
    neutr_r : forall x : carrier, op x neutr = x;
    comm : forall x y : carrier, op x y = op y x
}.

Coercion carrier : CMon >-> Sortclass.

Inductive type (X : CMon) : Type :=
    | elem : type X
    | prop : type X.

Arguments elem [X].
Arguments prop [X].

Inductive exp {X : CMon} : type X -> Type :=
    | Id : exp elem
    | Var : nat -> exp elem
    | Op : exp elem -> exp elem -> exp elem
    | fFalse : exp prop
    | fTrue : exp prop
    | fEquiv : exp elem -> exp elem -> exp prop
    | fAnd : exp prop -> exp prop -> exp prop
    | fOr : exp prop -> exp prop -> exp prop
    | fImpl : exp prop -> exp prop -> exp prop.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments fEquiv [X] _ _.
Arguments fAnd [X] _ _.
Arguments fOr [X] _ _.
Arguments fImpl [X] _ _.

Definition typeDenote {X : CMon} (t : type X) : Type :=
match t with
    | elem => X
    | prop => Prop
end.

Fixpoint denote {X : CMon} {t : type X} (env : Env X)
  (f : exp t) : typeDenote t :=
match f with
    | Id => neutr
    | Var n => nth n env neutr
    | Op e1 e2 => op (denote env e1) (denote env e2)
    | fFalse => False
    | fTrue => True
    | fEquiv e1 e2 => denote env e1 = denote env e2
    | fAnd f1 f2 => denote env f1 /\ denote env f2
    | fOr f1 f2 => denote env f1 \/ denote env f2
    | fImpl f1 f2 => denote env f1 -> denote env f2
end.

Fixpoint simplifyExp {X : CMon} (e : exp elem) : exp elem :=
match e with
    | Id => Id
    | Var v => Var v
    | Op e1 e2 =>
        match simplifyExp e1, simplifyExp e2 with
            | Id, e2' => e2'
            | e1', Id => e1'
            | e1', e2' => Op e1' e2'
        end
end.

Theorem simplifyExp_correct :
  forall (X : CMon) (env : Env X) (e : exp elem),
    denote env (simplifyExp e) = denote env e.
Proof.
  dependent induction e; cbn.
    reflexivity.
    reflexivity.
    remember (simplifyExp e1) as s1. remember (simplifyExp e2) as s2.
      specialize (IHe1 _ eq_refl JMeq_refl);
      specialize (IHe2 _ eq_refl JMeq_refl).
      dependent destruction s1; dependent destruction s2; cbn in *;
      rewrite <- ?IHe1, <- ?IHe2, <- ?Heqs1, <- ?Heqs2; cbn;
      rewrite ?neutr_l, ?neutr_r; reflexivity.
Qed.

Function denoteL {X : CMon} (env : Env X) (l : list nat) : X :=
match l with
    | [] => neutr
    | h :: t => op (nth h env neutr) (denoteL env t)
end.

Lemma denoteL_app :
  forall (X : CMon) (env : Env X) (l1 l2 : list nat),
    denoteL env (l1 ++ l2) = op (denoteL env l1) (denoteL env l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite IHt1, ?neutr_r, ?assoc. trivial.
Qed.

Fixpoint flatten {X : CMon} (e : exp elem) : list nat :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
end.

Theorem flatten_correct :
  forall (X : CMon) (env : Env X) (e : exp elem),
    denoteL env (flatten e) = denote env e.
Proof.
  dependent induction e; cbn.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite denoteL_app. rewrite IHe1, IHe2; reflexivity.
Qed.

Lemma denoteL_Permutation :
  forall (X : CMon) (env : Env X) (l1 l2 : list nat),
    Permutation l1 l2 -> denoteL env l1 = denoteL env l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    rewrite !assoc. rewrite (comm (nth y env neutr)). reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Theorem sort_correct :
  forall (X : CMon) (env : Env X) (l : list nat) (s : Sort),
    denoteL env (s natle l) = denoteL env l.
Proof.
  intros. apply denoteL_Permutation. apply (perm_Permutation natle).
  rewrite <- sort_perm. reflexivity.
Qed.

Function list_to_exp {X : CMon} (l : list nat) : exp elem :=
match l with
    | [] => Id
    | [x] => Var x
    | h :: t => Op (Var h) (list_to_exp t)
end.

Theorem list_to_exp_correct :
  forall (X : CMon) (env : Env X) (l : list nat),
    denote env (list_to_exp l) = denoteL env l.
Proof.
  intros. functional induction list_to_exp l; cbn.
    trivial.
    rewrite neutr_r. trivial.
    rewrite IHe. trivial.
Qed.

Definition simplify {X : CMon} (e : exp elem) : exp elem :=
  list_to_exp (insertionSort natle (flatten (simplifyExp e))).

Theorem simplify_correct :
  forall (X : CMon) (env : Env X) (e : exp elem),
    denote env (simplify e) = denote env e.
Proof.
  unfold simplify. intros.
  rewrite !list_to_exp_correct.
  rewrite !(sort_correct _ _ _ Sort_insertionSort).
  erewrite !flatten_correct, !simplifyExp_correct.
  trivial.
Qed.

Theorem reflectEq :
  forall (X : CMon) (env : Env X) (e1 e2 : exp elem),
    denote env (simplify e1) = denote env (simplify e2) ->
      denote env e1 = denote env e2.
Proof.
  intros. rewrite !simplify_correct in H. assumption.
Qed.

Fixpoint solve
  {X : CMon} (env : Env X) (f : exp prop)
  : option (denote env f).
Proof.
  dependent destruction f; cbn.
    apply None.
    apply Some. trivial.
    apply None.
    destruct (solve X env f1), (solve X env f2).
      apply Some. split; assumption.
      1-3: apply None.
    destruct (solve X env f1).
      apply Some. left. assumption.
      destruct (solve X env f2).
        apply Some. right. assumption.
        apply None.
    destruct (solve X env f2).
      apply Some. intro. assumption.
      apply None.
Defined.

Theorem solve_spec :
  forall (X : CMon) (env : Env X) (f : exp prop),
    (exists p : denote env f, solve env f = Some p) ->
      denote env f.
Proof.
  intros. destruct H. assumption.
Qed.

Definition simplifyFormula {X : CMon} (t : type X) : exp t -> exp t :=
match t with
    | elem => fun e => simplify e
    | prop => fun e =>
        match e with
            | fEquiv e1 e2 => fEquiv (simplify e1) (simplify e2)
            | _ => e
        end
end.

Theorem simplifyFormula_correct :
  forall (X : CMon) (t : type X) (env : Env X) (e : exp t),
    denote env (simplifyFormula e) = denote env e.
Proof.
  destruct t; cbn; intros.
    rewrite simplify_correct. trivial.
    dependent destruction e; trivial.
      cbn. rewrite !simplify_correct. trivial.
Qed.

Theorem reflectFormula :
  forall (X : CMon) (env : Env X) (e : exp prop),
    denote env (simplifyFormula e) -> denote env e.
Proof.
  dependent induction e; cbn; trivial.
    rewrite !simplify_correct. trivial.
Qed.

Ltac allVars X xs e :=
match e with
    | op ?e1 ?e2 =>
        let xs' := allVars X xs e2 in allVars X xs' e1
    | ?a = ?b =>
        let xs' := allVars X xs b in allVars X xs' a
    | ~?P => allVars xs P
    | ?P1 /\ ?P2 =>
        let xs' := allVars X xs P2 in allVars X xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVars X xs P2 in allVars X xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVars X xs P2 in allVars X xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVars X xs P2 in allVars X xs' P1
    | _ =>
        match type of e with
            | X => addToList e xs
        end
end.

Ltac reify env e :=
match e with
    | neutr => constr:(Id)
    | op ?a ?b =>
        let e1 := reify env a in
        let e2 := reify env b in constr:(Op e1 e2)
    | False => constr:(fFalse)
    | True => constr:(fTrue)
    | ?a = ?b =>
        let e1 := reify env a in
        let e2 := reify env b in constr:(fEquiv e1 e2)
    | ~?P =>
        let e' := reify env P in constr:(fImpl e' fFalse)
    | ?P1 /\ ?P2 =>
        let e1 := reify env P1 in
        let e2 := reify env P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reify env P1 in
        let e2 := reify env P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reify env P1 in
        let e2 := reify env P2 in constr:(fImpl e1 e2)
    | ?P1 <-> ?P2 =>
        let e1 := reify env P1 in
        let e2 := reify env P2 in constr:(fAnd (fImpl e1 e2) (fImpl e2 e1))
    | _ =>
        let n := lookup e env in constr:(Var n)
end.

Ltac reflectGoal :=
match goal with
    | X : CMon |- ?P =>
        let env := allVars (@carrier X) constr:(@nil X) P in
        let e := reify env P in
          change (denote env e);
          apply reflectFormula; cbn
end.

Ltac cmon_simpl := cbn; intros; subst;
match goal with
    | X : CMon |- ?a = ?b => reflectGoal
end.

Ltac cmon := cmon_simpl; reflexivity.