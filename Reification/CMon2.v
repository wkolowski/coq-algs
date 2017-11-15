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
(*    | fVar : nat -> exp prop*)
    | fFalse : exp prop
    | fTrue : exp prop
    | fEquiv : exp elem -> exp elem -> exp prop
(*    | fNot : exp prop -> exp prop*)
    | fAnd : exp prop -> exp prop -> exp prop
    | fOr : exp prop -> exp prop -> exp prop
    | fImpl : exp prop -> exp prop -> exp prop.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
(*Arguments fVar [X] _.*)
Arguments fEquiv [X] _ _.
(*Arguments fNot [X] _.*)
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
(*    | fVar i => nth i False*)
    | fFalse => False
    | fTrue => True
    | fEquiv e1 e2 => denote env e1 = denote env e2
(*    | fNot f' => ~ denote env f'*)
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

Definition simplify {X : CMon} (e : exp elem) : list nat :=
  insertionSort natle (flatten (simplifyExp e)).

Theorem simplify_correct :
  forall (X : CMon) (env : Env X) (e : exp elem),
    denoteL env (simplify e) = denote env e.
Proof.
  unfold simplify. intros.
  rewrite !(sort_correct _ _ _ Sort_insertionSort).
  erewrite !flatten_correct, !simplifyExp_correct.
  trivial.
Qed.

Theorem reflectEq :
  forall (X : CMon) (env : Env X) (e1 e2 : exp elem),
    denoteL env (simplify e1) = denoteL env (simplify e2) ->
      denote env e1 = denote env e2.
Proof.
  intros. rewrite !simplify_correct in H. assumption.
Qed.

Ltac allVarsExp xs e :=
match e with
    | op ?e1 ?e2 =>
        let xs' := allVarsExp xs e2 in allVarsExp xs' e1
    | _ => addToList e xs
end.

Ltac reifyExp env x :=
match x with
    | neutr => constr:(Id)
    | op ?a ?b =>
        let e1 := reifyExp env a in
        let e2 := reifyExp env b in constr:(Op e1 e2)
    | _ =>
        let n := lookup x env in constr:(Var n)
end.

Ltac reifyEq env a b :=
    let e1 := reifyExp env a in
    let e2 := reifyExp env b in
      constr:(denote env e1 = denote env e2).

Ltac reflectGoal' := cbn; intros; subst;
match goal with
    | X : CMon |- ?a = ?b =>
        let xs := allVarsExp constr:(@nil X) b in
        let xs' := allVarsExp xs a in
        let e := reifyEq xs' a b in
          change e; apply reflectEq; cbn; rewrite ?neutr_l, ?neutr_r
end.

Ltac reflectGoal := reflectGoal; reflexivity.

Ltac allVarsFormula xs P :=
match P with
    | ?a = ?b =>
        let xs' := allVarsExp xs b in allVarsExp xs' a
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | ?P1 <-> ?P2 =>
        let xs' := allVarsFormula xs P2 in allVarsFormula xs' P1
    | _ => xs
end.

Ltac reifyFormula xs P :=
match P with
    | ?a = ?b =>
        let e1 := reifyExp xs a in
        let e2 := reifyExp xs b in constr:(fEquiv e1 e2)
    | ~ ?P' =>
        let e := reifyFormula xs P' in constr:(fImpl e fFalse)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in constr:(fImpl e1 e2)
    | ?P1 <-> ?P2 =>
        let e1 := reifyFormula xs P1 in
        let e2 := reifyFormula xs P2 in
          constr:(fAnd (fImpl e1 e2) (fImpl e2 e1))
end.

Ltac reifyGoal :=
match goal with
    | X : CMon |- ?P =>
        let xs := allVarsFormula constr:(@nil X) P in
        let e := reifyFormula xs P in change (denote xs e)
end.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solve
  {X : CMon} (env : Env X) (f : exp prop)
  : option (denote env f).
Proof.
  dependent destruction f; cbn.
    apply None.
    apply Some. trivial.
    destruct (list_eq
              (insertionSort natle (flatten (simplifyExp f1)))
              (insertionSort natle (flatten (simplifyExp f2)))).
      apply Some. apply reflectEq. f_equal. assumption.
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

Axiom JMeq_eq_refl :
  forall (A : Type) (x : A) (p : x ~= x),
    @JMeq_eq A x x p = eq_refl x.

(*Ltac solve_goal' :=
  cbn; intros; cmon_subst; reifyGoal; apply solve_spec;
  repeat (try eexists; compute; rewrite ?JMeq_eq_refl); eauto.

Ltac solve_goal :=
  try (solve_goal'; fail);
  fail "Cannot solve the goal".*)

Section Test.

Variable (X : CMon) (a a' b b' c c' d e f : X).

(* [CMon] axioms. *)
Goal op a (op b c) = op (op a b) c.
Proof. reflectGoal'. reflexivity. Qed.

Goal op neutr a = a.
Proof. reflectGoal'. reflexivity. Qed.

Goal op a neutr = a.
Proof. reflectGoal'. reflexivity. Qed.

Goal op a b = op b a.
Proof. reflectGoal'. reflexivity. Qed.

Goal op a (op (op b c) (op d (op (op e e) d))) =
     op (op a d) (op d (op c (op e (op e b)))).
Proof. reflectGoal'. reflexivity. Qed.

(* Other tests. *)
Goal b = b' -> op a (op b c) = op (op a b') c.
Proof. reflectGoal'. reflexivity. Qed.

Goal op a b = op a b' -> op (op a b) c = op b' (op a c).
Proof.
  reflectGoal'. rewrite ?assoc. rewrite (comm b').
  rewrite <- !H. reflectGoal'. reflexivity.
Qed.

Goal a = b -> b = c -> c = a -> op b (op a c) = op a (op neutr (op b c)).
Proof. reflectGoal'. reflexivity. Qed.

(* Tests for formulas. *)
Goal a = b -> b = c -> c = a -> a = c /\ op c c = op b b.
Proof.
  intros. split.
    reflectGoal'. reflexivity.
    reflectGoal'. reflexivity. 
Qed.

End Test.