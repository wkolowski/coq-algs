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

Inductive exp (X : CMon) : Type :=
    | Id : exp X
    | Var : nat -> exp X
    | Op : exp X -> exp X -> exp X.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.

Fixpoint expDenote {X : CMon} (env : Env X) (e : exp X) : X :=
match e with
    | Id => neutr
    | Var n => nth n env neutr
    | Op e1 e2 => op (expDenote env e1) (expDenote env e2)
end.

Function simplifyExp {X : CMon} (e : exp X) : exp X :=
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
  forall (X : CMon) (env : Env X) (e : exp X),
    expDenote env (simplifyExp e) = expDenote env e.
Proof.
  intros. functional induction simplifyExp e; cbn;
  rewrite <- ?IHe, <- ?IHe0, <- ?IHe1, ?e3, ?e4; cbn;
  rewrite ?neutr_l, ?neutr_r; trivial.
Qed.

Fixpoint expDenoteL {X : CMon} (env : Env X) (l : list nat) : X :=
match l with
    | [] => neutr
    | h :: t => op (nth h env neutr) (expDenoteL env t)
end.

Lemma expDenoteL_app :
  forall (X : CMon) (env : Env X) (l1 l2 : list nat),
    expDenoteL env (l1 ++ l2) = op (expDenoteL env l1) (expDenoteL env l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Lemma expDenoteL_Permutation :
  forall (X : CMon) (env : Env X) (l1 l2 : list nat),
    Permutation l1 l2 -> expDenoteL env l1 = expDenoteL env l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    rewrite !assoc. rewrite (comm (nth y env neutr)). reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Fixpoint flatten {X : CMon} (e : exp X) : list nat :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
end.

Theorem flatten_correct :
  forall (X : CMon) (env : Env X) (e : exp X),
    expDenoteL env (flatten e) = expDenote env e.
Proof.
  induction e; simpl.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite expDenoteL_app. rewrite IHe1, IHe2. reflexivity.
Qed.

Theorem sort_correct :
  forall (X : CMon) (env : Env X) (l : list nat) (s : Sort),
    expDenoteL env (s natle l) = expDenoteL env l.
Proof.
  intros. apply expDenoteL_Permutation. apply (perm_Permutation natle).
  rewrite <- sort_perm. reflexivity.
Qed.

Definition simplify {X : CMon} (e : exp X) : list nat :=
  insertionSort natle (flatten (simplifyExp e)).

Theorem simplify_correct :
  forall (X : CMon) (env : Env X) (e : exp X),
    expDenoteL env (simplify e) = expDenote env e.
Proof.
  unfold simplify. intros.
  rewrite !(sort_correct _ _ _ Sort_insertionSort).
  rewrite !flatten_correct, !simplifyExp_correct.
  trivial.
Qed.

Theorem reflectEq :
  forall (X : CMon) (env : Env X) (e1 e2 : exp X),
    expDenoteL env (simplify e1) = expDenoteL env (simplify e2) ->
      expDenote env e1 = expDenote env e2.
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
      constr:(expDenote env e1 = expDenote env e2).

Ltac reflectGoal' := cbn; intros; subst;
match goal with
    | X : CMon |- ?a = ?b =>
        let xs := allVarsExp constr:(@nil X) b in
        let xs' := allVarsExp xs a in
        let e := reifyEq xs' a b in
          change e; apply reflectEq; cbn; rewrite ?neutr_l, ?neutr_r
end.

Ltac reflectGoal := reflectGoal; reflexivity.

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

End Test.