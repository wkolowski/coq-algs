Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import Arith.
Require Import Permutation.
Require Import Perm.
Require Import InsertionSort.

Require Import List.
Import ListNotations.

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
    | fVar : nat -> exp prop
    | fEquiv : exp elem -> exp elem -> exp prop
    | fNot : exp prop -> exp prop
    | fAnd : exp prop -> exp prop -> exp prop
    | fOr : exp prop -> exp prop -> exp prop
    | fImpl : exp prop -> exp prop -> exp prop.

Arguments Id [X].
Arguments Var [X] _.
Arguments Op [X] _ _.
Arguments fVar [X] _.
Arguments fEquiv [X] _ _.
Arguments fNot [X] _.
Arguments fAnd [X] _ _.
Arguments fOr [X] _ _.
Arguments fImpl [X] _ _.

Definition typeDenote {X : CMon} (t : type X) : Type :=
match t with
    | elem => X
    | prop => Prop
end.

Fixpoint denote {X : CMon} {t : type X} (envE : nat -> X) (envP : nat -> Prop)
  (f : exp t) : typeDenote t :=
match f with
    | Id => neutr
    | Var n => envE n
    | Op e1 e2 => op (denote envE envP e1) (denote envE envP e2)
    | fVar i => envP i
    | fEquiv e1 e2 => denote envE envP e1 = denote envE envP e2
    | fNot f' => ~ denote envE envP f'
    | fAnd f1 f2 => denote envE envP f1 /\ denote envE envP f2
    | fOr f1 f2 => denote envE envP f1 \/ denote envE envP f2
    | fImpl f1 f2 => denote envE envP f1 -> denote envE envP f2
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

Require Import Equality.

Theorem simplifyExp_correct :
  forall (X : CMon) (envE : nat -> X) (envP : nat -> Prop) (e : exp elem),
    denote envE envP (simplifyExp e) ~= denote envE envP e.
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

Fixpoint denoteL {X : CMon} (envE : nat -> X) (l : list nat) : X :=
match l with
    | [] => neutr
    | h :: t => op (envE h) (denoteL envE t)
end.

Lemma denoteL_app :
  forall (X : CMon) (envE : nat -> X) (l1 l2 : list nat),
    denoteL envE (l1 ++ l2) = op (denoteL envE l1) (denoteL envE l2).
Proof.
  induction l1 as [| h1 t1]; simpl; intros.
    rewrite neutr_l. reflexivity.
    rewrite <- assoc, IHt1. reflexivity.
Qed.

Fixpoint flatten {X : CMon} (e : exp elem) : list nat :=
match e with
    | Id => []
    | Var v => [v]
    | Op e1 e2 => flatten e1 ++ flatten e2
end.

Theorem flatten_correct :
  forall (X : CMon) (envE : nat -> X) (envP : nat -> Prop) (e : exp elem),
    denoteL envE (flatten e) = denote envE envP e.
Proof.
  dependent induction e; cbn.
    reflexivity.
    rewrite neutr_r. reflexivity.
    rewrite denoteL_app. rewrite IHe1, IHe2; reflexivity.
Qed.

Lemma denoteL_Permutation :
  forall (X : CMon) (env : nat -> X) (l1 l2 : list nat),
    Permutation l1 l2 -> denoteL env l1 = denoteL env l2.
Proof.
  induction 1; cbn.
    reflexivity.
    rewrite IHPermutation. reflexivity.
    rewrite !assoc. rewrite (comm (env y)). reflexivity.
    rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Theorem sort_correct :
  forall (X : CMon) (env : nat -> X) (l : list nat) (s : Sort),
    denoteL env (s natle l) = denoteL env l.
Proof.
  intros. apply denoteL_Permutation. apply (perm_Permutation natle).
  rewrite <- sort_perm. reflexivity.
Qed.

Definition simplify {X : CMon} (e : exp elem) : list nat :=
  insertionSort natle (flatten (simplifyExp e)).

Theorem simplify_correct :
  forall (X : CMon) (envE : nat -> X) (envP : nat -> Prop) (e1 e2 : exp elem),
    denoteL envE (simplify e1) = denoteL envE (simplify e2) ->
      denote envE envP e1 = denote envE envP e2.
Proof.
  unfold simplify. intros.
  rewrite !(sort_correct X envE _ Sort_insertionSort) in H.
  erewrite !flatten_correct, !simplifyExp_correct in H.
  eassumption.
Qed.

Ltac inList x l :=
match l with
    | [] => false
    | x :: _ => true
    | _ :: ?l' => inList x l'
end.

Ltac addToList x l :=
  let b := inList x l in
match b with
    | true => l
    | false => constr:(x :: l)
end.

Ltac lookup x l :=
match l with
    | x :: _ => constr:(0)
    | _ :: ?l' => let n := lookup x l' in constr:(S n)
end.

Ltac allVars xs e :=
match e with
    | op ?e1 ?e2 =>
        let xs' := allVars xs e2 in allVars xs' e1
    | ?f ?e' => allVars xs e'
    | _ => addToList e xs
end.

Ltac reifyTerm env x :=
match x with
    | neutr => constr:(Id)
    | op ?a ?b =>
        let e1 := reifyTerm env a in
        let e2 := reifyTerm env b in constr:(Op e1 e2)
    | _ =>
        let n := lookup x env in constr:(Var n)
end.

Ltac functionalize l X :=
let rec loop n l' :=
    match l' with
        | [] => constr:(fun _ : nat => @neutr X)
        | ?h :: ?t =>
            let f := loop (S n) t in
            constr:(fun m : nat => if m =? n then h else f m)
    end
in loop 0 l.

Ltac reify X :=
match goal with
    | |- ?e1 = ?e2 =>
        let xs := allVars constr:(@nil X) e1 in
        let xs' := allVars xs e2 in
        let r1 := reifyTerm xs' e1 in
        let r2 := reifyTerm xs' e2 in
        let env := functionalize xs' X in
        change (denote env (fun _ => False) r1 =
                denote env (fun _ => False) r2)
end.

Ltac reifyEqv X env a b :=
    let e1 := reifyTerm env a in
    let e2 := reifyTerm env b in constr:((e1, e2)).

Ltac cmon_subst := repeat
multimatch goal with
    | H : ?x = ?y |- _ => rewrite <- ?H in *
    | H : ?x = ?x |- _ => clear H
end.

Ltac reflect_cmon' := cbn; intros; cmon_subst;
match goal with
    | X : CMon |- ?e1 = ?e2 =>
        reify X; apply simplify_correct; cbn; rewrite ?neutr_l, ?neutr_r
end.

Ltac reflect_cmon := reflect_cmon'; try reflexivity.

Ltac reflect_goal := simpl; intros;
match goal with
    | X : CMon |- ?e1 = ?e2 =>
        reify X; apply simplify_correct
end.

Goal forall (X : CMon) (a b c : X),
  op a (op b c) = op (op a b) c.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : CMon) (a b : X),
  op a b = op b a.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : CMon) (a b b' c : X),
  b = b' -> op a (op b c) = op (op a b') c.
Proof.
  reflect_cmon.
Qed.

Goal forall (X : CMon) (a a' b b' c c' : X),
  op a b = op a b' -> op (op a b) c = op b' (op a c).
Proof.
  reflect_cmon'. rewrite ?assoc. rewrite (comm b').
  rewrite !H. reflect_cmon.
Qed.

Goal forall (X : CMon) (a a' b b' c c' : X),
  a = b -> b = c -> c = a -> op b (op a c) = op a (op neutr (op b c)).
Proof.
  reflect_cmon'. reflexivity.
Qed.

Ltac allVarsFormula xs P :=
match P with
    | ?a = ?b => allVars xs P
    | ~ ?P' => allVarsFormula xs P'
    | ?P1 /\ ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | ?P1 \/ ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | ?P1 -> ?P2 =>
        let xs' := allVarsFormula xs P1 in
          allVarsFormula xs' P2
    | _ => xs
end.

Ltac reifyFormula X xs P :=
match P with
    | ~ ?P' =>
        let e := reifyFormula X xs P' in constr:(fNot e)
    | ?a = ?b =>
        let e1 := reifyTerm xs a in
        let e2 := reifyTerm xs b in constr:(fEquiv e1 e2)
    | ?P1 /\ ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fAnd e1 e2)
    | ?P1 \/ ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fOr e1 e2)
    | ?P1 -> ?P2 =>
        let e1 := reifyFormula X xs P1 in
        let e2 := reifyFormula X xs P2 in constr:(fImpl e1 e2)
    | _ => constr:(fVar X P)
end.

Ltac reifyGoal :=
match goal with
    | X : CMon |- ?P =>
        let xs := allVarsFormula constr:(@nil X) P in
        let envE := functionalize xs X in
        let e := reifyFormula X xs P in change (denote envE (fun _ => False) e)
end.

Definition list_eq :
  forall (l1 l2 : list nat), {l1 = l2} + {l1 <> l2}.
Proof.
  do 2 decide equality.
Defined.

Fixpoint solve
  {X : CMon} (envE : nat -> X) (envP : nat -> Prop) (f : exp prop)
  : option (denote envE envP f).
Proof.
  dependent destruction f; cbn.
    apply None.
    destruct (list_eq
              (insertionSort natle (flatten (simplifyExp f1)))
              (insertionSort natle (flatten (simplifyExp f2)))).
      apply Some. apply simplify_correct. f_equal. assumption.
      apply None.
    apply None.
    destruct (solve X envE envP f1), (solve X envE envP f2).
      apply Some. split; assumption.
      1-3: apply None.
    destruct (solve X envE envP f1).
      apply Some. left. assumption.
      destruct (solve X envE envP f2).
        apply Some. right. assumption.
        apply None.
    destruct (solve X envE envP f2).
      apply Some. intro. assumption.
      apply None.
Defined.

Theorem solve_spec :
  forall (X : CMon) (envE : nat -> X) (envP : nat -> Prop) (f : exp prop),
    (exists p : denote envE envP f, solve envE envP f = Some p) ->
      denote envE envP f.
Proof.
  intros. destruct H. assumption.
Qed.

Ltac solve_goal' :=
  cbn; intros; cmon_subst; reifyGoal;
  apply solve_spec; cbn; eauto.

Ltac solve_goal :=
  try (solve_goal'; fail);
  fail "Cannot solve the goal".

Goal forall (X : CMon) (a a' b b' c c' : X),
  a = b -> b = c -> c = a -> a = c /\ op c c = op b b.
Proof.
  Require Import Quote.
  intros. Print denote.
  cbn; intros; cmon_subst. reifyGoal. apply solve_spec; cbn. cbn.
  Print Assumptions simplify_correct. compute. eexists.
  assert (forall (A : Type) (x : A) (p : x = x), p = eq_refl x).
Abort.