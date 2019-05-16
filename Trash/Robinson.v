Require Import List.
Require Import Nat.
Require Import Arith.

Require Import Classes.RelationClasses.
Require Import Relations.Relation_Operators.

Require Import Program.Tactics.
Require Import Program.Wf.
Require Import Wellfounded.Lexicographic_Product.
Require Import Wellfounded.Inverse_Image.

Require Import MSets.MSetFacts.
Require Import MSets.MSetProperties.
Require Import MSets.MSetWeakList.

Require Import Structures.Equalities.

Module RobinsonUnificationWf.

Set Implicit Arguments.

Definition VarId := nat.
Definition SymId := nat.

Inductive Tm : Set :=
    | Var : forall x : VarId, Tm
    | App : forall (f : SymId) (xs : list Tm), Tm.

Section All.

Variable T : Type.
Variable P : T -> Type.

Inductive ForallT : list T -> Type :=
    | ForallT_nil : ForallT nil
    | ForallT_cons : forall (x : T) (l : list T),
        P x -> ForallT l -> ForallT (x::l).

End All.

Section Recursor.

Variable P : Tm -> Type.

Variable PVar: forall x, P (Var x).
Variable PApp: forall f xs, ForallT P xs -> P (App f xs) .

Fixpoint Tm_list_rect (tm:Tm) {struct tm} : P tm :=
match tm with
| Var x => PVar x
| App f xs => 
  let onList := fix onList (ts:list Tm) : ForallT P ts := 
  match ts as TS return ForallT P TS with
  | nil =>
    ForallT_nil P 
  | t :: ts =>
    let proof := Tm_list_rect t in
    let rest := onList ts in
    @ForallT_cons Tm P t ts proof rest 
  end 
  in PApp f (onList xs)
end.

End Recursor.

Definition Stack : Set := list (Tm  * Tm).
Definition Subst := (VarId * Tm) % type.
Definition VarMap : Set := list Subst.

Fixpoint Tm_eq_dec (x y: Tm): {x = y} + {x <> y}.
Proof.
  intros.
  decide equality.
    apply Nat.eq_dec.
    apply list_eq_dec. apply Tm_eq_dec.
    apply Nat.eq_dec.
Defined.

Module VarIdDecidableType <: DecidableType.

  Definition t := nat.
  Definition eq := @eq t.

  Instance eq_equiv : Equivalence eq .
  Proof.
    constructor.
      constructor.
      intros x y; intros; symmetry; auto.
      intros x y z; intros HA HB. transitivity y; auto.
  Qed.

  Definition eq_dec := Nat.eq_dec.

End VarIdDecidableType.

Module MVarSet := MSetWeakList.Make(VarIdDecidableType).
Module MVarProp.
  Module Props := WPropertiesOn(VarIdDecidableType)(MVarSet).
  Include Props.
End MVarProp.

Definition VarSet := MVarSet.t.

Inductive HasVar (x:VarId) : Tm -> Prop :=
    | HasVar_var : HasVar x (Var x)
    | HasVar_app: forall (f : SymId) (ts : list Tm) (t : Tm),
        HasVar x t -> In t ts -> HasVar x (App f ts).

Hint Constructors HasVar.

Fixpoint applySubstToVar (x : VarId) (sb : Subst) :=
match sb with
    | (y, t) => if Nat.eq_dec x y then t else Var x
end.

Fixpoint applySubst (subst:Subst) (term:Tm) {struct term} :=
match term with
| Var x => applySubstToVar x subst
| App f xs => 
  let applySubst' := fix applySubst' ts :=
    match ts with
    | nil => nil
    | t :: ts => applySubst subst t :: applySubst' ts
    end
  in 
  App f (applySubst' xs)
end
.

Fixpoint applySubstTms (subst:Subst) (ts: list Tm) := 
    match ts with
    | nil => nil
    | t :: ts => applySubst subst t :: applySubstTms subst ts
    end.

Lemma applySubst_app: forall f ts subst,
  applySubst subst (App f ts) = App f (applySubstTms subst ts).
Proof.
  intros; destruct ts.
  + trivial.
  + simpl. 
    f_equal. f_equal.
    induction ts.
      - trivial.
      - simpl. f_equal. apply IHts.
Qed.

Fixpoint applySubstToStack subst stack :=
match stack with
| nil => nil
| (t0, t1) :: stack => 
  (applySubst subst t0, applySubst subst t1) :: applySubstToStack subst stack
end.

Fixpoint applySubstToVarMap subst sb : VarMap :=
match sb with
| nil => nil 
| (x,t) :: sb => 
  (x, applySubst subst t) :: applySubstToVarMap subst sb
end.

Definition hasVar (x:VarId) (term:Tm) : {HasVar x term} + {~ HasVar x term}.
Proof.
  induction term using Tm_list_rect.
  + destruct Nat.eq_dec with x x0; subst.
    - left; auto.
    - right; intro HH.
      inversion HH; auto.
  + induction xs.
    - right; intro HH.
      inversion HH; subst. inversion H3.
    - inversion H; subst.
      destruct H2.
      * left. constructor 2 with a. assumption. constructor 1; auto.
      * specialize (IHxs H3).
        destruct IHxs.
        ** left. inversion h; subst. constructor 2 with t. eauto.
           constructor 2. auto.
        ** right. intro HH. inversion HH; subst. inversion H4; subst.
            *** apply n; auto.
            *** apply n0; eauto.
Defined.

Fixpoint zip (xs:list Tm) (ys:list Tm) stack {struct xs} : option Stack :=
match xs, ys with
| nil, nil => Some stack
| x :: xs, y :: ys => 
  zip xs ys (pair x y :: stack)
| _, _ =>
  None
end.

Fixpoint size (t : Tm) : nat :=
match t with 
| Var _ => 1 
| App f xs => 
  let onList := fix onList (ts:list Tm) :=
  match ts with
  | nil => 1
  | t :: ts => size t + onList ts
  end
  in onList xs
end.

Fixpoint fvTm (t:Tm) : VarSet :=
match t with
    | Var x => MVarSet.singleton x
    | App f ts => 
        let onList := fix onList (ts : list Tm) : VarSet := 
          match ts with
              | nil => MVarSet.empty
              | t :: ts => MVarSet.union (fvTm t) (onList ts)
          end
        in onList ts 
end.

Fixpoint fvTms (ts : list Tm) :=
match ts with
    | nil => MVarSet.empty
    | t :: ts => MVarSet.union (fvTm t) (fvTms ts)
end.

Lemma fvTm_app: forall f xs,
  fvTm (App f xs) = fvTms xs.
Proof.
  induction xs; auto.
Qed.

Lemma fvTms_cons: forall t ts,
  fvTms (t :: ts) = MVarSet.union (fvTm t) (fvTms ts).
Proof.
  intros. simpl. reflexivity. 
Qed.

Fixpoint stackSize (stack : Stack) : nat := 
match stack with
| (t0, t1) :: stack => size t0 + size t1 + stackSize stack 
| nil => 0
end.

Fixpoint fvStack (stack : Stack) : VarSet := 
match stack with
| nil => MVarSet.empty
| (t0, t1) :: stack =>
    MVarSet.union (fvTm t0) (MVarSet.union (fvTm t1) (fvStack stack))
end.

Definition fvStackCard stack := MVarSet.cardinal (fvStack stack).

Definition stackMeasure (stack: Stack) : nat * nat :=
  (fvStackCard stack, stackSize stack).

Definition natnatlt (a0: nat * nat) (a1: nat * nat) : Prop := 
  lexprod nat (fun n => nat) lt (fun _ => lt)
   (existT _ (fst a0) (snd a0))
   (existT _ (fst a1) (snd a1)).

Definition natnatlt_wf : well_founded natnatlt.
Proof.
  unfold natnatlt.
  eapply wf_inverse_image.
  eapply wf_lexprod.
    apply lt_wf.
  intro; apply lt_wf.
Defined.

Definition stacklt stack0 stack1 :=
  natnatlt (stackMeasure stack0) (stackMeasure stack1).

Definition stacklt_wf : well_founded stacklt :=
  wf_inverse_image Stack (nat*nat) natnatlt stackMeasure natnatlt_wf.

Lemma size_gt0: forall t, size t > 0.
Proof.
  induction t using Tm_list_rect; simpl.
  + auto.
  + induction xs; simpl.
    - auto.
    - inversion H. eauto with arith.
Qed.

Lemma fvStackCard_monotone1: forall t0 t1 stack,
  fvStackCard stack <= fvStackCard ((t0, t1) :: stack).
Proof.
  intros.
  unfold fvStackCard. simpl.
  apply MVarProp.subset_cardinal.
  eapply MVarProp.subset_trans.
  apply MVarProp.union_subset_2.
  eapply MVarProp.subset_trans.
  apply MVarProp.union_subset_2.
  apply MVarProp.union_subset_5.
  apply MVarProp.union_subset_5.
  apply MVarProp.subset_refl.
Qed.

Lemma natnatlt_trans :
  forall a b c, natnatlt a b -> natnatlt b c -> natnatlt a c.
Proof.
  intros.
  inversion H; inversion H0; subst.
  + apply left_lex. eapply lt_trans; eauto.
  + apply left_lex. eapply lt_le_trans; eauto. rewrite H9; auto.
  + apply left_lex. rewrite H4; auto. 
  + destruct a, b, c; simpl in *; subst.
    apply right_lex; simpl. eapply lt_trans; eauto.
Qed.

Require Import Omega.

Lemma stackSize_cons :
  forall (t1 t2 : Tm) (s : Stack),
    stackSize s < stackSize ((t1, t2) :: s).
Proof.
  intros. pose (size_gt0 t1); pose (size_gt0 t2). cbn. omega.
Qed.

Require Import Recdef.

Program Fixpoint robinsonUnif (stack: Stack) (mgu:VarMap) {wf stacklt stack}
   : option VarMap :=
match stack with
| nil => Some mgu
| (t0, t1) :: stack => 
  if Tm_eq_dec t0 t1 then
    robinsonUnif stack mgu
  else
    let handleVar x t :=
      if hasVar x t then
        None
      else
        let sb := (x,t) in 
        let stack := applySubstToStack sb stack in
        let mgu := applySubstToVarMap sb mgu in 
        let mgu := cons sb mgu in 
        robinsonUnif stack mgu
    in
    match t0, t1 with
    | Var x, _ => handleVar x t1
    | _, Var x => handleVar x t0
    | App f0 xs0, App f1 xs1 => 
      if Nat.eq_dec f0 f1 then
        match zip xs0 xs1 stack with
        | Some stack => 
          robinsonUnif stack mgu
        | None =>
          None
        end
      else
        None
    end
end.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.
unfold MR.
apply wf_inverse_image.
apply stacklt_wf.
Defined.

Require Import List.
Import ListNotations.

Ltac inv H := inversion H; subst; clear H; try contradiction; auto.

Lemma hasnt :
  ~ HasVar 0 (App 0 [Var 1; Var 2; Var 3]).
Proof.
  intro. repeat
  match goal with
      | H : _ |- _ => inv H
  end.
Qed.

Theorem the_universe_explodes : False.
Proof.
  pose robinsonUnif_func_obligation_2 as H.
  specialize (H
    [(Var 4, Var 5); (Var 0, Var 0)] [] (fun _ _ _ => None) (Var 4) (Var 5)
    [(Var 0, Var 0)] eq_refl ltac:(inversion 1) 0 (App 0 [Var 1; Var 2; Var 3])
    hasnt).
  compute in H. inv H.
    omega.
    omega.
Qed.

Print Assumptions the_universe_explodes.

End RobinsonUnificationWf.