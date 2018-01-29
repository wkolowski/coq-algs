Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export FunctionalExtensionality.

Require Export Bool.

Require Export List.
Export ListNotations.

Require Export Arith.
Require Export Omega.

Require Export Equality.
Require Export Eqdep.

Require Export Permutation.

Require Export Coq.Program.Wf.
Require Export Recdef.

Set Implicit Arguments.

Hint Constructors reflect.

(* General useful tactics. *)
(*Ltac inv H := inversion H; subst.*)
Ltac inv H := inversion H; subst; clear H; auto.

Ltac gen x := generalize dependent x.

Ltac ext x := extensionality x.

(* Tactics for easier induction. *)
Ltac term_contains t x :=
match t with
    | x => idtac
    | ?f x => idtac
    | ?f _ => term_contains f x
    | _ => fail
end.

Ltac gen_IH H :=
match reverse goal with
    | H : _ |- _ => fail
    | x : ?Tx |- _ =>
        match type of H with
            | ?TH => term_contains TH x
            | _ => generalize dependent x
        end
end.

Ltac gen_ind H :=
  try intros until H; gen_IH H; induction H; cbn; auto.


Ltac invs := repeat
match goal with
    | H : ?f ?x1 ?x2 ?x3 = ?f ?x1' ?x2' ?x3' |- _ => inv H
    | H : ?f ?x1 ?x2 = ?f ?x1' ?x2' |- _ => inv H
    | H : ?f ?x1 = ?f ?x1' |- _ => inv H
end.

Ltac replace_nonvars H :=
match H with
    | ?f ?x1 => is_var x1; replace_nonvars f
    | ?f ?x1 =>
        let x1' := fresh "x1" in
        let H1 := fresh "H1" in remember x1 as x1' eqn: H1; replace_nonvars f
    | _ => idtac
end.

Ltac clean_eqs := repeat
match goal with
    | H : ?x = ?x |- _ => clear H
    | H : ?x = ?x -> _ |- _ => specialize (H eq_refl)
    | H : forall x, ?y = ?y -> ?P |- _ =>
        assert (H' := fun x => H x eq_refl); clear H; rename H' into H
end.

Ltac ind' H :=
match type of H with
    | ?T => replace_nonvars T; induction H; subst; try congruence;
        invs; clean_eqs; eauto
end.

Ltac ind H := try intros until H; gen_IH H; ind' H.

(* Tactics for reification. *)
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

(* Environments. *)
Definition Env (X : Type) : Type := list X.

Definition holds (n : nat) (env : Env Prop) : Prop := nth n env False.

Definition Proofs : Type := list nat.

Fixpoint allTrue (env : Env Prop) (proofs : Proofs) : Prop :=
match proofs with
    | [] => True
    | h :: t => holds h env /\ allTrue env t
end.

Theorem find_spec :
  forall (n : nat) (env : Env Prop) (proofs : Proofs),
    allTrue env proofs -> In n proofs -> holds n env.
Proof.
  induction proofs as [| h t]; cbn.
    inversion 2.
    do 2 destruct 1; subst.
      unfold holds in H. apply H.
      apply IHt; assumption.
Qed.

(* A type for solving formulas. *)
Inductive solution (P : Prop) : Type :=
    | Yes' : P -> solution P
    | No' : solution P.

Arguments Yes' [P] _.
Arguments No' [P].

Notation "'Yes'" := (Yes' _).
Notation "'No'" := No'.

Notation "'Reduce' x" := (if x then Yes else No) (at level 50).
Notation "x &&& y" := (if x then Reduce y else No).
Notation "x ||| y" := (if x then Yes else Reduce y).

Definition unwrap {P : Prop} (s : solution P) :=
match s return if s then P else Prop with
    | Yes' p => p
    | _ => True
end.