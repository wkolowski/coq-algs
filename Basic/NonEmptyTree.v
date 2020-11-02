Inductive Tree (A : Type) : Type :=
    | T : A -> Forest A -> Tree A

with Forest (A : Type) : Type :=
    | E : Forest A
    | F : Tree A -> Forest A -> Forest A.

Arguments T {A} _ _.
Arguments E {A}.
Arguments F {A} _ _ .

Require Import Arith.
Require Import FunInd.

Function auxT {A : Type} (t : Tree A) (k : nat) (acc : nat)
  : Tree (option nat) * nat :=
match t with
    | T _ f =>
        let
          '(f', acc') := auxF f k acc
        in
          if leb acc' k
          then (T (Some acc') f', S acc')
          else (T None f', acc')
end
with auxF {A : Type} (f : Forest A) (k : nat) (acc : nat)
  : Forest (option nat) * nat :=
match f with
    | E => (E, acc)
    | F t f' =>
        let
          '(t', acc') := auxT t k acc
        in let
          '(f'', acc'') := auxF f' k acc
        in
          (F t' f'', max acc' acc'')
end.

(** An algorithm that colors a tree so that at most k nodes in each
    path are colored. *)
Definition color {A : Type} (k : nat) (t : Tree A) : Tree (option nat) :=
  fst (auxT t k 1).

Require Import Lia.

Definition wut :=
  T 1 (F (T 2 (F (T 5 E) E)) (F (T 3 E) (F (T 4 E) E))).

Lemma specT :
  forall (A : Type) (t : Tree A) (t' : Tree (option nat)) (k acc acc' : nat),
    acc <= k -> auxT t k acc = (t', acc') -> acc' <= S k

with specF :
  forall (A : Type) (f : Forest A) (f' : Forest (option nat))
  (k acc acc' : nat),
    acc <= k -> auxF f k acc = (f', acc') -> acc' <= S k.
Proof.
  destruct t; simpl; intros. case_eq (auxF f k acc); intros.
  case_eq (n <=? k); intro; rewrite H1, H2 in H0;
  inversion H0; subst; clear H0.
    apply leb_complete in H2. apply le_n_S. assumption.
    apply (specF A _ _ _ _ _ H H1).
  destruct f; simpl; intros; inversion H0; subst; clear H0.
    apply le_S. assumption.
    case_eq (auxT t k acc); intros; case_eq (auxF f k acc); intros.
      rewrite H0, H1 in H2. inversion H2; subst; clear H2.
        apply Max.max_lub; [eapply specT | eapply specF]; eauto.
Qed.

Inductive elem {A : Type} (x : A) : Tree A -> Prop :=
    | elem0 :
        forall (y : A) (f : Forest A),
          x = y \/ elemF x f -> elem x (T y f)

with elemF {A : Type} (x : A) : Forest A -> Prop :=
    | elemF0 :
        forall (t : Tree A) (f : Forest A),
          elem x t \/ elemF x f -> elemF x (F t f).

Ltac inv H := inversion H; subst; clear H.

Lemma auxT_spec2 :
  forall (A : Type) (x : option nat) (t : Tree A) (t' : Tree (option nat))
  (k acc acc' : nat),
    acc <= k -> auxT t k acc = (t', acc') -> elem x t' ->
      x = None \/ exists k' : nat, x = Some k' /\ k' <= k

with auxF_spec2 :
  forall (A : Type) (x : option nat) (f : Forest A) (f' : Forest (option nat))
  (k acc acc' : nat),
    acc <= k -> auxF f k acc = (f', acc') -> elemF x f' ->
      x = None \/ exists k' : nat, x = Some k' /\ k' <= k.
Proof.
  destruct t; simpl; intros.
  case_eq (auxF f k acc); intros. rewrite H2 in *.
  case_eq (n <=? k); intros; rewrite H3 in *; inv H0.
    inv H1. destruct H4.
      right. exists n. split; auto. apply leb_complete. assumption.
      eapply auxF_spec2; eauto.
    inv H1. destruct H4.
      left. assumption.
      eapply auxF_spec2; eauto.
  destruct f; simpl; intros; inv H0.
    inv H1.
    case_eq (auxT t k acc); intros; rewrite H0 in *.
    case_eq (auxF f k acc); intros; rewrite H2 in *.
      inv H3. inv H1. destruct H4.
        eapply auxT_spec2; eauto.
        eapply auxF_spec2; eauto.
Qed.