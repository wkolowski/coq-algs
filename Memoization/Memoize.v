Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Set Implicit Arguments.

Fixpoint fib (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') => fib n' + fib n''
end.

Lemma fib_SS :
  forall n : nat, fib (S (S n)) = fib n + fib (S n).
Proof.
  intros. cbn. omega.
Qed.

Fixpoint fromTo (a b : nat) : list nat :=
  if b <? a then [] else
match b with
    | 0 => [0]
    | S b' => fromTo a b' ++ [b]
end.

Definition test := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Time Compute map fib (fromTo 0 24).

Time Compute fib 24.

Fixpoint find {A : Type} (n : nat) (l : list (nat * A)) : option A :=
match l with
    | [] => None
    | (m, v) :: t => if n =? m then Some v else find n t
end.

Axiom wut : False.

Instance KVP (A : LinDec) (B : Type) : LinDec :=
{
    carrier := A * B;
    leq p1 p2 := fst p1 ≤ fst p2;
    leqb p1 p2 := fst p1 <=? fst p2;
}.
Proof.
  all: intros; repeat
  match goal with
      | p : _ * _ |- _ => destruct p
  end; cbn in *; dec.
  cut False.
    inversion 1.
    apply wut.
Defined.

Function aux (n : nat) (acc : list (nat * nat)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        match find n'' acc with
            | None =>
                let a := aux n'' acc in
                let b := aux n' ((n'', a) :: acc) in a + b
            | Some a =>
                match find n' acc with
                    | None =>
                        let b := aux n' acc in a + b
                    | Some b => a + b
                end
        end
end.

Definition fibM n := aux n [(0, 0); (1, 1)].

Compute map fibM test.
Time Compute fibM 24.

(*Lemma aux_spec :
  forall n : nat, fibM n = fib n.
Proof.
  intros. unfold fibM. remember [(0, 0); (1, 1)] as acc.
  functional induction aux n acc; cbn; trivial.
    destruct n'' as [| [| n'']]; cbn.
*)

Let list_map := map.

Require Import BTree.
Require Import BST.
Require Import TrichDec.

Fixpoint find' {A : TrichDec} {B : Type} (k : A) (t : BTree (KVP A B))
  : option B :=
match t with
    | empty => None
    | node p l r =>
        match k <?> fst p with
            | Lt => find' k l
            | Eq => Some (snd p)
            | Gt => find' k r
        end
end.
Search BTree_ins.

(*Lemma find'_spec_eq :
  forall (A : TrichDec) (B : Type) (k k' : A) (v : B) (acc : BTree (KVP A B)),
    find' k (@BTree_ins (KVP A B) (k', v) acc) =
      if k =? k' then Some v else find' k acc.
Proof.
  induction acc; cbn.
    trich.
    destruct a. cbn in *. destruct (LinDec_eqb_spec A k k'); subst.
      case_eq (k' <?> c); intros; cbn; rewrite H.
        assumption.
        rewrite *)

Definition FibAcc := KVP natlt natlt.

Function aux' (n : nat) (acc : BTree (FibAcc)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        match find' n'' acc with
            | None =>
                let a := aux' n'' acc in
                let b := aux' n' (@BTree_ins (FibAcc) (n'', a) acc) in a + b
            | Some a =>
                match find' n' acc with
                    | None =>
                        let b := aux' n' acc in a + b
                    | Some b => a + b
                end
        end
end.

Definition fibM' n :=
  aux' n (@fromList (FibAcc) [(0, 0); (1, 1)]).

Time Compute list_map fibM' (fromTo 0 24).

Definition acc_correct (acc : BTree (FibAcc)) : Prop :=
  forall n : nat, find' n acc = Some (fib n) \/ find' n acc = None.

Definition acc_correct' (acc : BTree (FibAcc)) : Prop :=
  forall k v : nat, elem (k, v) acc -> exists n : nat, v = fib n.

Definition acc_correct'' (acc : BTree (FibAcc)) : Prop :=
  forall k v : nat, elem (k, v) acc -> v = fib k.

Lemma find'_reflect :
  forall (A : TrichDec) (B : Type) (k : A) (v : B) (t : BTree (KVP A B)),
    find' k t = Some v <-> elem (k, v) t.
Proof.
Admitted.

Ltac fib :=
repeat match goal with
    | p : ?P, H : ?P -> _ |- _ => destruct (H p); clear H
    | H : aux' _ _ = fib _ |- _ => rewrite H in *; clear H
    | H : find' _ _ = Some _ |- _ => rewrite find'_reflect in H
    | H : acc_correct'' _ |- _ => red in H
end;
  try (split; try red; intros);
repeat multimatch goal with
    | H : elem _ _ |- _ =>
        destruct (@elem_ins (FibAcc) _ _ _ H); clear H
    | H : (?k, ?v) = _ |- _ = fib _ => inv H; cbn; omega
    | H : forall k v : nat, elem _ ?acc -> _, H' : elem _ ?acc |- _ =>
        rewrite ?(H _ _ H') in *
end; cbn; auto; try omega.

Theorem aux'_correct :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct'' acc ->
      acc_correct'' (@BTree_ins FibAcc (n, aux' n acc) acc) /\
      aux' n acc = fib n.
Proof.
  intros n acc.
  functional induction aux' n acc; intros.
    cbn. split; trivial. red; intros.
      destruct (@elem_ins (FibAcc) _ _ _ H0).
        inv H1.
        red in H. apply H. assumption.
    cbn. split; trivial. red; intros.
      destruct (@elem_ins (FibAcc) _ _ _ H0).
        inv H1.
        red in H. apply H. assumption.
    destruct (IHn0 H). rewrite H1. edestruct IHn1.
      red. intros. destruct (@elem_ins (FibAcc) _ _ _ H2); inv H3.
      rewrite H1 in *. rewrite H3 in *. split.
        red. intros. destruct (@elem_ins (FibAcc) _ _ _ H4).
          inv H5. rewrite fib_SS. cbn. omega.
          apply H. assumption.
        rewrite fib_SS. omega.
    destruct (IHn0 H). rewrite H1. apply find'_reflect in e0.
    red in H. rewrite (H _ _ e0). split.
      red. intros. destruct (@elem_ins (FibAcc) _ _ _ H2).
        inv H3; cbn; omega.
        apply H. assumption.
      rewrite fib_SS; omega.
    apply find'_reflect in e0. apply find'_reflect in e1.
    red in H. rewrite (H _ _ e0), (H _ _ e1). split.
      red. intros. destruct (@elem_ins (FibAcc) _ _ _ H0).
        inv H1; cbn; omega.
        apply H. assumption.
      cbn; omega.
Restart.
  intros n acc.
  functional induction aux' n acc; intros; fib.
Qed.

Theorem fibM'_correct :
  forall n : nat, fibM' n = fib n.
Proof.
  intros. unfold fibM'. apply aux'_correct.
  red. intros. inv H; inv H1; inv H0.
Qed.

Theorem aux'_correct' :
  forall (n : nat) (acc : BTree (FibAcc)),
    acc_correct'' acc -> aux' n acc = fib n

with acc_correct''_ins :
  forall (n : nat) (acc : BTree (FibAcc)),
    acc_correct'' acc ->
      acc_correct'' (@BTree_ins (FibAcc) (n, aux' n acc) acc).
Proof.
  intros. clear aux'_correct'. functional induction aux' n acc.
    cbn; trivial.
    fib.
    erewrite IHn1, IHn0; eauto; cbn; omega.
    rewrite IHn0; auto. apply find'_reflect in e0. rewrite (H _ _ e0).
      cbn; omega.
    apply find'_reflect in e0; apply find'_reflect in e1.
      rewrite (H _ _ e0), (H _ _ e1). cbn; omega.
  intros. clear acc_correct''_ins. red. intros.
    destruct (@elem_ins FibAcc _ _ _ H0).
      inv H1.
      apply H. assumption.
Restart.
  intros. destruct n as [| [| n']].
    cbn. trivial.
    cbn. trivial.
    cbn. case_eq (@find' natlt nat n' acc); intros.
      assert (H0' := H0). apply find'_reflect in H0. apply H in H0.
      case_eq (@find' natlt nat (S n') acc); intros.
        apply find'_reflect in H1. apply H in H1.
          subst; cbn; omega.
        subst. destruct n'.
          cbn. trivial. case_eq (@find' natlt nat n' acc); intros.
            apply find'_reflect in H0. apply H in H0. subst. cbn. omega.
            rewrite ?aux'_correct' in *.
              cbn; omega.
              erewrite <- aux'_correct'; eauto.
              assumption.
      destruct n'.
        cbn. trivial.
        repeat match goal with
            | |- context [match ?x with _ => _ end] => case_eq x; intros
        end.
          rewrite ?aux'_correct'.
            fib. inv H2. omega.
            inv H3.
Abort.

Definition bind {A : TrichDec} {B : Type} (a : A)
  (f : A -> BTree (KVP A B) -> B) (acc : BTree (KVP A B))
  : B * BTree (KVP A B) :=
match find' a acc with
    | None => let b := f a acc in (b, @BTree_ins (KVP A B) (a, b) acc)
    | Some b => (b, acc)
end.

Function aux2 (n : nat) (acc : BTree (FibAcc)) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        let '(a, acc') := bind n'' aux2 acc in
        let '(b, acc'') := bind n' aux2 acc' in a + b
end.

Definition fibM2 n := aux2 n (@fromList (FibAcc) [(0, 0); (1, 1)]).

Time Compute list_map fib (fromTo 0 24).
Time Compute list_map fibM2 (fromTo 0 24).

Lemma bind_correct :
  forall (k : nat) (acc : BTree FibAcc),
    acc_correct'' acc -> fst (bind k aux2 acc) = fib k.
Proof.
  intros. unfold bind. case_eq (find' k acc); intros; cbn.
    apply find'_reflect in H0. red in H. rewrite (H _ _ H0). trivial.
    red in H.
Abort.

Theorem aux2_correct :
  forall (n : nat) (acc : BTree (FibAcc)),
    acc_correct'' acc ->
      acc_correct'' (@BTree_ins (FibAcc) (n, aux' n acc) acc) /\
      aux2 n acc = fib n.
Proof.
  intros n acc. functional induction aux2 n acc; intros.
    fib.
    fib.
Abort.


Fixpoint wutzor (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n4 as n3) as n2) as n1) =>
        wutzor n4 + wutzor n3 + wutzor n2 + wutzor n1
end.

Fixpoint wutzor' (n : nat) (acc : BTree (FibAcc)) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n4 as n3) as n2) as n1) =>
        let (x1, acc1) := bind n4 wutzor' acc in
        let (x2, acc2) := bind n3 wutzor' acc1 in
        let (x3, acc3) := bind n2 wutzor' acc2 in
        let (x4, acc4) := bind n1 wutzor' acc3 in x1 + x2 + x3 + x4
end.


Time Compute wutzor 30.
Time Compute
  wutzor' 30
    (@fromList (FibAcc) [(0, 0); (1, 0); (2, 0); (3, 0)]).