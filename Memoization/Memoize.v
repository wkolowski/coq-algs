(*Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export RCCBase.

Require Import BTree.
Require Import BST.
Require Import TrichDec.

Set Implicit Arguments.

Lemma prod_eq :
  forall (A B : Type) (a a' : A) (b b' : B),
    (a, b) = (a', b') -> a = a' /\ b = b'.
Proof.
  intros. inv H.
Qed.

Fixpoint fromTo (a b : nat) : list nat :=
  if b <? a then [] else
match b with
    | 0 => [0]
    | S b' => fromTo a b' ++ [b]
end.

Axiom wut : False. (* TODO *)

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
    apply wut. (* TODO *)
Defined.

Function find {A : TrichDec} {B : Type} (k : A) (t : BTree (KVP A B))
  : option B :=
match t with
    | empty => None
    | node p l r =>
        match k <?> fst p with
            | Lt => find k l
            | Eq => Some (snd p)
            | Gt => find k r
        end
end.

Definition FibAcc := KVP natlt natlt.

Function fib (n : nat) : nat :=
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

Fixpoint fib_tr_aux (n a b : nat) : nat :=
match n with
    | 0 => a
    | S n' => fib_tr_aux n' b (a + b)
end.

Definition fib_tr (n : nat) := fib_tr_aux n 0 1.

Lemma fib_tr_aux_spec :
  forall n k : nat,
    fib_tr_aux (1 + k) (fib n) (fib (1 + n)) = fib (1 + k + n).
Proof.
  intros. generalize dependent n.
  induction k; intros.
    cbn. trivial.
    change (fib_tr_aux (S k) (fib (1 + n)) (fib n + fib (1 + n)) =
            fib (1 + S k + n)).
      replace (fib n + fib (1 + n)) with (fib (2 + n)).
        rewrite IHk. f_equal. omega.
        cbn. omega.
Qed.

Theorem fib_tr_is_fib : fib_tr = fib.
Proof.
  ext n. unfold fib_tr. destruct n.
    cbn. trivial.
    change 1 with (fib 1). change 0 with (fib 0).
      rewrite fib_tr_aux_spec. f_equal. cbn. omega.
Qed.

Let list_map := @map.

Function fibM_aux (n : nat) (acc : BTree FibAcc) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        match find n'' acc with
            | None =>
                let a := fibM_aux n'' acc in
                let b := fibM_aux n' (@BTree_ins FibAcc (n'', a) acc) in a + b
            | Some a =>
                match find n' acc with
                    | None =>
                        let b := fibM_aux n' acc in a + b
                    | Some b => a + b
                end
        end
end.

Definition fibM (n : nat) : nat :=
  fibM_aux n (@fromList FibAcc [(0, 0); (1, 1)]).

Definition acc_correct {A : TrichDec} {B : Type}
  (f : A -> B) (acc : BTree (KVP A B)) : Prop :=
    forall (k : A) (v : B), elem (k, v) acc -> v = f k.

Lemma find_elem :
  forall (A : TrichDec) (B : Type) (k : A) (v : B) (t : BTree (KVP A B)),
    find k t = Some v -> elem (k, v) t.
Proof.
  intros. revert v H.
  functional induction @find A B k t; intros; try congruence.
    eauto.
    destruct p; cbn in *. trich. inv H.
    eauto.
Qed.

Ltac fib := 
repeat match goal with
    | p : ?P, H : ?P -> _ |- _ => destruct (H p); clear H
    | H : _ = fib _ |- _ => rewrite H in *; clear H
    | H : find _ _ = Some _ |- _ => apply find_elem in H
    | H : acc_correct _ _ |- _ => red in H
end;
  try (split; try red; intros);
repeat multimatch goal with
    | H : elem _ _ |- _ =>
        destruct (@elem_ins FibAcc _ _ _ H); clear H
    | H : (?k, ?v) = _ |- _ = fib _ => inv H; cbn; omega
    | H : forall (k : _) (v : _), elem _ ?acc -> _, H' : elem _ ?acc |- _ =>
        rewrite ?(H _ _ H') in *
end; cbn; auto; try omega.

Theorem aux'_correct :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct fib acc ->
      acc_correct fib (@BTree_ins FibAcc (n, fibM_aux n acc) acc) /\
      fibM_aux n acc = fib n.
Proof.
  intros n acc.
  functional induction fibM_aux n acc; intros; fib.
Qed.

Theorem fibM_correct : fibM = fib.
Proof.
  ext n. unfold fibM. apply aux'_correct.
  red. intros. inv H; inv H1; inv H0.
Qed.

Theorem acc_correct_ins_fibM_aux :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct fib acc -> fibM_aux n acc = fib n ->
      acc_correct fib (@BTree_ins FibAcc (n, fibM_aux n acc) acc).
Proof.
  intros. red; intros.
  destruct (@elem_ins FibAcc _ _ _ H1); fib.
Qed.

Theorem fibM_aux_correct :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct fib acc -> fibM_aux n acc = fib n.
Proof.
  intros. functional induction fibM_aux n acc.
    fib.
    fib.
    erewrite IHn1, IHn0; eauto; cbn.
      omega.
      apply acc_correct_ins_fibM_aux; auto.
    apply find_elem in e0. rewrite (H _ _ e0).
      erewrite IHn0; eauto; cbn. omega.
    fib.
Qed.

Theorem fibM_correct' : fibM = fib.
Proof.
  ext n. unfold fibM. apply fibM_aux_correct.
  red. intros. inv H; inv H1; inv H0.
Qed.

Definition bind {A : TrichDec} {B : Type} (a : A)
  (f : A -> BTree (KVP A B) -> B) (acc : BTree (KVP A B))
  : B * BTree (KVP A B) :=
match find a acc with
    | None => let b := f a acc in (b, @BTree_ins (KVP A B) (a, b) acc)
    | Some b => (b, acc)
end.

Function fibM'_aux (n : nat) (acc : BTree FibAcc) : nat :=
match n with
    | 0 => 0
    | 1 => 1
    | S (S n'' as n') =>
        let '(a, acc') := bind n'' fibM'_aux acc in
        let '(b, acc'') := bind n' fibM'_aux acc' in a + b
end.

Definition fibM' n := fibM'_aux n (@fromList FibAcc [(0, 0); (1, 1)]).

Lemma bind_correct_fibM'_aux :
  forall (k : nat) (acc : BTree FibAcc),
    acc_correct fib acc -> fibM'_aux k acc = fib k ->
      fst (@bind natlt nat k fibM'_aux acc) = fib k.
Proof.
  intros. unfold bind. case_eq (@find natlt nat k acc); intros; cbn.
    apply find_elem in H1. red in H. rewrite (H _ _ H1). trivial.
    assumption.
Qed.

Theorem acc_correct_ins_fibM'_aux :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct fib acc -> fibM'_aux n acc = fib n ->
      acc_correct fib (@BTree_ins FibAcc (n, fibM'_aux n acc) acc).
Proof.
  intros. red; intros.
  destruct (@elem_ins FibAcc _ _ _ H1); fib.
Qed.

Theorem fibM'_aux_correct :
  forall (n : nat) (acc : BTree FibAcc),
    acc_correct fib acc -> fibM'_aux n acc = fib n.
Proof.
  intro. functional induction fib n; cbn; intros.
    trivial.
    trivial.
    destruct (@bind natlt nat n'' fibM'_aux acc) as [a acc'] eqn: H1;
    destruct (@bind natlt nat (S n'') fibM'_aux acc') as [b acc''] eqn: H2.
    unfold bind in *.
    case_eq (@find natlt nat n'' acc);
    case_eq (@find natlt nat (S n'') acc'); intros;
    rewrite H0, H3 in *;
    repeat match goal with
        | H : find _ _ = Some _ |- _ => apply find_elem in H
    end.
      inv H1; inv H2. rewrite (H _ _ H0), (H _ _ H3). cbn; omega.
      inv H1. destruct (prod_eq H2).
        rewrite (H _ _ H3), <- H1, IHn0. cbn; omega. assumption.
      destruct (prod_eq H1). inv H2. destruct (@elem_ins FibAcc _ _ _ H0).
        inv H2. omega.
        rewrite (H _ _ H2), IHn1. cbn; omega. assumption.
      destruct (prod_eq H1), (prod_eq H2); subst. rewrite IHn0, IHn1.
        cbn; omega.
        assumption.
        apply acc_correct_ins_fibM'_aux; auto.
Qed.

Fixpoint wutzor (n : nat) : nat :=
match n with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | S (S (S (S n4 as n3) as n2) as n1) =>
        wutzor n4 + wutzor n3 + wutzor n2 + wutzor n1
end.

Fixpoint wutzor' (n : nat) (acc : BTree FibAcc) : nat :=
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


Time Compute wutzor 29.
Time Compute
  wutzor' 29
    (@fromList FibAcc [(0, 0); (1, 0); (2, 0); (3, 0)]).
*)