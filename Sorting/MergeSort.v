Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Coq.Program.Wf.
Require Export Recdef.
Require Export Div2.

Require Export Sort.
Require Export ListLemmas.

Set Implicit Arguments.

Fixpoint merge (A : LinDec) (l1 : list A) {struct l1} : list A -> list A :=
    fix f (l2 : list A) {struct l2} : list A :=
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if h1 <=? h2
            then h1 :: merge A t1 l2
            else h2 :: f t2
    end.

(* Mergesort using Program Fixpoint. *)
Program Fixpoint msPF (A : LinDec) (l : list A) 
    {measure (length l)} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
      let n := div2 (length l') in
      let l1 := take n l' in
      let l2 := drop n l' in
      merge A (msPF A l1) (msPF A l2)
end.
Next Obligation.
  apply take_length_lt. apply lt_div2. destruct l; simpl;
  try (contradiction H0; auto; fail); try omega. Qed.
Next Obligation.
  apply drop_length_lt; auto.
    destruct l; simpl. contradiction H0; auto.
      destruct l; simpl. contradiction (H c); auto. omega. Qed.
Next Obligation.
  split; repeat intro; inversion H3.
Defined.

Eval compute in msPF natle testl.

(* Mergesort using Function. *)
Function msFun (A : LinDec) (l : list A) {measure length l} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
      let n := div2 (length l') in
      let l1 := take n l' in
      let l2 := drop n l' in
      merge A (msFun A l1) (msFun A l2)
end.
Proof.
  intros. apply drop_length_lt; simpl. omega. inversion 1.
  intros. apply take_length_lt. apply lt_div2. simpl. omega.
Defined.

Eval compute in msFun natle testl.

(* Mergesort using fuel recursion. *)
Fixpoint msFuel' (A : LinDec) (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | _, [x] => [x]
    | S n', l' =>
        let n := div2 (length l') in
        let l1 := take n l' in
        let l2 := drop n l' in
        merge A (msFuel' A n' l1) (msFuel' A n' l2)
end.

Eval compute in msFuel' natle 5 testl.

(* Mergesort using well-founded recursion and refine. *)
Definition msWfRef (A : LinDec) : list A -> list A.
refine (Fix (@lengthOrder_wf A) _
(fun (l : list A) =>
match l with
    | [] => fun _ => []
    | [x] => fun _ => [x]
    | x :: y :: l' => fun msWf =>
        let n := div2 (length (x :: y :: l')) in
        let l1 := take n (x :: y :: l') in
        let l2 := drop n (x :: y :: l') in merge A (msWf l1 _) (msWf l2 _)
end)).
Proof.
  all: unfold l1, l2, n.
    apply take_length_lt. apply lt_div2. simpl. omega.
    apply drop_length_lt; simpl.
      omega.
      inversion 1.
Defined.

(* Mergesort using Bove-Capretta *)
Inductive msDom {A : LinDec} : list A -> Type :=
    | msDom0 : msDom []
    | msDom1 : forall x : A, msDom [x]
    | msDom2 : forall l : list A,
        msDom (take (div2 (length l)) l) ->
        msDom (drop (div2 (length l)) l) -> msDom l.

Fixpoint msBC' {A : LinDec} {l : list A} (dom : msDom l) : list A :=
match dom with
    | msDom0 => []
    | msDom1 x => [x]
    | msDom2 l dom1 dom2 =>
        let l1 := msBC' dom1 in
        let l2 := msBC' dom2 in merge A l1 l2
end.

Theorem msDom_all : forall (A : LinDec) (l : list A), msDom l.
Proof.
  intro. apply well_founded_induction_type with lengthOrder.
    apply lengthOrder_wf.
    intros l ms. destruct l as [| h [| h' t]]; constructor.
      apply ms. apply take_length_lt. apply lt_div2. simpl. omega.
      apply ms. apply drop_length_lt. simpl. omega. inversion 1.
Defined.

Definition msBC (A : LinDec) (l : list A) : list A :=
    msBC' (msDom_all A l).

Eval compute in msBC natle testl.