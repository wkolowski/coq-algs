(* Mergesort *)

(*Require Import List.
Import ListNotations.*)


Fixpoint merge' {A : LinDec} (n : nat) (l1 l2 : list A) : option (list A) :=
match n, l1, l2 with
    | 0, _, _ => None
    | _, nil, _ => Some l2
    | _, _, nil => Some l1
    | S n', h :: t, h' :: t' =>
        if leq_dec h h'
        then match merge' n' t l2 with
            | None => None
            | Some m => Some (h :: m)
        end
        else match merge' n' l1 t' with
            | None => None
            | Some m => Some (h' :: m)
        end
end.

Theorem merge_sorted' : forall (A : LinDec) (n : nat) (l1 l2 l : list A),
    sorted A l1 -> sorted A l2 -> merge' n l1 l2 = Some l ->
    sorted A l.
Proof.
  induction 1; intros.
    destruct n; inversion H0; subst; auto.
    destruct n, l2; inversion H0; subst. constructor.
      case_eq (leq_dec x c); intros eq' eq; rewrite eq in *.
        destruct n; inversion H2; constructor; auto.
        destruct n, l2; inversion H2. constructor. auto.
  

  induction n as [| n']; intros.
    inversion H1.
    induction H.
      inversion H1; subst. assumption.
      apply (IHn' [x] l2). constructor. auto. rewrite <- H1. destruct n'.
        simpl in *. destruct l2. inversion H1.
  induction 1. Print merge_func.
Abort.

Program Fixpoint merge (A : LinDec) (l1 l2 : list A)
    {measure (length l1 + length l2)} : list A :=
match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | h :: t, h' :: t' => if leq_dec h h'
        then h :: (merge A t (h' :: t'))
        else h' :: (merge A (h :: t) t')
end.
Next Obligation. simpl; omega. Defined.

Eval compute in merge natle [1; 2; 3] [4; 5; 6].

(*Eval compute in merge natle (5 :: _) (6 :: _).*)

(*Theorem merge_eq : forall (A : LinDec) (l1 l2 : list A),
    merge A l1 l2 = match l1, l2 with
        | nil, _ => l2
        | _, nil => l1
        | h :: t, h' :: t' => if leq_dec h h'
        then h :: (merge A t (h' :: t'))
        else h' :: (merge A (h :: t) t')
    end.
Proof.
  induction l1 as [| h t].
    destruct l2; compute; trivial.
    (*intro l2. generalize dependent t. generalize dependent h.*)
    induction l2 as [| h' t']; intros.
      compute. trivial.
      destruct (leq_dec h h').
        rewrite IHt. destruct t. compute. simpl. compute. simpl.*)

(*Definition merge' : forall (A : LinDec) (l : list A * list A), list A.
Proof. intro.
  apply Fix with (fun l l' => length (fst l) + length (snd l) <
    length (fst l') + length (snd l')).
    red. intro. constructor. intros.
      destruct a as [a1 a2], y as [y1 y2].
      simpl in H. induction a1, a2, y1, y2; simpl in *;
      try (inversion H; fail).
        constructor. inversion 1.
        constructor. simpl.
      
  Focus 2. exact (@nil A).
  intros.
  destruct l1 as [| h t].
    exact l2.
    destruct l2 as [| h' t'].
      exact (h :: t).
      destruct (leq_dec h h').
        refine (X *)

Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => []
    | _, [] => []
    | S n', h :: t => h :: take n' t
end.

Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
match n, l with
    | 0, _ => l
    | _, [] => []
    | S n', h :: t => drop n' t
end.

Theorem take_length : forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= length l.
Proof.
  induction n as [| n']; destruct l; simpl; intros; auto; omega.
Qed.

Theorem take_length2 : forall (A : Type) (n : nat) (l : list A),
    n < length l -> length (take n l) < length l.
Proof.
  induction n as [| n']; simpl; intros; auto.
  destruct l; simpl in *.
    inversion H.
    apply lt_n_S. apply IHn'. omega.
Qed.

Theorem drop_length : forall (A : Type) (l : list A) (n : nat),
    length (drop n l) <= length l.
Proof.
  induction l as [| h t]; destruct n; simpl; intros; auto.
Qed.

Theorem drop_length2 : forall (A : Type) (l : list A) (n : nat),
    0 < n -> l <> [] -> length (drop n l) < length l.
Proof.
  induction l as [| h t]; intros; destruct n; try (inversion H; fail);
  simpl in *.
    contradiction H0. trivial.
    unfold lt. apply le_n_S. apply drop_length.
Qed.

Program Fixpoint mergeSort (A : LinDec) (l : list A) 
    {measure (length l)} : list A :=
match l with
    | [] => []
    | [x] => [x]
    | l' =>
      let n := div2 (length l') in
      let l1 := take n l' in
      let l2 := drop n l' in
      merge A (mergeSort A l1) (mergeSort A l2)
end.
Next Obligation.
  apply take_length2. apply lt_div2. destruct l; simpl;
  try (contradiction H0; auto; fail); try omega. Qed.
Next Obligation.
  apply drop_length2; auto.
    destruct l; simpl. contradiction H0; auto.
      destruct l; simpl. contradiction (H c); auto. omega. Qed.
Next Obligation.
  split; repeat intro; inversion H.
Defined.

Fixpoint aux (A : LinDec) (l : list (list A)) : list (list A) :=
match l with
    | [] => []
    | [l'] => [l']
    | l1 :: l2 :: t => merge A l1 l2 :: aux A t
end.

Eval compute in merge natle (qs natle [5; 2; 8]) (qs natle [6; 4; 9]).
Eval compute in aux natle [[5; 2; 8]; [1; 4; 9]].
