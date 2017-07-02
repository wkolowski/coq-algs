Require Import Sort.

Fixpoint merge (A : LinDec) (l1 : list A) {struct l1} : list A -> list A :=
    fix f (l2 : list A) {struct l2} : list A :=
    match l1, l2 with
        | [], _ => l2
        | _, [] => l1
        | h1 :: t1, h2 :: t2 =>
            if @leq_total_dec A h1 h2
            then h1 :: merge A t1 l2
            else h2 :: f t2
    end.

(*Theorem merge_eq1 : forall (A : LinDec) (h1 h2 : A) (t1 t2 : list A),
  @leq A h1 h2 -> merge A (h1 :: t1) (h2 :: t2) = h1 :: merge A t1 (h2 :: t2).
Proof.
  intros. simpl. Check leq_total_dec. Print sumbool.*)


Eval compute in merge natle [1; 2; 3] [4; 5; 6].

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

Eval compute in merge' 10 [1; 2; 3] [4; 5; 6].

Hint Constructors sorted.

Theorem merge_sorted : forall (A : LinDec) (l1 l2 : list A),
    sorted A l1 -> sorted A l2 -> sorted A (merge A l1 l2).
Proof.
  intros A l1 l2 H. generalize dependent l2.
  induction H.
    destruct l2; auto.
    induction 1.
      simpl. auto.
      simpl. destruct (leq_total_dec x x0); auto.
      simpl in *. destruct (leq_total_dec x x0); auto.
        destruct (leq_total_dec x y); auto.
    induction 1.
      simpl. auto.
      specialize (IHsorted _ (sorted1 A x0)). simpl in *.
        destruct (leq_total_dec x x0); auto.
          destruct (leq_total_dec y x0); simpl; auto.
      simpl. destruct (leq_total_dec x x0).
        

assert (sorted A (y0 :: l0) -> sorted A (merge A (y :: l) (y0 :: l0))).
        intro. clear H3.
Abort. 
          
        
        

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
  
Abort. (*
  induction n as [| n']; intros.
    inversion H1.
    induction H.
      inversion H1; subst. assumption.
      apply (IHn' [x] l2). constructor. auto. rewrite <- H1. destruct n'.
        simpl in *. destruct l2. inversion H1.
  induction 1. Print merge_func.
Abort.*)

Program Fixpoint merge2 (A : LinDec) (l1 l2 : list A)
    {measure (length l1 + length l2)} : list A :=
match l1, l2 with
    | nil, _ => l2
    | _, nil => l1
    | h :: t, h' :: t' => if leq_dec h h'
        then h :: (merge2 A t l2)
        else h' :: (merge2 A l1 t')
end.
Next Obligation. simpl; omega. Defined.

Eval compute in merge2 natle [1; 2; 3] [4; 5; 6].

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
  induction n as [| n']; destruct l; simpl; intros; auto.
    omega.
    apply le_n_S. apply IHn'.
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

Require Import Arith.
Require Import Div2.

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

(*Eval compute in merge natle (qs natle [5; 2; 8]) (qs natle [6; 4; 9]).*)
Eval compute in aux natle [[5; 2; 8]; [1; 4; 9]].

(* Mergesort using Bove-Capretta *)

Inductive msDom' (A : LinDec) : list A -> Type :=
    | msDom_base : msDom' A []
    | msDom_base' : forall x : A, msDom' A [x]
    | msDom_rec : forall l : list A,
        msDom' A (take (div2 (length l)) l) ->
        msDom' A (drop (div2 (length l)) l) -> msDom' A l.

Fixpoint ms_aux (A : LinDec) (l : list A) (dom : msDom' A l) : list A :=
match dom with
    | msDom_base => []
    | msDom_base' x => [x]
    | msDom_rec l dom1 dom2 =>
        let l1 := ms_aux A _ dom1 in
        let l2 := ms_aux A _ dom2 in merge A l1 l2
end.

Theorem msDom_all : forall (A : LinDec) (l : list A), msDom' A l.
Proof.
  intro.
  apply well_founded_induction_type with (fun l1 l2 => length l1 < length l2).
    eapply well_founded_lt_compat. eauto.
    intros l ms. destruct l as [| h [| h' t]]; constructor.
      
      apply ms. apply take_length2. apply lt_div2. simpl. omega.
      apply ms. apply drop_length2. simpl. omega. inversion 1.
Defined.

Definition ms {A : LinDec} (l : list A) : list A :=
    ms_aux A l (msDom_all A l).

Eval compute in @ms natle testl.