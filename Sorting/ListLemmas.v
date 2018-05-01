Add Rec LoadPath "/home/zeimer/Code/Coq".

(*Require Import Sorting.Sort.*)
Require Export RCCBase.
Require Export LinDec.

Require Import Div2.

Set Implicit Arguments.

(* General lemmas *)
Definition lengthOrder {A : Type} (l1 l2 : list A) : Prop :=
  length l1 < length l2.

Theorem lengthOrder_wf :
  forall A : Type, well_founded (@lengthOrder A).
Proof.
  unfold lengthOrder. intro.
  apply (@well_founded_lt_compat _ (@length A)). trivial.
Defined.

Definition lenSum {A : Type} (l : list A * list A) : nat :=
  length (fst l) + length (snd l).

Definition lenSumOrd {A : Type} (l1 l2 : list A * list A) : Prop :=
  lenSum l1 < lenSum l2.

Lemma lenSumOrd_wf : forall (A : Type), well_founded (@lenSumOrd A).
Proof.
  intro. apply well_founded_lt_compat with lenSum.
  unfold lenSumOrd. auto.
Qed.

(* Selection sort lemmas *)
Fixpoint removeFirst {A : LinDec} (x : A) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if x =? h then t else h :: removeFirst x t
end.

Lemma removeFirst_In_eq : forall (A : LinDec) (x : A) (l : list A),
    In x l -> S (length (removeFirst x l)) = length l.
Proof.
  induction l as [| h t]; destruct 1; dec.
Defined.

Lemma removeFirst_le : forall (A : LinDec) (x : A) (l : list A),
    length (removeFirst x l) <= length l.
Proof.
  induction l as [| h t]; dec.
Defined.

Lemma removeFirst_In_lt : forall (A : LinDec) (x : A) (l : list A),
    In x l -> length (removeFirst x l) < length l.
Proof.
  induction l as [| h t]; destruct 1; dec.
    apply lt_n_S. auto.
Defined.

Lemma removeFirst_min_lengthOrder :
  forall (A : LinDec) (h : A) (t : list A),
    lengthOrder (removeFirst (min_dflt A h t) (h :: t)) (h :: t).
Proof.
  red; intros. apply removeFirst_In_lt. apply min_In.
Defined.

Lemma removeFirst_cons:
  forall (A : LinDec) (h : A) (t : list A), min_dflt A h t <> h ->
    lengthOrder (h :: removeFirst (min_dflt A h t) t) (h :: t).
Proof.
  intros. replace (h :: removeFirst (min_dflt A h t) t) with
    (removeFirst (min_dflt A h t) (h :: t)).
    apply removeFirst_min_lengthOrder.
    simpl. dec.
Qed.

Lemma min_split :
  forall (A : LinDec) (h : A) (t : list A),
    exists l1 l2 : list A, h :: t = l1 ++ min_dflt A h t :: l2 /\
      l1 ++ l2 = removeFirst (min_dflt A h t) (h :: t).
Proof.
  induction t as [| h' t']; intros.
    exists [], []. cbn. dec.
    simpl. dec; subst; cbn. eauto.
      exists [h], t'. dec.
      exists [], (h' :: t'). rewrite e. dec.
      exists [h], t'. dec.
      exists [h], t'. dec.
      destruct IHt' as [l1 [l2 [H H']]]. destruct l1.
        inversion H. dec.
        exists (h :: h' :: l1), l2. split.
          inversion H. dec.
          cbn in H'. dec.
Qed.

Lemma removeFirst_In_conv :
  forall (A : LinDec) (x h : A) (t : list A),
    In x (removeFirst (min_dflt A h t) (h :: t)) ->
      In x (h :: t).
Proof.
  induction t as [| h' t'].
    simpl. dec.
    simpl in *. dec; inversion H; subst; auto.
      inversion H; inversion H0; subst; auto.
        edestruct IHt'; simpl; auto.
Qed.

Lemma removeFirst_In :
  forall (A : LinDec) (x h : A) (t : list A),
    In x t -> min_dflt A h t <> x -> In x (removeFirst (min_dflt A h t) t).
Proof.
  induction t as [| h' t']; inversion 1; subst; intros.
    simpl in *. dec.
    simpl. dec. right. apply IHt'.
      assumption.
      simpl in *. destruct (leqb_spec h' (min_dflt A h t')).
        contradiction.
        assumption.
Qed.

(* Quicksort lemmas *)
Lemma filter_length :
  forall (A : Type) (f : A -> bool) (l : list A),
    length (filter f l) <= length l.
Proof.
  induction l as [| h t]; simpl; try destruct (f h); simpl; omega.
Qed.

Lemma filter_lengthOrder :
  forall {A : Type} (p : A -> bool) (h : A) (t : list A),
    lengthOrder (filter p t) (h :: t).
Proof.
  intros. unfold lengthOrder, lt. simpl. apply le_n_S.
  apply filter_length.
Qed.

Lemma filter_In_app :
  forall (A : LinDec) (p : A -> bool) (x : A) (l : list A),
    In x (filter p l ++ filter (fun x => negb (p x)) l) -> In x l.
Proof.
  induction l as [| h t]; simpl.
    auto.
    destruct (p h); simpl.
      destruct 1; auto.
      intro. apply in_app_or in H. destruct H.
        right. apply IHt. apply in_or_app. auto.
        inversion H.
          subst. auto.
          right. apply IHt. apply in_or_app. auto.
Qed.

Function bifilter {A : Type} (p : A -> bool) (l : list A)
    : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t =>
        let (l1, l2) := bifilter p t in
        if p h then (h :: l1, l2) else (l1, h :: l2)
end.

Theorem bifilter_spec :
  forall (A : Type) (p : A -> bool) (l : list A),
    bifilter p l = (filter p l, filter (fun x : A => negb (p x)) l).
Proof.
  intros. functional induction @bifilter A p l; simpl;
  rewrite ?e1; simpl; try rewrite e0 in IHp0; try inversion IHp0; auto.
Qed.

Require Import TrichDec.

Function trifilter {A : TrichDec} (x : A) (l : list A)
  : list A * list A * list A :=
match l with
    | [] => ([], [], [])
    | h :: t =>
        let '(l1, l2, l3) := trifilter x t in
        match h <?> x with
            | Lt => (h :: l1, l2, l3)
            | Eq => (l1, h :: l2, l3)
            | Gt => (l1, l2, h :: l3)
        end
end.

Theorem trifilter_spec :
  forall (A : TrichDec) (pivot : A) (l : list A),
    trifilter pivot l =
      (filter (fun x : A => x <? pivot) l,
       filter (fun x : A => x =? pivot) l,
       filter (fun x : A => pivot <? x) l).
Proof.
  intros. functional induction @trifilter A pivot l; cbn;
  try (rewrite e0 in *; clear e0; inv IHp); trich.
Qed.

(* Mergesort lemmas *)
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

Theorem take_length_le : forall (A : Type) (n : nat) (l : list A),
    length (take n l) <= length l.
Proof.
  induction n as [| n']; destruct l; simpl; intros; auto.
    omega.
    apply le_n_S. apply IHn'.
Qed.

Theorem take_length_lt : forall (A : Type) (n : nat) (l : list A),
    n < length l -> length (take n l) < length l.
Proof.
  induction n as [| n']; simpl; intros; auto.
  destruct l; simpl in *.
    inversion H.
    apply lt_n_S. apply IHn'. omega.
Qed.

Theorem drop_length_le : forall (A : Type) (l : list A) (n : nat),
    length (drop n l) <= length l.
Proof.
  induction l as [| h t]; destruct n; simpl; intros; auto.
Qed.

Theorem drop_length_lt : forall (A : Type) (l : list A) (n : nat),
    0 < n -> l <> [] -> length (drop n l) < length l.
Proof.
  induction l as [| h t]; intros; destruct n; try (inversion H; fail);
  simpl in *.
    contradiction H0. trivial.
    unfold lt. apply le_n_S. apply drop_length_le.
Qed.

Lemma take_In :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    In x (take n l) -> In x l.
Proof.
  induction n as [| n'].
    simpl. inversion 1.
    destruct l as [| h t]; simpl; auto.
      destruct 1; auto.
Qed.

Lemma drop_In :
  forall (A : Type) (n : nat) (x : A) (l : list A),
    In x (drop n l) -> In x l.
Proof.
  induction n as [| n'].
    simpl. auto.
    destruct l as [| h t]; simpl; auto.
Qed.

Lemma take_In_tail :
  forall (A : Type) (n : nat) (x h : A) (t : list A),
    In x (take n t) -> In x (take (S n) (h :: t)).
Proof.
  induction n as [| n']; simpl.
    inversion 2.
    destruct t as [| h' t']; simpl; destruct 1; auto.
Qed.

Lemma drop_In_tail :
  forall (A : Type) (n : nat) (x h : A) (t : list A),
    In x (drop n t) -> In x (drop (S n) (h :: t)).
Proof.
  induction n as [| n']; simpl.
    auto.
    destruct t as [| h' t']; simpl; auto.
Qed.

Fixpoint list_ind2 (A : Type) (P : list A -> Prop)
  (Hnil : P []) (Hsingl : forall x : A, P [x])
  (Hcons : forall (x y : A) (l : list A), P l -> P (x :: y :: l))
    (l : list A) : P l.
Proof.
  destruct l as [| h [| h' t]].
    apply Hnil.
    apply Hsingl.
    apply Hcons. apply list_ind2; auto.
Defined.

Lemma take_drop :
  forall (A : Type) (n : nat) (l : list A),
    take n l ++ drop n l = l.
Proof.
  induction n as [| n']; destruct l as [| h t]; simpl; try f_equal; auto.
Qed.

Function ms_split {A : Type} (l : list A) : list A * list A :=
match l with
    | [] => ([], [])
    | [x] => ([x], [])
    | x :: y :: l' =>
        let (l1, l2) := ms_split l' in (x :: l1, y :: l2)
end.

Lemma ms_split_len1 :
  forall (A : Type) (x y : A) (l l1 l2 : list A),
    ms_split (x :: y :: l) = (l1, l2) -> length l1 < length (x :: y :: l).
Proof.
  intros A x y l. functional induction @ms_split A l.
    inversion 1; simpl; omega.
    inversion 1; simpl; omega.
    simpl in *. destruct (ms_split l'). inversion 1; inversion e0; subst.
      specialize (IHp x0 y (x0 :: l1) (y :: l2) eq_refl). simpl in *.
        omega.
Qed.

Lemma ms_split_len2 :
  forall (A : Type) (x y : A) (l l1 l2 : list A),
    ms_split (x :: y :: l) = (l1, l2) -> length l2 < length (x :: y :: l).
Proof.
  intros A x y l. functional induction @ms_split A l.
    inversion 1; simpl; omega.
    inversion 1; simpl; omega.
    simpl in *. destruct (ms_split l'). inversion 1; inversion e0; subst.
      specialize (IHp x0 y (x0 :: l1) (y :: l2) eq_refl). simpl in *.
        omega.
Qed.

Functional Scheme div2_ind := Induction for div2 Sort Prop.

Lemma div2_pres_le :
  forall n m : nat, n <= m -> Nat.div2 n <= Nat.div2 m.
Proof.
  intro. functional induction div2 n; intros.
    omega.
    omega.
    destruct m as [| [| m']].
      omega.
      omega.
      simpl. apply le_n_S. apply IHn0. omega.
Qed.

(* Moved from Test.v *)
Fixpoint cycle {A : Type} (n : nat) (l : list A) : list A :=
match n with
    | 0 => []
    | S n' => l ++ cycle n' l
end.

(* Moved from TrichQuicksortSpec.v *)

Lemma filter_eqb_repeat :
  forall (A : LinDec) (x : A) (l : list A),
    exists n : nat, filter (fun x' : A => x' =? x) l = repeat x n.
Proof.
  induction l as [| h t]; cbn.
    exists 0. reflexivity.
    dec. destruct IHt as [n H]. exists (S n). cbn. rewrite H. reflexivity.
Qed.