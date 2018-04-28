Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.

Set Implicit Arguments.

Function min {A : LinDec} (l : list A) : option A :=
match l with
    | [] => None
    | h :: t =>
        match min t with
            | None => Some h
            | Some m =>
                Some (if h <=? m then h else m)
        end
end.

Function ss (A : LinDec) (l : list A) {measure length l} : list A :=
match min l with
    | None => []
    | Some m =>
        m :: ss A (removeFirst m l)
end.
Proof.
  intros. functional induction @min A l; inv teq; cbn; dec.
  apply lt_n_S. apply IHo. assumption.
Defined.

Lemma min_present :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m -> exists l1 l2 : list A,
      l = l1 ++ m :: l2.
Proof.
  intros. functional induction min l; inv H.
    exists [], t. cbn. reflexivity.
    exists [], t. cbn. reflexivity.
    destruct (IHo _ e0) as (l1 & l2 & Heq). subst.
      exists (h :: l1), l2. cbn. reflexivity.
Qed.

Lemma removeFirst_middle :
  forall (A : LinDec) (m : A) (l1 l2 : list A),
    perm A (l1 ++ l2) (removeFirst m (l1 ++ m :: l2)).
Proof.
  induction l1 as [| h t]; cbn; intros; dec.
Qed.

Theorem ss_perm :
  forall (A : LinDec) (l : list A), perm A l (ss A l).
Proof.
  intros. functional induction ss A l.
    destruct l; inv e. destruct (min l); inv H0.
    destruct (min_present _ _ e) as (l1 & l2 & Heq). subst.
      eapply perm_trans.
        apply perm_front.
        apply perm_cons. rewrite <- IHl0. apply removeFirst_middle.
Qed.

Lemma ss_In :
  forall (A : LinDec) (x : A) (l : list A),
    In x (ss A l) <-> In x l.
Proof.
  intros. rewrite !count_In. rewrite <- ss_perm. reflexivity.
Qed.

Lemma min_spec :
  forall (A : LinDec) (x m : A) (l : list A),
    In x l -> min l = Some m -> m ≤ x.
Proof.
  intros. functional induction min l; inv H0.
    inv H. destruct t.
      inv H0.
      cbn in e0. destruct (min t); inv e0.
    inv H. apply leq_trans with m0; dec.
    inv H. dec.
Qed.

Lemma removeFirst_min_In :
  forall (A : LinDec) (x m : A) (l : list A),
    In x l -> x <> m -> min l = Some m -> In x (removeFirst m l).
Proof.
  intros. functional induction min l; inv H1.
    inv H. destruct t.
      inv H1.
      cbn in e0. destruct (min t); inv e0.
    cbn. dec. inv H.
    cbn. inv H; dec.
Qed.

Lemma removeFirst_In :
  forall (A : LinDec) (x m : A) (l : list A),
    In x (removeFirst m l) -> In x l.
Proof.
  induction l as [| h t]; cbn; intros.
    assumption.
    dec. inv H.
Qed.

Theorem ss_sorted :
  forall (A : LinDec) (l : list A), sorted A (ss A l).
Proof.
  intros. functional induction ss A l.
    constructor.
    destruct (ss A (removeFirst m l)) eqn: Heq; constructor.
      apply min_spec with l.
        apply removeFirst_In with m. rewrite <- ss_In, Heq. left. auto.
        assumption.
      assumption.
Qed.

Instance Sort_ss (A : LinDec) : Sort A :=
{
    sort := @ss A;
    sort_sorted := ss_sorted A;
    sort_perm := ss_perm A
}.

(** Selection sort on steroids *)

Function mins {A : LinDec} (l : list A) : list A :=
match l with
    | [] => []
    | h :: t =>
        let l' := mins t in
        match l' with
            | [] => [h]
            | m :: ms =>
                if h =? m
                then h :: l'
                else if h <=? m
                then [h]
                else l'
        end
end.

(*Fixpoint removeAll
  {A : Type} (p : A -> bool) (l : list A) : list A :=
match l with
    | [] => []
    | h :: t => if p h then removeAll p t else h :: remove_all p t
end.

Lemma length_removeAll :
  forall (A : Type) (p : A -> bool) ( *)

Lemma ss'_aux :
  forall (A : LinDec) (l : list A) (h : A) (t : list A),
    mins l = h :: t ->
      length (filter (fun x : A => negb (x =? h)) l) < length l.
Proof.
  induction l as [| h' t']; cbn in *; intros.
    inv H.
    destruct (mins t'); dec; inv H.
      1-3: apply le_n_S; apply filter_length.
      apply lt_n_S. apply IHt' with t. reflexivity.
Qed.

Function ss'
  {A : LinDec} (l : list A) {measure length l} : list A :=
match mins l with
    | [] => []
    | h :: t => (h :: t) ++ ss' (filter (fun x => negb (x =? h)) l)
end.
Proof.
  apply ss'_aux.
Defined.

Function ss''
  {A : LinDec} (l : list A) {measure length l} : list A :=
match min l with
    | None => []
    | Some m =>
        filter (fun x => x =? m) l ++
        ss'' (filter (fun x => negb (x =? m)) l)
end.
Proof.
  intros. functional induction min l; cbn; inv teq; dec.
    1-3: apply le_n_S, filter_length.
    apply lt_n_S, IHo. assumption.
Defined.

Function ss_bifilter
  {A : LinDec} (l : list A) {measure length l} : list A :=
match min l with
    | None => []
    | Some m =>
        let
          (l1, l2) := bifilter (fun x => x =? m) l
        in
          l1 ++ ss_bifilter l2
end.
Proof.
  intros. functional induction min l; cbn in *; inv teq;
  rewrite bifilter_spec in *; dec; inv teq0.
    1-3: apply le_n_S, filter_length.
    cbn. apply lt_n_S. eapply IHo; eauto. apply bifilter_spec.
Defined.

(** Da ultimate selection sort! *)

Require Import TrichDec.

Function mins'
  {A : TrichDec} (l : list A) : list A * list A :=
match l with
    | [] => ([], [])
    | h :: t =>
        let
          (mins, rest) := mins' t
        in
          match mins with
              | [] => ([h], rest)
              | m :: ms =>
                  match h <?> m with
                      | Lt => ([h], mins ++ rest)
                      | Eq => (h :: mins, rest)
                      | Gt => (mins, h :: rest)
                  end
          end
end.

Lemma mins'_nil :
  forall (A : TrichDec) (l rest : list A),
    mins' l = ([], rest) -> rest = [].
Proof.
  intros. functional induction mins' l; inv H.
Qed.

Lemma mins'_length :
  forall (A : TrichDec) (l mins rest : list A),
    mins' l = (mins, rest) -> length l = length mins + length rest.
Proof.
  intros. functional induction mins' l; inv H; cbn in *.
    destruct t; cbn in e0.
      inv e0.
      destruct (mins' t), l.
        inv e0.
        destruct (c <?> c0); inv e0.
    1-3: f_equal; rewrite (IHp _ _ e0), ?app_length; cbn; omega.
Qed.

Function ss_mins'
  {A : TrichDec} (l : list A) {measure length l} : list A :=
match mins' l with
    | ([], _) => []
    | (mins, rest) => mins ++ ss_mins' rest
end.
Proof.
  intros. functional induction mins' l; inv teq; cbn in *.
    apply mins'_nil in e0. subst. cbn. apply le_n_S, le_0_n.
    all: apply mins'_length in e0; cbn in e0;
      rewrite e0, ?app_length; omega.
Defined.

(*Time Compute ss natle (cycle 500 testl).
Time Compute ss' natle (cycle 500 testl).
Time Compute ss'' natle (cycle 500 testl).
Time Compute ss_bifilter natle (cycle 500 testl).
Time Compute ss_mins' natlt (cycle 500 testl).*)

(** Time to prove something *)

(*Class MinMaxRest *)