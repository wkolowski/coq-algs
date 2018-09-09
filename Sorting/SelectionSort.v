Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Export Sorting.Sort.

Set Implicit Arguments.

Function min {A : LinDec} (l : list A) : option (A * list A) :=
match l with
    | [] => None
    | h :: t =>
        match min t with
            | None => Some (h, [])
            | Some (m, l') =>
                if h <=? m then Some (h, m :: l') else Some (m, h :: l')
        end
end.

Function ss {A : LinDec} (l : list A) {measure length l} : list A :=
match min l with
    | None => []
    | Some (m, l') => m :: ss l'
end.
Proof.
  induction l as [| h t]; cbn; intros.
    inv teq.
    destruct (min t) eqn: Heq.
      destruct p0. dec; inv teq; cbn; apply lt_n_S; eapply IHt; eauto.
      inv teq. cbn. apply le_n_S, le_0_n.
Defined.

Lemma Permutation_min :
  forall (A : LinDec) (l l' : list A) (m : A),
    min l = Some (m, l') -> Permutation (m :: l') l.
Proof.
  intros A l. functional induction @min A l; cbn; inv 1.
    destruct t; cbn in e0.
      reflexivity.
      destruct (min t).
        destruct p. 1-2: dec.
    rewrite Permutation.perm_swap. auto.
Qed.

Lemma Permutation_ss :
  forall (A : LinDec) (l : list A),
    Permutation (ss A l) l.
Proof.
  intros. functional induction @ss A l.
    destruct l; cbn in e.
      reflexivity.
      destruct (min l); try destruct p; dec.
    apply Permutation_min in e. rewrite <- e, IHl0. reflexivity.
Qed.

Lemma min_spec :
  forall (A : LinDec) (l l' : list A) (m : A),
    min l = Some (m, l') -> forall x : A, In x l' -> leq m x.
Proof.
  intros A l.
  functional induction @min A l; inv 1; cbn; intros; destruct H; subst; dec.
Qed.

Lemma Sorted_ss :
  forall (A : LinDec) (l : list A),
    Sorted A (ss A l).
Proof.
  intros. functional induction @ss A l.
    destruct l; dec.
    apply Sorted_cons.
      intros. assert (In x l').
        apply Permutation_in with (ss A l').
          apply Permutation_ss.
          assumption.
        eapply min_spec; eauto.
      assumption.
Qed.




(*
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
  intros. revert m H.
  functional induction min l; inv 1; intros.
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
  intros. revert x m H0 H. functional induction min l; do 2 inv 1.
    destruct t.
      inv H0.
      cbn in e0. destruct (min t); inv e0.
    apply leq_trans with m0; dec.
    dec.
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

Theorem Sorted_ss :
  forall (A : LinDec) (l : list A), Sorted A (ss A l).
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
    Sorted_sort := Sorted_ss A;
    sort_perm := ss_perm A
}.
*)

(** Selection sort on steroids *)

(*
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
    | Some (m, _) =>
        filter (fun x => x =? m) l ++
        ss'' (filter (fun x => negb (x =? m)) l)
end.
Proof.
  intros. functional induction min l; cbn; inv teq; dec.
    1-3: apply le_n_S, filter_length.
    apply lt_n_S, IHo. assumption.
Defined.

(** Spec of [ss'']. *)

Lemma perm_filter :
  forall (A : LinDec) (p : A -> bool) (l : list A),
    perm A l (filter p l ++ filter (fun x => negb (p x)) l).
Proof.
  induction l as [| h t]; cbn; intros.
    reflexivity.
    destruct (p h); cbn.
      apply perm_cons. assumption.
        symmetry. rewrite perm_front. apply perm_cons.
          symmetry. assumption.
Qed.

Theorem ss''_perm :
  forall (A : LinDec) (l : list A),
    perm A l (ss'' A l).
Proof.
  intro A.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; cbn; intros.
      reflexivity.
      rewrite ss''_equation. destruct (min (h :: t)) eqn: Hc.
        cbn. dec.
          apply perm_cons. eapply perm_trans.
            apply perm_filter.
            apply perm_app.
              reflexivity.
              apply H. red. cbn. apply le_n_S. apply filter_length.
          rewrite (perm_filter A (fun x => x =? c)). cbn. dec. apply perm_app.
            reflexivity.
            apply H. red. cbn in *. apply lt_n_S.
              revert H.
              functional induction min t; cbn in *; inv 1; dec.
                1-3: apply le_n_S; apply filter_length.
                apply le_n_S. apply IHo.
                  rewrite e0. dec.
                  intros. apply H. red. red in H0. cbn in *. omega.
        cbn in Hc. destruct (min t); inv Hc.
Qed.

Lemma min_cons :
  forall (A : LinDec) (h : A) (t : list A),
    min (h :: t) = Some h \/ min (h :: t) = min t.
Proof.
  cbn; intros. destruct (min t).
    dec.
    left. reflexivity.
Qed.

Lemma min_cons' :
  forall (A : LinDec) (x y : A) (l : list A),
    min (x :: y :: l) = Some x \/
    min (x :: y :: l) = Some y \/
    min (x :: y :: l) = min l.
Proof.
  cbn; intros. destruct (min l); dec.
Qed.

Lemma filter_cons :
  forall (A : Type) (p : A -> bool) (h : A) (t : list A),
    filter p (h :: t) =
    if p h
    then h :: filter p t
    else filter p t.
Proof. reflexivity. Qed.

Lemma lengthOrder_filter_min :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m ->
      lengthOrder (filter (fun x : A => negb (x =? m)) l) l.
Proof.
  intros. functional induction min l; red; cbn; inv H; dec.
    1-3: apply le_n_S, filter_length.
    apply lt_n_S. apply IHo. assumption.
Qed.

Lemma ss''_ind :
  forall (A : LinDec) (P : list A -> list A -> Prop),
    (forall l : list A, min l = None -> P l []) ->
    (forall (l : list A) (m : A),
      min l = Some m ->
        P (filter (fun x => negb (x =? m)) l)
          (ss'' A (filter (fun x => negb (x =? m)) l)) ->
        P l (ss'' A l)) ->
    forall l : list A, P l (ss'' A l).
Proof.
  intros until 2.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intros.
      cbn. apply H. cbn. reflexivity.
      destruct (min (h :: t)) eqn: Hc.
        apply (H0 (h :: t) c).
          assumption.
          apply H1. apply lengthOrder_filter_min. assumption.
        cbn in Hc. destruct (min t); inv Hc.
Qed.

Lemma Sorted_filter_eq :
  forall (A : LinDec) (m : A) (l : list A),
    Sorted A (filter (fun x : A => x =? m) l).
Proof.
  induction l; cbn.
    constructor.
    dec.
      match goal with
          | |- Sorted ?A (?h :: ?t) => change (Sorted A ([h] ++ t))
      end.
      apply Sorted_app.
        constructor.
        assumption.
        inv 1. clear IHl. induction l as [| h t]; cbn; intros.
          contradiction.
          dec. inv H.
Qed.

Theorem Sorted_ss'' :
  forall (A : LinDec) (l : list A),
    Sorted A (ss'' A l).
Proof.
  intros A.
  apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intros.
      cbn. constructor.
      rewrite ss''_equation. destruct (min (h :: t)) eqn: Hc.
        2: constructor.
        apply Sorted_app.
          apply Sorted_filter_eq.
          apply H. apply lengthOrder_filter_min. assumption.
          intros. rewrite filter_In in H0. destruct H0. dec.
            pose ss''_perm. symmetry in p.
              pose (perm_In A y _ _ H1 (p A _)). clearbody i.
              apply filter_In in i. destruct i. dec.
              apply min_spec with (h :: t); assumption.
Qed.

(** Wut *)

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
  intros A l. functional induction min l; cbn in *; inv 1;
  rewrite bifilter_spec in *; dec; inv teq0.
    1-3: apply le_n_S, filter_length.
    cbn. apply lt_n_S. eapply IHo; eauto. apply bifilter_spec.
Defined.

Lemma ss_bifilter_spec :
  forall (A : LinDec) (l : list A),
    ss_bifilter A l = ss'' A l.
Proof.
  intro A. apply well_founded_ind with lengthOrder.
    apply lengthOrder_wf.
    destruct x as [| h t]; intros.
      cbn. reflexivity.
      rewrite ss_bifilter_equation, ss''_equation.
        destruct (min (h :: t)) eqn: Hc.
          rewrite bifilter_spec. f_equal. apply H.
            apply lengthOrder_filter_min. assumption.
        reflexivity.
Qed.

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
  intros A l. functional induction mins' l; inv 1; cbn in *.
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
*)

(** Time to prove something *)

Class Select (A : LinDec) : Type :=
{
    select :> list A -> list A * list A * list A;
    select_mins :
      forall l mins rest maxes : list A,
        select l = (mins, rest, maxes) ->
          forall x y : A, In x mins -> In y l -> x ≤ y;
    select_maxes :
      forall l mins rest maxes : list A,
        select l = (mins, rest, maxes) ->
          forall x y : A, In x l -> In y maxes -> x ≤ y;
    select_Permutation :
      forall l mins rest maxes : list A,
        select l = (mins, rest, maxes) ->
          Permutation l (mins ++ rest ++ maxes);
    select_length_rest :
      forall l mins rest maxes : list A,
        select l = (mins, rest, maxes) ->
          mins = [] /\ rest = [] /\ maxes = [] \/
          length rest < length l;
}.

Coercion select : Select >-> Funclass.

Function gss
  {A : LinDec} (s : Select A) (l : list A)
  {measure length l} : list A :=
match select l with
    | ([], [], []) => []
    | (mins, rest, maxes) =>
        mins ++ gss s rest ++ maxes
end.
Proof.
  all: intros; subst;
  apply select_length_rest in teq;
  decompose [and or] teq; clear teq;
  try congruence; try assumption.
Defined.

Lemma Permutation_gss :
  forall (A : LinDec) (s : Select A) (l : list A),
    Permutation (gss s l) l.
Proof.
  intros. functional induction @gss A s l.
    apply select_Permutation in e. cbn in e. symmetry. assumption.
    rewrite IHl0. symmetry. apply select_Permutation. assumption.
Qed.

Lemma select_In :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A) (x : A),
    select l = (mins, rest, maxes) ->
      In x mins \/ In x rest \/ In x maxes -> In x l.
Proof.
  intros. eapply Permutation_in.
    symmetry. apply select_Permutation. eassumption.
    apply in_or_app. decompose [or] H0; clear H0.
      left. assumption.
      right. apply in_or_app. left. assumption.
      right. apply in_or_app. right. assumption.
Qed.

Lemma select_mins_maxes :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A),
    select l = (mins, rest, maxes) ->
      forall x y : A, In x mins -> In y maxes -> x ≤ y.
Proof.
  intros. eapply select_mins; try eassumption.
  eapply select_In; eauto.
Qed.

Lemma select_mins_same :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A),
    select l = (mins, rest, maxes) ->
      forall x y : A, In x mins -> In y mins -> x = y.
Proof.
  intros. apply leq_antisym.
    eapply select_mins; eauto. eapply select_In; eauto.
    eapply select_mins; eauto. eapply select_In; eauto.
Qed.

Lemma select_maxes_same :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A),
    select l = (mins, rest, maxes) ->
      forall x y : A, In x maxes -> In y maxes -> x = y.
Proof.
  intros. apply leq_antisym.
    eapply select_maxes; eauto. eapply select_In; eauto.
    eapply select_maxes; eauto. eapply select_In; eauto.
Qed.

Lemma same_Sorted :
  forall (A : LinDec) (x : A) (l : list A),
    (forall y : A, In y l -> x = y) ->
      Sorted A l.
Proof.
  intros A x.
  induction l as [| h t]; cbn; intros.
    constructor.
    specialize (IHt ltac:(auto)). change (Sorted A ([h] ++ t)).
      apply Sorted_app.
        constructor.
        assumption.
        assert (x = h) by auto. inv 1. intro. rewrite (H y).
          dec.
          right. assumption.
Qed.

Lemma Sorted_select_mins :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A),
    select l = (mins, rest, maxes) -> Sorted A mins.
Proof.
  destruct mins; intros.
    constructor.
    apply same_Sorted with c. intros. eapply select_mins_same.
      exact H.
      left. reflexivity.
      assumption.
Qed.

Lemma Sorted_select_maxes :
  forall (A : LinDec) (s : Select A) (l mins rest maxes : list A),
    select l = (mins, rest, maxes) -> Sorted A maxes.
Proof.
  destruct maxes; intros.
    constructor.
    apply same_Sorted with c. intros. eapply select_maxes_same.
      exact H.
      left. reflexivity.
      assumption.
Qed.

Lemma gss_In :
  forall (A : LinDec) (s : Select A) (x : A) (l : list A),
    In x (gss s l) <-> In x l.
Proof.
  intros. split; intros.
    eapply Permutation_in.
      apply Permutation_gss.
      assumption.
    eapply Permutation_in.
      symmetry. apply Permutation_gss.
      assumption.
Qed.

Lemma gSorted_ss :
  forall (A : LinDec) (s : Select A) (l : list A),
    Sorted A (gss s l).
Proof.
  intros. functional induction @gss A s l; try clear y.
    constructor.
    apply Sorted_app.
      eapply Sorted_select_mins. eassumption.
      apply Sorted_app.
        assumption.
        eapply Sorted_select_maxes. eassumption.
        intros. rewrite gss_In in H. eapply select_maxes; eauto.
          eapply select_In; eauto.
      intros. apply in_app_or in H0. destruct H0.
        rewrite gss_In in H0. eapply select_mins; try eassumption.
          eapply select_In; eauto.
        eapply select_mins_maxes; eauto.
Qed.

Instance Sort_gss (A : LinDec) (s : Select A) : Sort A :=
{
    sort := gss s;
    Sorted_sort := gSorted_ss s;
(*    sort_perm := gss_perm s;*)
}.
Proof.
  intros. apply Permutation_gss.
Defined.

(*Require Import SortSpec.*)

(*
Lemma min_In :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m -> In m l.
Proof.
  intros. functional induction min l; cbn; inv H.
Qed.

Lemma lengthOrder_removeFirst_min :
  forall (A : LinDec) (m : A) (l : list A),
    min l = Some m -> lengthOrder (removeFirst m l) l.
Proof.
  intros. functional induction min l; inv H; dec; red; cbn; try omega.
    apply lt_n_S. apply IHo. assumption.
Qed.

Instance Select_min (A : LinDec) : Select A :=
{
    select l :=
      match min l with
          | None => ([], [], [])
          | Some m => ([m], removeFirst m l, [])
      end;
}.
Proof.
  all: intros; destruct (min l) eqn: Hc; inv H.
    inv H0. eapply min_spec; eauto.
    rewrite app_nil_r. cbn.
      apply perm_Permutation, removeFirst_In_perm, min_In, Hc.
    destruct l; cbn in *.
      reflexivity.
      destruct (min l); inv Hc.
    right. apply lengthOrder_removeFirst_min. assumption.
Defined.
*)