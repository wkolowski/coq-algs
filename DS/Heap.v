Require Export RCCBase.
Require Import BTree.
Require Import BST.
Require Export TrichDec.
Require Import Sorting.Sort.

(** * Various heap property definitions and their relations. *)

Inductive isHeap {A : TrichDec} : BTree A -> Prop :=
    | isHeap_empty : isHeap empty
    | isHeap_node :
        forall (v : A) (l r : BTree A),
          (forall x : A, Elem x l -> v ≤ x) -> isHeap l ->
          (forall x : A, Elem x r -> v ≤ x) -> isHeap r ->
            isHeap (node v l r).

Hint Constructors isHeap : core.

Ltac isHeap :=
repeat match goal with
    | H : isHeap empty        |- _ => inv H
    | H : isHeap (node _ _ _) |- _ => inv H
end.

Inductive OK {A : Type} (R : A -> A -> Prop) (x : A) : BTree A -> Prop :=
    | OK_empty : OK R x empty
    | OK_node  :
        forall (v : A) (l r : BTree A),
          R x v -> OK R x (node v l r).

Inductive isHeap2 {A : Type} (R : A -> A -> Prop) : BTree A -> Prop :=
    | isHeap2_empty : isHeap2 R empty
    | isHeap2_node :
        forall (v : A) (l r : BTree A),
          OK R v l -> OK R v r ->
            isHeap2 R l -> isHeap2 R r -> isHeap2 R (node v l r).

Hint Constructors OK isHeap2 : core.

Ltac ok :=
repeat match goal with
    | H : OK _ _ empty        |- _ => inv H
    | H : OK _ _ (node _ _ _) |- _ => inv H
end.

Ltac isHeap2 :=
repeat match goal with
    | H : isHeap2 _ empty        |- _ => inv H
    | H : isHeap2 _ (node _ _ _) |- _ => inv H
    | _ => ok
end.

Inductive isHeap3 {A : TrichDec} : BTree A -> Prop :=
    | isHeap3_empty : isHeap3 empty
    | isHeap3_singl : forall v : A, isHeap3 (node v empty empty)
    | isHeap3_l :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> isHeap3 (node x l r) -> isHeap3 (node v (node x l r) empty)
    | isHeap3_r :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> isHeap3 (node x l r) -> isHeap3 (node v empty (node x l r))
    | isHeap3_lr :
        forall (v lv rv : A) (ll lr rl rr : BTree A),
          v ≤ lv -> isHeap3 (node lv ll lr) ->
          v ≤ rv -> isHeap3 (node rv rl rr) ->
            isHeap3 (node v (node lv ll lr) (node rv rl rr)).

Hint Constructors isHeap3 : core.

Lemma isHeap2_isHeap :
  forall {A : TrichDec} (t : BTree A),
    isHeap2 (@trich_le A) t <-> isHeap t.
Proof.
  split.
    induction 1; constructor; auto.
      inv IHisHeap2_1; isHeap2; inv 1; trich.
        specialize (H3 _ H8). trich.
        specialize (H5 _ H8). trich.
      inv IHisHeap2_2; isHeap2; inv 1; trich.
        specialize (H3 _ H8). trich.
        specialize (H5 _ H8). trich.
    induction 1; constructor; auto.
      inv IHisHeap1.
      inv IHisHeap2.
Qed.

Lemma isHeap2_isHeap3 :
  forall {A : TrichDec} (t : BTree A),
    isHeap2 (@trich_le A) t <-> isHeap3 t.
Proof.
  split.
    induction 1.
      constructor.
      inv IHisHeap2_1; inv IHisHeap2_2; isHeap2; constructor; auto.
    induction 1; constructor; auto.
Qed.

(** * Relations between [isHeap] and various [BTree] functions. *)

Lemma isHeap_singleton :
  forall (A : TrichDec) (x : A),
    isHeap (singleton x).
Proof.
  intros. unfold singleton. constructor; auto; inv 1.
Qed.

Lemma isHeap_isEmpty :
  forall (A : TrichDec) (t : BTree A),
    isEmpty t = true -> isHeap t.
Proof.
  destruct t; intro.
    constructor.
    cbn in H. congruence.
Qed.

(** * The rest *)

Function sendDown {A : TrichDec} (x : A) (t : BTree A) : A * BTree A :=
match t with
    | empty => (x, empty)
    | node v l r =>
        let
          '(m, M) := trich_minmax x v
        in
          match l, r with
              | empty, empty => (m, (node M l r))
              | empty, _ =>
                  let '(m', r') := sendDown M r in
                    let (m1, m2) := trich_minmax m m' in
                    (m1, node m2 empty r')
              | _, empty =>
                  let '(m', l') := sendDown M l in
                    let (m1, m2) := trich_minmax m m' in
                    (m1, node m2 l' empty)
              | node vl _ _, node vr _ _ =>
                  if vl ≤? vr
                  then
                    let '(m', l') := sendDown M l in
                    let (m1, m2) := trich_minmax m m' in
                      (m1, node m2 l' r)
                  else
                    let '(m', r') := sendDown M r in
                    let (m1, m2) := trich_minmax m m' in
                      (m1, node m2 l r')
          end
end.

Ltac wut :=
repeat match goal with
    | H : match ?x with _ => _ end |- _ => destruct x
    | H : False |- _ => contradiction
    | H : True |- _ => clear H
    | H : node _ _ _ = empty |- _ => inv H
    | |- _ /\ _ => split
    | |- _ = _ => reflexivity
    | H : Elem _ empty |- _ => inv H
    | H : Elem _ (node _ empty empty) |- _ => inv H
    | H : (_, _) = (_, _) |- _ => inv H
    | H : context [_ ≤? _] |- _ => trich
    | H : (_, _) = (_, _) |- _ => inv H
    | _ => subst; trich
end.

Ltac m := unfold trich_min, trich_max, trich_minmax in *; wut.

Lemma Elem_sendDown :
  forall {A : TrichDec} {x m : A} {t t' : BTree A},
    sendDown x t = (m, t') ->
      x = m \/ Elem x t'.
Proof.
  intros A x m t. revert m.
  functional induction sendDown x t;
  inv 1; wut; edestruct IHp; eauto; trich.
Qed.

Lemma Elem_sendDown2 :
  forall (A : TrichDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      (x = m (*/\ t = t'*)) \/ Elem x t'.
Proof.
  intros A x m t. revert m.
  functional induction sendDown x t; inv 1; trich;
  try
  match goal with
      | H : sendDown _ _ = _ |- _ =>
          specialize (IHp _ _ H); apply Elem_sendDown in H
  end;
  wut; inv IHp.
Qed.

Lemma Elem_sendDown' :
  forall {A : TrichDec} {x m : A} {t t' : BTree A},
    sendDown x t = (m, t') ->
      forall y : A, Elem y t ->
        y = m \/ Elem y t'.
Proof.
  intros A x m t. revert m.
  functional induction sendDown x t;
  inv 1; inv 1.
    trich.
    all: try
    match goal with
        | IH : forall _ _, sendDown _ _ = _ -> _,
          e  : sendDown _ _ = _ 
          |- _ => specialize (IH _ _ e);
                  destruct (Elem_sendDown e);
                  trich;
                  edestruct IHp; eauto; trich
    end.
Qed.

(* TODO *) Lemma Elem_sendDown'' :
  forall (A : TrichDec) (x m y : A) (t t' : BTree A),
    sendDown x t = (m, t') -> Elem y t ->
      (x = m (*/\ t = t' TODO *)) \/
      (y = m /\ Elem x t').
Proof.
(*
  intros A x m y t. revert m y.
  functional induction sendDown x t; cbn; intros; wut.
    m.
    inv H0.
      apply Elem_sendDown in e3. destruct e3; subst; m.
      destruct (IHp _ _ e3 _ H1); subst; m.
    inv H0.
      apply Elem_sendDown in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
    inv H0.
      apply Elem_sendDown in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
*)
Admitted.

Function makeHeap {A : TrichDec} (t : BTree A) : BTree A :=
match t with
    | empty => empty
    | node v l r =>
        match makeHeap l, makeHeap r with
            | empty, empty => node v empty empty
            | empty, r' =>
                let '(m, r'') := sendDown v r' in node m empty r''
            | l', empty =>
                let '(m, l'') := sendDown v l' in node m l'' empty
            | node vl _ _ as l', node vr _ _ as r' =>
                if vl ≤? vr
                then let '(m, l'') := sendDown v l' in node m l'' r'
                else let '(m, r'') := sendDown v r' in node m l' r''
        end
end.

(* Lemma minmax_leq :
  forall (A : TrichDec) (x y m M : A),
    trminmax x y = (m, M) -> m ≤ M.
Proof.
  unfold minmax. intros. trich.
Qed.

Lemma leq_min_max :
  forall (A : TrichDec) (x y : A),
    min x y ≤ max x y.
Proof.
  unfold min, max. intros. trich.
Qed.
 *)
Lemma isHeap_Elem :
  forall (A : TrichDec) (x y v : A) (l r : BTree A),
    Elem y (node v l r) -> isHeap (node v l r) ->
      x ≤ v -> x ≤ y.
Proof.
  intros. remember (node v l r) as t. revert v l r Heqt x H1 H0.
  induction H; intros; inv Heqt.
    destruct l0.
      inv H.
      inv H0. eapply IHElem; eauto. specialize (H5 c ltac:(constructor)). trich.
    destruct r0.
      inv H.
      inv H0; eapply IHElem; eauto. specialize (H7 c ltac:(constructor)). trich.
Qed.

Lemma sendDown_spec1 :
  forall (A : TrichDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> isHeap t ->
      t = empty /\ t' = empty \/
      exists (v : A) (l r : BTree A),
        t' = node v l r /\ isHeap t' /\ m ≤ v.
Proof.
  intros A x m t. revert m.
  functional induction sendDown x t; inv 1; inv 1; right.
    do 3 eexists. split; try reflexivity. split.
      apply isHeap_singleton.
      trich.
    do 3 eexists. split; try reflexivity.
  Ltac aa := match goal with
      | H : isHeap empty        |- _ => inv H
      | H : isHeap (node _ _ _) |- _ => inv H
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | IH : forall _ _ , sendDown _ _ = _ -> ?isHeap -> _,
        H1 : sendDown _ _ = _,
        H2 : ?isHeap |- _ =>
            specialize (IH _ _ H1 H2);
            decompose [and or ex] IH; clear IH; subst
      | H : node _ _ _ = empty |- _ => inv H
      | |- exists _, _ => eexists
      | |- _ /\ _ => split
      | |- _ = _ => reflexivity
      | |- trich_min _ _ ≤ trich_max _ _ => trich
      | |- isHeap _ => constructor
      | H : sendDown ?M _ = _ |- _ =>
          let H' := fresh "H" in
          assert (H' := Elem_sendDown'' _ M _ _ _ _ H ltac:(constructor));
          decompose [and or] H'; clear H H'; subst
      | H : node _ _ _ = node _ _ _ |- _ => inv H
  end.
Admitted.

Lemma Elem_node :
  forall (A : Type) (x v : A) (l r : BTree A),
    Elem x (node v l r) <-> x = v \/ Elem x l \/ Elem x r.
Proof.
  split.
    inv 1.
    firstorder. subst. constructor.
Qed.

Lemma sendDown_spec2 :
  forall (A : TrichDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> isHeap t ->
      forall a : A, Elem a t -> m ≤ a.
Proof.
  Ltac wut' := 
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | H : (_, _) = _ |- _ => inv H
      | H : Elem _ empty |- _ => inv H
      | H : isHeap empty |- _ => clear H
      | H : isHeap (node _ ?x ?y) |- _ =>
          tryif is_var x then fail else
          tryif is_var y then fail else inv H
      | IH : forall _, Elem _ _ -> _,
         H : Elem _ _
        |- _ => specialize (IH _ H)
  end.
  intros A x m t. revert m.
  functional induction @sendDown A x t;
  inv 1; inv 1; inv 1;
  try match goal with
    | IH : forall _, Elem _ _ -> _,
       H : Elem _ _
      |- _ => specialize (IH _ H)
  end; trich.
Qed.

Lemma sendDown_spec2' :
  forall (A : TrichDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      isHeap2 trich_le t -> isHeap2 trich_le t'.
Proof.
  intros until t. revert m.
  functional induction sendDown x t;
  inv 1; inv 1; isHeap2.
    inv H4.
      contradiction.
      constructor; auto; admit.
    inv H3.
      contradiction.
      isHeap2. constructor; auto.
        admit.
        eapply IHp; eauto.
    constructor; eauto.
Admitted.

Lemma isHeap_makeHeap :
  forall (A : TrichDec) (t : BTree A),
    isHeap (makeHeap t).
Proof.
  intros. functional induction makeHeap t;
  repeat match goal with
      | H : Elem _ empty |- _            => inv H
      |                  |- isHeap empty => constructor
      | H : match ?x with _ => _ end |- _ => destruct x eqn: Hx
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | H : Elem _ empty |- _ => inv H
      | H : makeHeap _ = _ |- _ => rewrite ?H in *; clear H
      | H : isHeap empty |- _ => clear H
  end;
  try match goal with
      | H : sendDown _ _ = _, H0 : isHeap _ |- _ =>
          let H' := fresh "H" in 
          assert (H' := sendDown_spec1 _ _ _ _ _ H H0);
          decompose [and or ex] H'; clear H'; subst
  end;
  constructor; try assumption; try congruence; auto;
  intros;
  repeat match goal with
      | H : Elem _ empty |- _ => inv H
      | H : sendDown  _ _ = _ |- _ => apply Elem_sendDown in H
      | H : isHeap (node _ _ _) |- _ => inv H
  end.
    inv e2. inv H; trich.
Admitted.