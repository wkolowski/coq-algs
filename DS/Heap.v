

Require Import BTree.
Require Export LinDec.
Require Import Sorting.Sort.

Definition minmax {A : LinDec} (x y : A) : A * A :=
  if x <=? y then (x, y) else (y, x).

Definition min {A : LinDec} (x y : A) : A :=
  if x <=? y then x else y.

Definition max {A : LinDec} (x y : A) : A :=
  if y <=? x then x else y.

Function sendDown {A : LinDec} (x : A) (t : BTree A) : A * BTree A :=
match t with
    | empty => (x, empty)
    | node v l r =>
        let
          '(m, M) := minmax x v
        in
          match l, r with
              | empty, empty => (m, (node M l r))
              | empty, _ =>
                  let '(m', r') := sendDown M r in
                    (min m m', node (max m m') empty r')
              | _, empty =>
                  let '(m', l') := sendDown M l in
                    (min m m', node (max m m') l' empty)
              | node vl _ _, node vr _ _ =>
                  if vl <=? vr
                  then
                    let '(m', l') := sendDown M l in
                      (min m m', node (max m m') l' r)
                  else
                    let '(m', r') := sendDown M r in
                      (min m m', node (max m m') l r')
          end
end.

Ltac dec' := cbn;
repeat match goal with
    | |- context [?x =? ?y] =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | |- context [?x <=? ?y] =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
    | H : context [?x =? ?y] |- _ =>
        try destruct (LinDec_eqb_spec natle x y);
        try destruct (LinDec_eqb_spec _ x y); subst; intros
    | H : context [?x <=? ?y] |- _ =>
        try destruct (@leqb_spec natle x y);
        try destruct (leqb_spec x y); intros
    | H : ?a ≤ ?b, H' : ?b ≤ ?a |- _ =>
        let H'' := fresh "H" in
          assert (H'' := leq_antisym _ _ H H'); clear H H'; subst
end; cbn;
repeat match goal with
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
    | H : True |- _ => clear H
    | H : ?x = ?x |- _ => clear H
end; try congruence.

Ltac wut :=
repeat match goal with
    | H : match ?x with _ => _ end |- _ => destruct x
    | H : False |- _ => contradiction
    | H : True |- _ => clear H
    | H : node _ _ _ = empty |- _ => inv H
    | |- _ /\ _ => split
    | |- _ = _ => reflexivity
    | H : elem _ empty |- _ => inv H
    | H : elem _ (node _ empty empty) |- _ => inv H
    | H : (_, _) = (_, _) |- _ => inv H
    | H : context [_ <=? _] |- _ => dec'
end.

Ltac m := unfold min, max, minmax in *; wut.

Lemma sendDown_elem :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      x = m \/ elem x t'.
Proof.
  intros A x m t. revert m.
  functional induction @sendDown A x t; inv 1; dec;
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | IH : forall _ _, _ -> _, H : sendDown _ _ = _ |- _ =>
          destruct (IH _ _ H); clear IH; subst
  end;
  unfold min, max, minmax in *; dec; inv e0.
Qed.

Lemma sendDown_elem2 :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      (x = m /\ t = t') \/ elem x t'.
Proof.
  intros A x m t. revert m.
  functional induction @sendDown A x t; inv 1; dec.
  Focus 2.
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | IH : forall _ _, _ -> _, H : sendDown _ _ = _ |- _ =>
          decompose [and or] (IH _ _ H); clear IH; subst
  end;
  unfold min, max, minmax in *; dec; inv e0.
(*    cbn in e3. destruct (minmax M c), r1, r2. wut. inv H; wut.
    apply sendDown_elem in e3. destruct e3; subst; wut.
*)
Admitted.

Lemma sendDown_elem' :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') ->
      forall y : A, elem y t ->
        y = m \/ elem y t'.
Proof.
  intros A x m t. revert m.
  functional induction @sendDown A x t; cbn; intros; wut.
    m.
    inv H0.
      apply sendDown_elem in e3. destruct e3; subst; m.
      destruct (IHp _ _ e3 _ H1); subst; m.
    inv H0.
      apply sendDown_elem in e3. destruct e3; subst; m.
      destruct (IHp _ _ e3 _ H1); subst; m.
    inv H0.
      apply sendDown_elem in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
    inv H0.
      apply sendDown_elem in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
Qed.

(* TODO *) Lemma sendDown_elem'' :
  forall (A : LinDec) (x m y : A) (t t' : BTree A),
    sendDown x t = (m, t') -> elem y t ->
      (x = m /\ t = t') \/
      (y = m /\ elem x t').
Proof.
(*
  intros A x m y t. revert m y.
  functional induction @sendDown A x t; cbn; intros; wut.
    m.
    inv H0; wut.
      apply sendDown_elem in e3. destruct e3; subst; m.
      destruct (IHp _ _ _ e3 H1); subst; m.
    inv H0.
      apply sendDown_elem in e3. destruct e3; subst; m.
      destruct (IHp _ _ e3 _ H1); subst; m.
    inv H0.
      apply sendDown_elem in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
    inv H0.
      apply sendDown_elem in e4. destruct e4; subst; m.
      destruct (IHp _ _ e4 _ H1); subst; m.
*)
Admitted.

Function makeHeap {A : LinDec} (t : BTree A) : BTree A :=
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
                if vl <=? vr
                then let '(m, l'') := sendDown v l' in node m l'' r'
                else let '(m, r'') := sendDown v r' in node m l' r''
        end
end.

Inductive ih {A : LinDec} : BTree A -> Prop :=
    | ih_empty : ih empty
    | ih_singl : forall v : A, ih (node v empty empty)
    | ih_l :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> ih (node x l r) -> ih (node v (node x l r) empty)
    | ih_r :
        forall (v x : A) (l r : BTree A),
          v ≤ x -> ih (node x l r) -> ih (node v empty (node x l r))
    | ih_lr :
        forall (v lv rv : A) (ll lr rl rr : BTree A),
          v ≤ lv -> ih (node lv ll lr) ->
          v ≤ rv -> ih (node rv rl rr) ->
            ih (node v (node lv ll lr) (node rv rl rr)).

Lemma minmax_leq :
  forall (A : LinDec) (x y m M : A),
    minmax x y = (m, M) -> m ≤ M.
Proof.
  unfold minmax. intros. dec. inv H.
Qed.

Lemma leq_min_max :
  forall (A : LinDec) (x y : A),
    min x y ≤ max x y.
Proof.
  unfold min, max. intros. dec.
Qed.

Lemma ih_elem :
  forall (A : LinDec) (x y v : A) (l r : BTree A),
    elem y (node v l r) -> ih (node v l r) ->
      x ≤ v -> x ≤ y.
Proof.
  intros. remember (node v l r) as t. revert v l r Heqt x H1 H0.
  induction H; intros; inv Heqt.
    destruct l0.
      inv H.
      inv H0; eapply IHelem; dec.
    destruct r0.
      inv H.
      inv H0; eapply IHelem; dec.
Qed.

Lemma sendDown_ih :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> ih t ->
      t = empty /\ t' = empty \/
      exists (v : A) (l r : BTree A),
        t' = node v l r /\ ih t' /\ m ≤ v.
Proof.
  intros A x m t. revert m.
  functional induction @sendDown A x t; inv 1; right; inv H;
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | IH : forall _ _ , sendDown _ _ = _ -> ?ih -> _,
        H1 : sendDown _ _ = _,
        H2 : ?ih |- _ =>
            specialize (IH _ _ H1 H2);
            decompose [and or ex] IH; clear IH; subst
      | H : node _ _ _ = empty |- _ => inv H
      | |- exists _, _ => eexists
      | |- _ /\ _ => split
      | |- _ = _ => reflexivity
      | |- min _ _ ≤ max _ _ => apply leq_min_max
      | |- ih _ => constructor
      | H : sendDown ?M _ = _ |- _ =>
          let H' := fresh "H" in
          assert (H' := sendDown_elem'' _ M _ _ _ _ H ltac:(constructor));
          decompose [and or] H'; clear H H'; subst
      | H : node _ _ _ = node _ _ _ |- _ => inv H
  end;
  try assumption;
  unfold max, minmax in *; dec'; inv e0; dec.
Qed.

Lemma elem_node :
  forall (A : Type) (x v : A) (l r : BTree A),
    elem x (node v l r) <-> x = v \/ elem x l \/ elem x r.
Proof.
  split.
    inv 1.
    firstorder. subst. constructor.
Qed.

Lemma ih_sendDown_arg :
  forall (A : LinDec) (x m : A) (t t' : BTree A),
    sendDown x t = (m, t') -> ih t ->
      forall a : A, elem a t -> m ≤ a.
Proof.
  Ltac wut' := 
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | H : (_, _) = _ |- _ => inv H
      | H : elem _ empty |- _ => inv H
      | H : ih empty |- _ => clear H
      | H : ih (node _ ?x ?y) |- _ =>
          tryif is_var x then fail else
          tryif is_var y then fail else inv H
  end.
  intros A x m t. revert m.
  functional induction @sendDown A x t; intros; wut'.
    inv H1; try inv H0. unfold minmax in e0; dec'; inv e0.
    inv H1.
      unfold minmax, min in *; dec'; inv e0; dec.
      inv H0.
      unfold min; dec'.
        apply leq_trans with m'.
          assumption.
          eapply IHp; eauto.
        eapply IHp; eauto.
    inv H1.
      unfold minmax, min in *; dec'; inv e0; dec.
      unfold min; dec'.
        apply leq_trans with m'.
          assumption.
          eapply IHp; eauto.
        eapply IHp; eauto.
      inv H0.
    inv H1.
      unfold minmax, min in *; dec'; inv e0; dec.
      unfold min; dec'.
        apply leq_trans with m'.
          assumption.
          eapply IHp; eauto.
        eapply IHp; eauto.
      apply (ih_elem _ _ _ _ _ _ H0 H11).
        unfold minmax, min in *; dec'; inv e0; dec.
    inv H1.
      unfold minmax, min in *; dec'; inv e0; dec.
      apply (ih_elem _ _ _ _ _ _ H0 H9).
        unfold minmax, min in *; dec'; inv e0; dec.
      unfold min; dec'.
        apply leq_trans with m'.
          assumption.
          eapply IHp; eauto.
        eapply IHp; eauto.
Qed.

Lemma makeHeap_ih :
  forall (A : LinDec) (t : BTree A),
    ih (makeHeap t).
Proof.
  intros. functional induction @makeHeap A t;
  repeat match goal with
      | H : match ?x with _ => _ end |- _ => destruct x eqn: Hx
      | H : False |- _ => contradiction
      | H : True |- _ => clear H
      | H : elem _ empty |- _ => inv H
      | H : makeHeap _ = _ |- _ => rewrite ?H in *; clear H
      | H : ih empty |- _ => clear H
  end;
  try match goal with
      | H : sendDown _ _ = _, H0 : ih _ |- _ =>
          let H' := fresh "H" in 
          assert (H' := sendDown_ih _ _ _ _ _ H H0);
          decompose [and or ex] H'; clear H'; subst
  end;
  constructor; try assumption; try congruence.
    eapply leq_trans with vl.
      eapply ih_sendDown_arg; eauto.
      dec'.
    eapply leq_trans with vr.
      eapply ih_sendDown_arg; eauto.
      dec.
Qed.