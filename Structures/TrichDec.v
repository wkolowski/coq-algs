Require Export RCCBase.

Set Implicit Arguments.

Class TrichDec : Type :=
{
    carrier : Type;
    trich_lt : carrier -> carrier -> Prop;
    trich_lt_antisym :
      forall {x y : carrier}, trich_lt x y -> ~ trich_lt y x;
    trich_lt_trans :
      forall {x y z : carrier}, trich_lt x y -> trich_lt y z -> trich_lt x z;
    cmp : carrier -> carrier -> comparison;
    cmp_spec :
      forall x y : carrier, CompareSpec (x = y) (trich_lt x y) (trich_lt y x) (cmp x y);
}.

Coercion carrier : TrichDec >-> Sortclass.

(* Hint Resolve trich_lt_trans : core. *)

Definition trich_ltb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Lt => true
    | _ => false
end.

Definition trich_leb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Lt | Eq => true
    | Gt      => false
end.

Definition trich_eqb {A : TrichDec} (x y : A) : bool :=
match cmp x y with
    | Eq => true
    | _  => false
end.

Definition trich_le {A : TrichDec} (x y : A) : Prop :=
  trich_lt x y \/ x = y.

Infix "<?>" := cmp (at level 30).
Infix "<?" := trich_ltb (at level 70).
Notation "x >? y" := (trich_ltb y x) (at level 30, only parsing).
Infix "≤?" := trich_leb (at level 30).
Notation "x >=? y" := (trich_leb y x) (at level 30, only parsing).
Infix "=?" := trich_eqb (at level 70).

Infix "<" := trich_lt (at level 70).
Notation "x > y" := (trich_lt y x) (at level 70, only parsing).
Infix "≤" := trich_le (at level 30).
Notation "x >= y" := (trich_le y x) (at level 70, only parsing).

Lemma trich_lt_irrefl :
  forall {A : TrichDec} {x : A},
    ~ trich_lt x x.
Proof.
  intros A x H. eapply trich_lt_antisym; eassumption.
Qed.

Lemma trich_lt_connected :
  forall {A : TrichDec} {x y : A},
    ~ trich_lt x y -> ~ trich_lt y x -> x = y.
Proof.
  intros. destruct (cmp_spec x y).
    assumption.
    contradiction.
    contradiction.
Qed.

Lemma trich_lt_comparison :
  forall {A : TrichDec} {x z : A},
    trich_lt x z -> forall y : A, trich_lt x y \/ trich_lt y z.
Proof.
  intros. destruct (cmp_spec x y).
    subst. auto.
    auto.
    right. eapply trich_lt_trans; eassumption.
Qed.

(** comparison properties *)

Lemma cmp_spec1 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Lt <-> trich_lt x y.
Proof.
  intros. destruct (cmp_spec x y).
    subst. split.
      inv 1.
      intro. contradict H. apply trich_lt_irrefl.
    firstorder.
    split.
      inv 1.
      intro. contradict H. apply trich_lt_antisym. assumption.
Qed.

Lemma cmp_spec2 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Eq <-> x = y.
Proof.
  intros. destruct (cmp_spec x y).
    firstorder.
    split; inv 1. contradict H. apply trich_lt_irrefl.
    split; inv 1. contradict H. apply trich_lt_irrefl.
Qed.

Lemma cmp_spec3 :
  forall {A : TrichDec} (x y : A),
    cmp x y = Gt <-> trich_lt y x.
Proof.
  intros. destruct (cmp_spec x y);
  firstorder; try congruence.
    contradict H0. subst. apply trich_lt_irrefl.
    contradict H0. apply trich_lt_antisym. assumption.
Qed.

Lemma CompOpp_cmp :
  forall {A : TrichDec} {x y : A},
    CompOpp (x <?> y) = (y <?> x).
Proof.
  intros.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : ?x < ?y |- _ =>
          pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma cmp_refl :
  forall {A : TrichDec} (x : A),
    x <?> x = Eq.
Proof.
  intros.
  destruct (cmp_spec x x).
    reflexivity.
    apply trich_lt_irrefl in H. contradiction.
    apply trich_lt_irrefl in H. contradiction.
Qed.

Lemma trich_ltb_irrefl :
  forall {A : TrichDec} (x : A),
    x <? x = false.
Proof.
  intros.
  unfold trich_ltb.
  rewrite cmp_refl.
  reflexivity.
Qed.

Lemma negb_trich_ltb :
  forall {A : TrichDec} (x y : A),
    negb (x <? y) = x >=? y.
Proof.
  intros.
  unfold trich_ltb, trich_leb.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : _ < _ |- _ => pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma trich_leb_refl :
  forall {A : TrichDec} (x : A),
    x ≤? x = true.
Proof.
  intros.
  unfold trich_leb.
  rewrite cmp_refl.
  reflexivity.
Qed.

Lemma negb_trich_leb :
  forall {A : TrichDec} (x y : A),
    negb (x ≤? y) = x >? y.
Proof.
  intros.
  unfold trich_ltb, trich_leb.
  destruct (cmp_spec x y), (cmp_spec y x);
  cbn; subst; try reflexivity;
  match goal with
      | H : _ < _ |- _ => pose (trich_lt_antisym H); contradiction
  end.
Qed.

Lemma trich_eqb_refl :
  forall {A : TrichDec} (x : A),
    x =? x = true.
Proof.
  intros.
  unfold trich_eqb.
  rewrite cmp_refl.
  reflexivity.
Qed.

(* Newest lemmas *)

Lemma trichb_Gt_to_Lt :
  forall {A : TrichDec} {x y : A},
    x <?> y = Gt <-> y <?> x = Lt.
Proof.
  intros.
  rewrite ?cmp_spec1, <- ?cmp_spec3 in *.
  reflexivity.
Qed.

Lemma trichb_not_Gt_to_not_Lt :
  forall {A : TrichDec} {x y : A},
    x <?> y <> Gt <-> y <?> x <> Lt.
Proof.
  intros.
  rewrite ?cmp_spec1, <- ?cmp_spec3 in *.
  reflexivity.
Qed.

Lemma trichb_not_Lt_to_not_Gt :
  forall {A : TrichDec} {x y : A},
    x <?> y <> Lt <-> y <?> x <> Gt.
Proof.
  intros.
  rewrite ?cmp_spec1, <- ?cmp_spec3 in *.
  reflexivity.
Qed.

Lemma trichb_trans_Lt :
  forall {A : TrichDec} {x y z : A},
    x <?> y = Lt -> y <?> z = Lt -> x <?> z = Lt.
Proof.
  intros A x y z Hxy Hyz.
  rewrite cmp_spec1 in *.
  eapply trich_lt_trans; eassumption.
Qed.

Lemma trichb_trans_Gt_neq :
  forall {A : TrichDec} {x y z : A},
    x <?> y <> Gt -> y <?> z <> Gt -> x <?> z <> Gt.
Proof.
  intros A x y z Hxy Hyz.
  rewrite <- trichb_not_Lt_to_not_Gt in *.
  rewrite <- trichb_not_Lt_to_not_Gt in Hxy.
  rewrite <- trichb_not_Lt_to_not_Gt in Hyz.
Admitted.

Lemma trichb_trans_Lt_Gt :
  forall {A : TrichDec} {x y z : A},
    x <?> y = Lt -> y <?> z <> Gt -> x <?> z = Lt.
Proof.
  intros A x y z Hxy Hyz.
  destruct (cmp_spec y z); try congruence.
  rewrite <- cmp_spec1 in H.
  eapply trichb_trans_Lt; eassumption.
Qed.

Lemma trichb_trans_Gt_Lt :
  forall {A : TrichDec} {x y z : A},
    cmp x y <> Gt -> cmp y z = Lt -> cmp x z = Lt.
Proof.
  intros A x y z Hxy Hyz.
  destruct (cmp_spec x y); try congruence.
  rewrite <- cmp_spec1 in H.
  eapply trichb_trans_Lt; eassumption.
Qed.

(* Specs *)

Lemma trich_ltb_spec :
  forall {A : TrichDec} (x y : A),
    BoolSpec (x < y) (x >= y) (x <? y).
Proof.
  intros.
  unfold trich_ltb.
  destruct (cmp_spec x y); constructor.
    right. symmetry. assumption.
    assumption.
    left. assumption.
Qed.

Lemma trich_leb_spec :
  forall {A : TrichDec} (x y : A),
    BoolSpec (x ≤ y) (x > y) (x ≤? y).
Proof.
  intros.
  unfold trich_leb.
  destruct (cmp_spec x y); constructor.
    right. assumption.
    left. assumption.
    assumption.
Qed.

Lemma trich_eqb_spec :
  forall {A : TrichDec} (x y : A),
    BoolSpec (x = y) (x <> y) (x =? y).
Proof.
  intros.
  unfold trich_eqb.
  destruct (cmp_spec x y); constructor.
    assumption.
    inv 1. apply trich_lt_irrefl in H. assumption.
    inv 1. apply trich_lt_irrefl in H. assumption.
Qed.

Lemma trich_le_refl :
  forall {A : TrichDec} (x : A),
    x ≤ x.
Proof.
  intros. right. reflexivity.
Qed.

Lemma trich_le_antisym :
  forall {A : TrichDec} (x y : A),
    x ≤ y -> y ≤ x -> x = y.
Proof.
  destruct 1.
    destruct 1.
      contradict H. apply trich_lt_antisym. assumption.
      symmetry. assumption.
    intro. assumption.
Qed.

Lemma trich_le_antisym' :
  forall {A : TrichDec} {x y : A},
    x <?> y <> Gt -> y <?> x <> Gt -> x = y.
Proof.
  intros.
  rewrite cmp_spec3 in H.
  rewrite cmp_spec3 in H0.
  apply trich_lt_connected; assumption.
Qed.

Lemma trich_le_nf :
  forall {A : TrichDec} (x y : A),
    x ≤ y <-> cmp x y <> Gt.
Proof.
  split; intros.
    destruct (cmp_spec x y); subst.
      inv 1.
      inv 1.
      destruct H.
        apply trich_lt_antisym in H. contradiction.
        subst. apply trich_lt_irrefl in H0. contradiction.
    destruct (cmp_spec x y); subst.
      apply trich_le_refl.
      left. assumption.
      contradiction.
Qed.

Lemma trich_leb_true :
  forall {A : TrichDec} (x y : A),
    x ≤? y = true -> x ≤ y.
Proof.
  intros.
  unfold trich_leb in H.
  destruct (cmp_spec x y).
    right. assumption.
    left. assumption.
    congruence.
Qed.

Lemma trich_leb_false :
  forall {A : TrichDec} (x y : A),
    x ≤? y = false -> y < x.
Proof.
  intros.
  unfold trich_leb in H.
  destruct (cmp_spec x y).
    congruence.
    congruence.
    assumption.
Qed.

Lemma trich_ltb_true :
  forall {A : TrichDec} (x y : A),
    x <? y = true -> x < y.
Proof.
  intros.
  unfold trich_ltb in H.
  destruct (cmp_spec x y).
    congruence.
    assumption.
    congruence.
Qed.

Lemma trich_ltb_false :
  forall {A : TrichDec} (x y : A),
    x <? y = false -> y ≤ x.
Proof.
  intros.
  unfold trich_ltb in H.
  destruct (cmp_spec x y).
    right. symmetry. assumption.
    congruence.
    left. assumption.
Qed.

(* [min], [max] and [minmax] *)

Definition trich_min {A : TrichDec} (x y : A) : A :=
  if x ≤? y then x else y.

Definition trich_max {A : TrichDec} (x y : A) : A :=
  if y ≤? x then x else y.

Definition trich_minmax {A : TrichDec} (x y : A) : A * A :=
  if x ≤? y then (x, y) else (y, x).

Lemma trich_min_spec :
  forall {A : TrichDec} {x y a : A},
    trich_min x y = a ->
      a ≤ x /\ a ≤ y.
Proof.
Admitted.

Lemma trich_max_spec :
  forall {A : TrichDec} {x y a : A},
    trich_max x y = a ->
      x ≤ a /\ y ≤ a.
Proof.
Admitted.

(* Lemma trich_minmax_spec :
  forall {A : TrichDec} {x y a b : A},
    trich_minmax x y = (a, b) ->
      a ≤ x /\ a ≤ y /\ x ≤ b /\ y ≤ b.
Proof.
Admitted.
 *)

Lemma trich_minmax_spec :
  forall {A : TrichDec} {x y a b : A},
    trich_minmax x y = (a, b) ->
      x ≤ y /\ (a = x /\ b = y) \/
      x > y /\ (a = y /\ b = x).
Proof.
Admitted.

Lemma trich_neq_nf :
  forall {A : TrichDec} {x y : A},
    x <> y -> cmp x y <> Eq.
Proof.
  intros A x y H H'.
  rewrite cmp_spec2 in H'.
  contradiction.
Qed.

Ltac trichbody :=
match goal with
(* General contradictions *)
    | H : False |- _ => contradiction
    | H : ?x <> ?x |- _ => contradiction H; reflexivity
(* Easy contradictions from TrichDec properties *)
    | H : ?x < ?x |- _ => apply trich_lt_irrefl in H; contradiction
    | H : ?x < ?y, H' : ?y < ?x |- _ =>
        pose (trich_lt_antisym x y H); contradiction
(* Easy wins from properties of [trich_le] *)
    | |- ?x ≤ ?x => apply trich_le_refl
(* Deduce equality and substitute *)
    | H : _ <?> _ = Eq |- _ => rewrite cmp_spec2 in H; subst
    | H : ~ ?x < ?y, H' : ~ ?y < ?x |- _ =>
        pose (trich_lt_connected H H'); subst; clear H H'
    | Hxy : ?x ≤ ?y, Hyx : ?y ≤ ?x |- _ =>
        pose (trich_le_antisym Hxy Hyx); subst; clear Hxy Hyx
(* put stuff in normal form (i.e. cmp _ _ = _) *)
    | H : ?x < ?y |- _ =>
        rewrite <- ?cmp_spec1, <- ?cmp_spec3 in H
    | |- ?x < ?y =>
        rewrite <- ?cmp_spec1, <- ?cmp_spec3
    | H : ?x ≤ ?y |- _ => rewrite trich_le_nf in H
    | |- ?x ≤ ?y => rewrite trich_le_nf
    | H : ?x ≤? ?y = true |- _ => apply trich_leb_true in H
    | H : ?x ≤? ?y = false |- _ => apply trich_leb_false in H
    | H : ?x <? ?y = true |- _ => apply trich_ltb_true in H
    | H : ?x <? ?y = false |- _ => apply trich_ltb_false in H
    | |- _ <> _ => intro; subst
(* more normal forms *)
    | H1 : ?x <?> ?y = _, H2 : ?x <?> ?y <> _ |- _ => try contradiction; clear H2
(*     | H : _ <> _ |- _ => apply trich_neq_nf in H
    | H : _ = _ |- _ => subst + rewrite <- cmp_spec2 in H *)
(* Computational properties of cmp *)
    | H : ?x <?> ?x = _ |- _ =>
        rewrite cmp_refl in H; try congruence
    | H : ?x <?> ?x <> _ |- _ =>
        rewrite cmp_refl in H; try congruence
    | |- context [?x <?> ?x] =>
        rewrite cmp_refl
    | H : context [CompOpp (_ <?> _)] |- _ =>
        rewrite CompOpp_cmp in H
    | |- context [CompOpp (_ <?> _)] =>
        rewrite CompOpp_cmp
(* Computational properties of derived operations *)
    | H : context [negb (_ ≤? _)] |- _ => rewrite negb_trich_leb in H
    | |-  context [negb (_ ≤? _)]      => rewrite negb_trich_leb
    | H : context [negb (_ <? _)] |- _ => rewrite negb_trich_ltb in H
    | |-  context [negb (_ <? _)]      => rewrite negb_trich_ltb
    | H : context [?x <? ?x] |- _ =>
        rewrite trich_ltb_irrefl in H
    | |- context [?x <? ?x] =>
        rewrite trich_ltb_irrefl
    | H : context [?x ≤? ?x] |- _ =>
        rewrite trich_leb_refl in H
    | |- context [?x ≤? ?x] =>
        rewrite trich_leb_refl
    | H : context [?x =? ?x] |- _ =>
        rewrite trich_eqb_refl in H
    | |- context [?x =? ?x] =>
        rewrite trich_eqb_refl
(* Normalize the order of arguments. *)
    | H : _ <?> _  = Gt |- _ => rewrite trichb_Gt_to_Lt in H
    | |-  _ <?> _  = Gt      => rewrite trichb_Gt_to_Lt
    | H : _ <?> _ <> Lt |- _ => rewrite <- trichb_not_Gt_to_not_Lt in H
    | |-  _ <?> _ <> Lt      => rewrite <- trichb_not_Gt_to_not_Lt
(* Antisymmetry *)
    | Hxy : ?x <?> ?y <> Gt, Hyx : ?y <?> ?x <> Gt |- _ =>
        let H := fresh "H" in
          pose (H := trich_le_antisym' Hxy Hyx); clearbody H; clear Hxy Hyx; subst
(* Transitivity *)
     | Hxy : ?x <?> ?y = Lt, Hyz : ?y <?> ?z = Lt |- _ =>
        lazymatch goal with
            | Hxz : x <?> z = Lt |- _ => fail
            | _ =>
                let Hxz := fresh "Hxz" in
                pose (Hxz := trichb_trans_Lt Hxy Hyz); clearbody Hxz
        end
    | Hxy : ?x <?> ?y <> Gt, Hyz : ?y <?> ?z <> Gt |- _ =>
        lazymatch goal with
            | Hxz : x <?> z <> Gt |- _ => fail
            | Hxz : x <?> z =  _  |- _ => fail
            | _ => constr_eq x z
                     ||
                   let Hxz := fresh "Hxz" in
                   pose (Hxz := trichb_trans_Gt_neq Hxy Hyz); clearbody Hxz
        end
    | Hxy : ?x <?> ?y = Lt, Hyz : ?y <?> ?z <> Gt |- _ =>
        lazymatch goal with
            | Hxz : x <?> z = Lt |- _ => fail
            | _ => 
                let Hxz := fresh "Hxz" in
                pose (Hxz := trichb_trans_Lt_Gt Hxy Hyz); clearbody Hxz
        end
    | Hxy : ?x <?> ?y <> Gt, Hyz : ?y <?> ?z = Lt |- _ =>
        lazymatch goal with
            | Hxz : x <?> z = Lt |- _ => fail
            | _ =>
                let Hxz := fresh "Hxz" in
                pose (Hxz := trichb_trans_Gt_Lt Hxy Hyz); clearbody Hxz
        end
(* Case analysis *)
(* <? *)
    | |- context [match ?x <? ?y with | _ => _ end] =>
        destruct (trich_ltb_spec x y); subst
    | H : context [match ?x <? ?y with | _ => _ end] |- _ =>
        destruct (trich_ltb_spec x y); subst
(* ≤? *)
    | |- context [match ?x ≤? ?y with | _ => _ end] =>
        destruct (trich_leb_spec x y); subst
    | H : context [match ?x ≤? ?y with | _ => _ end] |- _ =>
        destruct (trich_leb_spec x y); subst
(* =? *)
    | |- context [match ?x =? ?y with | _ => _ end] =>
        destruct (trich_eqb_spec x y); subst
    | H : context [?x =? ?y] |- _ =>
        destruct (trich_eqb_spec x y); subst
(* <?> *)
    | H : context [match ?x <?> ?y with | _ => _ end] |- _ =>
        destruct (cmp_spec x y)
    | |- context [match ?x <?> ?y with | _ => _ end] =>
        destruct (cmp_spec x y)
(* [min], [max] and [minmax] *)
    | H : trich_min _ _    = _      |- _ => apply trich_min_spec in H; destruct H
    | H : trich_max _ _    = _      |- _ => apply trich_max_spec in H; destruct H
    | H : trich_minmax _ _ = (_, _) |- _ => apply trich_minmax_spec in H; decompose [and or] H; clear H 
(* try to finish somehow *)
    | _ => subst; auto; try (cbn in *; congruence)
end.

Ltac trich :=
  cbn; repeat trichbody; subst; auto; try congruence.

Ltac trich_aggresive :=
repeat match goal with
    | H : context [?x <?> ?y] |- _ => destruct (cmp_spec x y); subst
    | |- context [?x <?> ?y] => destruct (cmp_spec x y); subst
end.

Ltac trich' := trich; try (trich_aggresive; trich; fail).

Fixpoint cmp_nat (n m : nat) : comparison :=
match n, m with
    | 0, 0 => Eq
    | 0, _ => Lt
    | _, 0 => Gt
    | S n', S m' => cmp_nat n' m'
end.

#[refine]
Instance natlt : TrichDec :=
{
    carrier := nat;
    trich_lt := Peano.lt;
    cmp := cmp_nat
}.
Proof.
  1-2: intros; lia.
  induction x as [| x']; destruct y as [| y']; cbn.
    1-3: constructor; lia.
    destruct (IHx' y'); constructor; lia.
Defined.


Definition testl := [3; 0; 1; 42; 34; 19; 44; 21; 42; 65; 5].