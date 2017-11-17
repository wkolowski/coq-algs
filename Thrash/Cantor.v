Theorem diagonal : forall (X T : Set) (f : T -> T -> X),
    (forall g : T -> X, exists t : T, forall x : T, g x = f x t) ->
    forall α : X -> X, exists x : X, α x = x.
Proof.
  intros. pose (g := fun x : T => α (f x x)).
  specialize (H g). destruct H as [x H]. exists (f x x).
  unfold g in *. rewrite H. trivial.
Qed.

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall x x' : A, f x = f x' -> x = x'.

Theorem nat_natnat :
  ~ exists f : (nat -> nat) -> nat, injective f.
Proof.
  intro. destruct H as [f inj]. red in inj.
Abort.

Definition surjective {A B : Type} (f : A -> B) : Prop :=
  forall b : B, exists a : A, f a = b.

Theorem natnat_nat :
  ~ exists f : nat -> (nat -> nat), surjective f.
Proof.
  destruct 1 as [f sur]. red in sur.
  pose (f' := fun i : nat =>  S (f i i)).
  assert (forall i : nat, f i <> f').
    do 2 intro. assert (f i i = f' i) by (rewrite H; auto).
      unfold f' in *. induction (f i i); inversion H0; auto.
    destruct (sur f'). specialize (H x). contradiction.
Qed.

Definition infinite (A : Type) : Prop :=
    exists f : nat -> A, injective f.

Definition dedekind_inf (A : Type) : Prop :=
    exists (P : A -> Prop) (a : A), ~ P a /\
    exists f : A -> A,
      (forall a : A, P (f a)) /\
      (forall x y : A, f x = f y -> x = y) /\
      (forall y : A, P y -> exists x : A, y = f x).

Theorem infinite_dedekind_if : forall (A : Type),
  infinite A -> dedekind_inf A.
Proof.
  unfold infinite, injective, dedekind_inf. intros.
  destruct H as [f inj]. pose (g := fun n : nat => f (S n)).
  exists (fun y : A => exists n : nat, y = g n).
  exists (f 0). repeat split.
    destruct 1 as [n Hn]. unfold g in Hn.
      specialize (inj _ _ Hn). inversion inj.
    exists (fun x : A => x). repeat split; intros.
      Focus 2. assumption.
      Focus 2. exists y. auto.
Abort.