Require Import RCCBase.
Require Import FunctionalExtensionality.

Ltac ext H := apply functional_extensionality; intro H.

Inductive Finger (A : Type) : Type :=
    | F1 : A -> Finger A
    | F2 : A -> A -> Finger A
    | F3 : A -> A -> A -> Finger A
    | F4 : A -> A -> A -> A -> Finger A.

Arguments F1 {A} _.
Arguments F2 {A} _ _.
Arguments F3 {A} _ _ _.
Arguments F4 {A} _ _ _ _.

Inductive Node (A : Type) : Type :=
    | N2 : A -> A -> Node A
    | N3 : A -> A -> A -> Node A.

Arguments N2 {A} _ _.
Arguments N3 {A} _ _ _.

Inductive FingerTree (A : Type) : Type :=
    | Empty  : FingerTree A
    | Single : A -> FingerTree A
    | Deep   : Finger A -> FingerTree (Node A) -> Finger A -> FingerTree A.

Arguments Empty  {A}.
Arguments Single {A} _.
Arguments Deep   {A} _ _ _.

Function cons {A : Type} (x : A) (t : FingerTree A) : FingerTree A :=
match t with
    | Empty      => Single x
    | Single a   => Deep (F1 x) Empty (F1 a)
    | Deep l m r =>
        match l with
            | F1 a       => Deep (F2 x a)     m                   r
            | F2 a b     => Deep (F3 x a b)   m                   r
            | F3 a b c   => Deep (F4 x a b c) m                   r
            | F4 a b c d => Deep (F2 x a)     (cons (N3 b c d) m) r
        end
end.

Function snoc {A : Type} (t : FingerTree A) (x : A) : FingerTree A :=
match t with
    | Empty      => Single x
    | Single a   => Deep (F1 a) Empty (F1 x)
    | Deep l m r =>
        match r with
            | F1 a       => Deep l m                   (F2 a x)
            | F2 a b     => Deep l m                   (F3 a b x)
            | F3 a b c   => Deep l m                   (F4 a b c x)
            | F4 a b c d => Deep l (snoc m (N3 a b c)) (F2 d x)
        end
end.

Function nodes {A : Type} (f1 f2 : Finger A) : Finger (Node A) :=
match f1, f2 with
    | F1 a      , F1 a'          => F1 (N2 a a'   )
    | F1 a      , F2 a' b'       => F1 (N3 a a' b')
    | F1 a      , F3 a' b' c'    => F2 (N2 a a'   ) (N2 b' c'   )
    | F1 a      , F4 a' b' c' d' => F2 (N3 a a' b') (N2 c' d'   )
    | F2 a b    , F1 a'          => F1 (N3 a b a' )
    | F2 a b    , F2 a' b'       => F2 (N2 a b    ) (N2 a' b'   )
    | F2 a b    , F3 a' b' c'    => F2 (N3 a b a' ) (N2 b' c'   )
    | F2 a b    , F4 a' b' c' d' => F2 (N3 a b a' ) (N3 b' c' d')
    | F3 a b c  , F1 a'          => F2 (N2 a b    ) (N2 c a'    )
    | F3 a b c  , F2 a' b'       => F2 (N3 a b c  ) (N2 a' b'   )
    | F3 a b c  , F3 a' b' c'    => F2 (N3 a b c  ) (N3 a' b' c')
    | F3 a b c  , F4 a' b' c' d' => F3 (N3 a b c  ) (N2 a' b'   ) (N2 c' d')
    | F4 a b c d, F1 a'          => F2 (N3 a b c  ) (N2 d a'    )
    | F4 a b c d, F2 a' b'       => F2 (N3 a b c  ) (N3 d a' b' )
    | F4 a b c d, F3 a' b' c'    => F3 (N3 a b c  ) (N2 d a'    ) (N2 b' c')
    | F4 a b c d, F4 a' b' c' d' => F3 (N3 a b c  ) (N3 d a' b' ) (N2 c' d')
end.

Function app3 {A : Type} (t1 : FingerTree A) (f1 f2 : Finger A) (t2 : FingerTree A) : FingerTree A :=
match t1, t2 with
    | Empty        , _             => t2
    | _            , Empty         => t1
    | Single a     , _             => cons a t2
    | _            , Single a      => snoc t1 a
    | Deep l1 m1 r1, Deep l2 m2 r2 => Deep l1 (app3 m1 (nodes r1 f1) (nodes f2 l2) m2) r2
end.

(* Function app {A : Type} (t1 t2 : FingerTree A) : FingerTree A :=
match t1, t2 with
    | Empty        , _             => t2
    | _            , Empty         => t1
    | Single a     , _             => cons a t2
    | _            , Single a      => snoc t1 a
    | Deep l1 m1 r1, Deep l2 m2 r2 => Deep l1 (app3 m1 r1 l2 m2) r2
end. *)

Function nodes' {A : Type} (l : list A) : list (Node A) :=
match l with
    | [] => []
    | [_] => []
    | [a; b] => [N2 a b]
    | [a; b; c] => [N3 a b c]
    | [a; b; c; d] => [N2 a b; N2 c d]
    | a :: b :: c :: l' => N3 a b c :: nodes' l'
end.

Function app3' {A : Type} (t1 : FingerTree A) (xs : list A) (t2 : FingerTree A) : FingerTree A :=
match t1, t2 with
    | Empty        , _             => t2
    | _            , Empty         => t1
    | Single a     , _             => cons a t2
    | _            , Single a      => snoc t1 a
    | Deep l1 m1 r1, Deep l2 m2 r2 => Deep l1 (app3' m1 (nodes' xs) m2) r2
end.

Definition fingerToList {A : Type} (f : Finger A) : list A :=
match f with
    | F1 a       => [a]
    | F2 a b     => [a; b]
    | F3 a b c   => [a; b; c]
    | F4 a b c d => [a; b; c; d]
end.

Function flatten {A : Type} (l : list (Node A)) : list A :=
match l with
    | []             => []
    | N2 a b   :: l' => a :: b :: flatten l'
    | N3 a b c :: l' => a :: b :: c :: flatten l'
end.

Function toList {A : Type} (t : FingerTree A) : list A :=
match t with
    | Empty      => []
    | Single a   => [a]
    | Deep l m r => fingerToList l ++ flatten (toList m) ++ fingerToList r
end.

Function fromList {A : Type} (l : list A) : FingerTree A :=
match l with
    | []     => Empty
    | h :: t => cons h (fromList t)
end.

Definition mapFinger {A B : Type} (f : A -> B) (t : Finger A) : Finger B :=
match t with
    | F1 a       => F1 (f a)
    | F2 a b     => F2 (f a) (f b)
    | F3 a b c   => F3 (f a) (f b) (f c)
    | F4 a b c d => F4 (f a) (f b) (f c) (f d)
end.

Definition mapNode {A B : Type} (f : A -> B) (n : Node A) : Node B :=
match n with
    | N2 a b   => N2 (f a) (f b)
    | N3 a b c => N3 (f a) (f b) (f c)
end.

Function map {A B : Type} (f : A -> B) (t : FingerTree A) : FingerTree B :=
match t with
    | Empty      => Empty
    | Single a   => Single (f a)
    | Deep l m r => Deep (mapFinger f l) (map (mapNode f) m) (mapFinger f r)
end.

Definition revFinger {A : Type} (f : Finger A) : Finger A :=
match f with
    | F1 a       => F1 a
    | F2 a b     => F2 b a
    | F3 a b c   => F3 c b a
    | F4 a b c d => F4 d c b a
end.

Definition revNode {A : Type} (n : Node A) : Node A :=
match n with
    | N2 a b   => N2 b a
    | N3 a b c => N3 c b a
end.

Function rev {A : Type} (t : FingerTree A) : FingerTree A :=
match t with
    | Empty      => Empty
    | Single a   => Single a
    | Deep l m r => Deep (revFinger r) (map revNode (rev m)) (revFinger l)
end.

Lemma toList_cons :
  forall {A : Type} (h : A) (t : FingerTree A),
    toList (cons h t) = h :: toList t.
Proof.
  intros.
  functional induction cons h t;
  cbn; rewrite ?IHf; cbn;
  reflexivity.
Qed.

Lemma toList_fromList :
  forall {A : Type} (l : list A),
    toList (fromList l) = l.
Proof.
  induction l as [| h t]; cbn.
    reflexivity.
    rewrite toList_cons, IHt. reflexivity.
Qed.

Lemma mapFinger_mapFinger :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : Finger A),
    mapFinger g (mapFinger f t) = mapFinger (fun x => g (f x)) t.
Proof.
  destruct t; cbn; reflexivity.
Qed.

Lemma mapNode_mapNode :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (n : Node A),
    mapNode g (mapNode f n) = mapNode (fun x => g (f x)) n.
Proof.
  destruct n; cbn; reflexivity.
Qed.

Lemma mapNode_mapNode' :
  forall {A B C : Type} (f : A -> B) (g : B -> C),
    (fun x => mapNode g (mapNode f x)) = mapNode (fun x => g (f x)).
Proof.
  intros. ext n. apply mapNode_mapNode.
Qed.

Lemma map_map :
  forall {A B C : Type} (f : A -> B) (g : B -> C) (t : FingerTree A),
    map g (map f t) = map (fun x => g (f x)) t.
Proof.
  intros until t. revert C g.
  functional induction map f t;
  cbn; intros.
    1-2: reflexivity.
    rewrite IHf0, !mapFinger_mapFinger, mapNode_mapNode'. reflexivity.
Qed.

Lemma mapFinger_revFinger :
  forall {A B : Type} (f : A -> B) (t : Finger A),
    mapFinger f (revFinger t) = revFinger (mapFinger f t).
Proof.
  destruct t; reflexivity.
Qed.

Lemma mapNode_revNode :
  forall {A B : Type} (f : A -> B) (n : Node A),
    mapNode f (revNode n) = revNode (mapNode f n).
Proof.
  destruct n; reflexivity.
Qed.

Lemma map_rev :
  forall {A B : Type} (f : A -> B) (t : FingerTree A),
    map f (rev t) = rev (map f t).
Proof.
  intros. revert B f.
  functional induction rev t;
  cbn; intros.
    1-2: reflexivity.
    rewrite !mapFinger_revFinger, <- IHf, !map_map. do 2 f_equal.
      ext n. apply mapNode_revNode.
Qed.