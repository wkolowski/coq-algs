From CoqAlgs Require Import CMonRefl.

Section Test.

Variable (X : CMon) (a a' b b' c c' d e f : X).
Variable P Q R S : Prop.

Goal a = a.
Proof. solveGoal. Qed.

Goal a = b -> b = a.
Proof. solveGoal. Qed.

Goal a = b -> b = c -> a = c.
Proof. solveGoal. Abort.

Goal b = c -> a = b -> a = c.
Proof. solveGoal. Qed.

Goal b = b' -> op a (op b c) = op (op a b') c.
Proof. solveGoal. solveGoal. Qed.

Goal op a b = op a b' -> op (op a b) c = op b' (op a c).
Proof.
  cmon_simpl. rewrite ?assoc. rewrite (comm b').
  rewrite <- !H. cmon_simpl. reflexivity.
Qed.

Goal a = b -> b = c -> c = a -> op b (op a c) = op a (op neutr (op b c)).
Proof. cmon_simpl. reflexivity. Qed.

End Test.