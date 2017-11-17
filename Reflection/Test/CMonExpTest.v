Add Rec LoadPath "/home/zeimer/Code/Coq".

Require Import CMonRefl.

Section Test.

Variable (X : CMon) (a a' b b' c c' d e f : X).

(* [CMon] axioms. *)
Goal op a (op b c) = op (op a b) c.
Proof. cmon_simpl. reflexivity. Qed.

Goal op neutr a = a.
Proof. cmon_simpl. reflexivity. Qed.

Goal op a neutr = a.
Proof. cmon_simpl. reflexivity. Qed.

Goal op a b = op b a.
Proof. cmon_simpl. reflexivity. Qed.

Goal op a (op (op b c) (op d (op (op e e) d))) =
     op (op a d) (op d (op c (op e (op e b)))).
Proof. cmon_simpl. reflexivity. Qed.

(* Other tests. *)
Goal b = b' -> op a (op b c) = op (op a b') c.
Proof. solveGoal. Qed.

Goal op a b = op a b' -> op (op a b) c = op b' (op a c).
Proof.
  cmon_simpl. rewrite ?assoc. rewrite (comm b').
  rewrite <- !H. cmon_simpl. reflexivity.
Qed.

Goal a = b -> b = c -> c = a -> op b (op a c) = op a (op neutr (op b c)).
Proof. cmon_simpl. reflexivity. Qed.

End Test.