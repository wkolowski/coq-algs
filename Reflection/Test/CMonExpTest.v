Require Import CMonRefl2.

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

(* Other tests. *)
Goal op a (op (op b c) (op d (op (op e e) d))) =
     op (op a d) (op d (op c (op e (op e b)))).
Proof. cmon_simpl. reflexivity. Qed.

End Test.