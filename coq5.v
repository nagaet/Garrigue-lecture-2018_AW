(* 2 単一化と自動化 *)

Require Import Arith.

Goal forall x, 1 + x = x + 1. (* Goal で名前のない定理を証明する *)
  intros.
   (* 1 + x = x + 1 *)
  Check plus_comm.
   (* : forall n m : nat, n + m = m + n *)
  apply plus_comm.
Abort. (* 定理を登録せずに証明を終わらせる *)


Goal forall x y z, x + y + z = z + y + x.
  intros.
  Check eq_trans.
   (*  : forall (A : Type) (x y z : A), x = y -> y = z -> x = z *)
  (* apply eq_trans.
     Error: Unable to find an instance for the variable y.  *)
  eapply eq_trans. (* y が結論に現れないので，eapply に変える *)
  (* x + y + z = ?13 *)
  apply plus_comm.
  eapply eq_trans.
  Check f_equal.
  (*: forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y *)
  apply f_equal. (* ?f = plus z *)
  apply plus_comm.
  apply plus_assoc.
  Restart. (* 証明を元に戻す *)
  intros.
  rewrite plus_comm. (* rewrite も単一化を使う *)
  rewrite (plus_comm x).
  apply plus_assoc.
Abort.


Goal
(forall P : nat -> Prop,
P 0 -> (forall n, P n -> P (S n)) -> forall n, P n)
-> forall n, n + 1 = 1 + n.
  intros H n. (* 全ての変数を intro する *)
  apply H.
  Restart.
  intros H n.
  pattern n. (* pattern で正しい述語を構成する *)
  apply H.
  Restart.
  intros H. (* forall n を残すとうまくいく *)
  apply H.
Abort.


(* 練習問題 2.1 以下の補題を証明せよ。 *)
Section Coq5.

Require Import List.

Variable A : Set.
Variable op : A -> A -> A.
Variable e : A.

Hypothesis op_comm : forall x y, op x y = op y x.
Hypothesis op_assoc : forall x y z, op x (op y z) = op (op x y) z.
Hypothesis op_neutral : forall x, op e x = x.

Fixpoint reduce (l : list A) : A :=
match l with
| nil => e
| a :: l' => op a (reduce l')
end.

Lemma reduce_fold : forall l, reduce l = fold_right op e l.
Proof.
Admitted.

Lemma reduce_app : forall l1 l2, reduce (l1 ++ l2) = op (reduce l1) (reduce l2).
Proof.
Admitted.

End Coq5.
