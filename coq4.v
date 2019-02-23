Definition prod_ind (A B:Set) (P:prod A B -> Prop) :=
 fun (f : forall a b, P (pair a b)) =>
 fun p => match p as x return P x with pair a b => f a b end. 

Check prod_ind.
(* : forall (A B : Set) (P : A * B -> Prop),
  (forall (a : A) (b : B), P (a, b)) -> forall p : A * B, P p   *)


Definition sum_ind (A B:Set) (P:sum A B -> Prop) :=
fun (fl : forall a, P (inl _ a)) (fr : forall b, P (inr _ b)) =>
fun p => match p as x return P x
with inl a => fl a | inr b => fr b end.

Check sum_ind.
(*: forall (A B : Set) (P : A + B -> Prop),
   (forall a : A, P (inl B a)) -> (forall b : B, P (inr A b)) ->
   forall p : A + B, P p *)

Fixpoint nat_ind (P:nat -> Prop) (f0:P O) (fn:forall n, P n -> P (S n))
(n : nat) {struct n} :=
match n as x return P x
with O => f0 | S m => fn m (nat_ind P f0 fn m) end.

Check nat_ind.
(* : forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) ->
   forall n : nat, P n  *)

(*
前回ならった induction n という作戦はこの補題を利用するが，作業がかなり複雑である．
1. n を含む全ての仮定をゴールに戻す．(作戦 revert H1 ... Hn でも手動でできる)
2. n の型を見て，型が t a1 . . . an ならば，apply (t ind a1 . . . an) を行う．(このステップは作戦 elim n でもできる)
厳密には，ゴールのソートによって t rec, t ind, t rect のいずれかが使われる．
3. 新しくできた各ゴールに対して，仮定をおく．(intros にあたる)
destruct と induction/elim はよく似ているが，後者が生成された補題を利用しているので，
効果が違ったりする．
*)

Lemma plus_0 : forall n, plus n 0 = n.
Proof.
  apply nat_ind. reflexivity.
  intros n IHn.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.


(* 偶数の定義 *)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

(* 帰納的述語を証明する定理 *)
Theorem even_double : forall n, even (n + n).
Proof.
  induction n.
  apply even_O.
  simpl.
  rewrite <- plus_n_Sm.
  apply even_SS.
  assumption.
Qed.

(* 帰納的述語に対する帰納法もできる *)
Theorem even_plus : forall m n, even m -> even n -> even (m + n).
Proof.
  intros m n Hm Hn.
  induction Hm.
  apply Hn.
  simpl.
  apply even_SS.
  assumption.
Qed.

(*
実は Coq の論理結合子のほとんどが帰納的述語として定義されている．
Inductive and (A B : Prop) : Prop := conj : A -> B -> A /\ B.
Inductive or (A B : Prop) : Prop :=
 or_introl : A -> A \/ B | or_intror : B -> A \/ B.
*)

(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
 ex_intro : forall x : A, P x -> exists x, P x.

Inductive False : Prop := .
 *)

(*
and、or や ex について destruct が使えた理由がこの定義方法である．
しかも，False は最初からあるものではなく，構成子のない述語として定義されている．生成
される帰納法の補題をみると面白い．
*)

Print False_rect.
(* fun (P : Type) (f : False) => match f return P with end
   : forall P : Type, False -> P     *)

(* ちょうど，矛盾の規則に対応している．作戦　 elim でそれが使える．  *)

Theorem contradict : forall (P Q : Prop),
P -> ~P -> Q.
Proof.
  intros P Q p np.
  elim np.
  assumption.
Qed.

(* 練習問題 2.1 以下の定理を証明せよ． *)
Module Ex4_1.
Inductive odd : nat -> Prop :=
| odd_1 : odd 1
| odd_SS : forall n, odd n -> odd (S (S n)).

Theorem even_odd : forall n, even n -> odd (S n).
Proof.
Admitted.

Theorem odd_even : forall n, odd n -> even (S n).
Proof.
Admitted.

Theorem even_not_odd : forall n, even n -> ~odd n.
Proof.
Admitted.

Theorem even_or_odd : forall m, even m \/ odd m.
Proof.
Admitted.

Theorem odd_odd_even : forall m n, odd m -> odd n -> even (m+n).
Proof.
Admitted.

End Ex4_1.



Fixpoint vec (n:nat) (T:Set) :=
match n with
| 0 => unit
| S m => (vec m T * T)%type
end.

Check ((tt, 1, 2, 3) : vec 3 nat).

(*
この中で特に S = Set または S = Prop の場合を多相的という。関数や定理が任意のデータ型
または任意の命題について定義される。
標準ライブラリのリスト 典型的な多相的なデータ構造として、リストが挙げられる。
*)


Require Import List.

Module Lists.

Print list.
(* Inductive list (A : Type) : Type := (* 型引数がある *)
   nil : list A | cons : A -> list A -> list A   *)

Definition l1 := 1 :: 2 :: 3 :: 4 :: nil. (* cons は :: と書ける *)
Print l1.
(* l1 = 1 :: 2 :: 3 :: 4 :: nil
   : list nat   *)

(*
Definition hd {A:Set} (l:list A) := (* { } で A が省略可能になる *)
match l with
| cons a _ => a
end. *)
(* Error: Non exhaustive pattern-matching: no clause found for pattern nil *)

Definition hd {A:Set} (d:A) (l:list A) :=
match l with
| cons a _ => a
| nil => d (* nil のときは d を返す *)
end.

Eval compute in hd 0 l1.
(* = 1
   : nat   *)

Fixpoint length {A:Set} (l : list A) := (* 長さ *)
match l with
| nil => 0
| cons _ l' => 1 + length l'
end.

Eval compute in length l1.
(* = 4
   : nat  *)

Fixpoint append {A:Set} (l1 l2:list A) : list A := (* 結合 *)
match l1 with
| nil => l2
| a :: l' => a :: append l' l2
end.

Eval compute in append (1 :: 2 :: nil) (3 :: 4 :: nil).
(* = 1 :: 2 :: 3 :: 4 :: nil
   : list nat  *)

Fixpoint fold_right {A B:Set} (f : A -> B -> B) (z : B) (l : list A) :=
match l with
| nil => z
| a :: l' => f a (fold_right f z l')
end.

(* fold_right ? b (a1 :: . . . :: an) = a1 ? . . . ? an ? b *)

Definition sum := fold_right plus 0.
Eval compute in sum l1.
(* = 10
   : nat  *)

Eval compute in fold_right mult 1 l1.
(* = 24
   : nat *)

End Lists.

(* 練習問題 3.1 多項式を係数のリストとして定義する。Z 上の多項式をある点 x で計算する関数を定義せよ。 *)

Module Ex4_2.

Require Import ZArith.
Open Scope Z_scope.

Fixpoint eval_poly (p : list Z) (x : Z) := ...
 Eval compute in eval_poly (1 :: 2 :: 3 :: nil) 5. (* = 1 + 2*5 + 3*5*5 *)

End Ex4_2.

(* 多相性と論理 Coq の論理演算子は Inductive で定義されているが、実は多相的な論理式として定義できる。*)

Definition and’ (P Q : Prop) := forall (X : Prop), (P -> Q -> X) -> X.
Definition or’ (P Q : Prop) := forall (X : Prop), (P -> X) -> (Q -> X) -> X.
Definition False’ := forall (X : Prop), X.
Definition Equal’ (T : Type) (x y : T) := forall (P : T -> Prop), P x <-> P y.

Theorem and’_ok : forall P Q, and’ P Q <-> P /\ Q.
Proof.
  split.
  intros.
  apply H.
  split; assumption.
  intros pq X pqx.
  destruct pq as [p q].
  apply pqx; assumption.
Qed.

Theorem or’_ok : forall P Q, or’ P Q <-> P \/ Q.

Theorem False’_ok : False’ <-> False.

Theorem Equal’_ok : forall T x y, Equal’ T x y <-> x = y.

(* 練習問題 3.2 or’ ok、False’ ok および Equal’ ok を証明せよ *)

