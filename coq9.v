
(* 例 *)
Require Import ssreflect.

Section Koushin.

Variables P Q : Prop.

Theorem modus_ponens : P -> (P -> Q) -> Q.
Proof.
  by move=> p; apply.
Qed.

Theorem DeMorgan : ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  move=> npq.
  by split=> [p|q]; apply npq; [left | right].
Qed.

Theorem and_comm : P /\ Q -> Q /\ P.
Proof.
  by move=> [p q]; split.
Qed.

End Koushin.

Module Plus.

Lemma plus_assoc m n p : m + (n + p) = (m + n) + p.
Proof.
elim: m => [|m IHm] //=.
by rewrite IHm.
Qed.
End Plus.

(* 3 MathComp のライブラリ
先週は ssreflect のコマンドを見たが、MathComp の本当の強さはそのライブラリにある。その
大きな特徴は書き換えを証明の基本手法とすること。
ライブラリは ssreflect, fingroup, algebra 等、いくつかのの部分からできている。前者は
一般的なデータ構造で、後者は代数系の証明に使う。

基本データ
まず、ssreflect を読み込む。それほど多くはない。*)

From mathcomp Require Import
     ssreflect ssrbool ssrnat ssrfun seq eqtype choice fintype.
(*
ssrbool は論理式と述語の扱い。ssrnat は自然数。ssrfun は関数 (写像) の様々な性質。seq はリスト。eqtype, choice, fintype はそれぞれ等価性、選択、有限性が使えるデータ構造のた
めの枠組みを提供している。例えば、自然数の等価性は判定できるので、排中律を仮定しなくて
も場合分けができる。
中身について、ファイルを参照するしかないが、まず ssrnat の例をみよう。(ちなみに、ソー
スファイルはは~/.local/share/coq/mathcomp/ssreflect の下にある) *)
Module Test_ssrnat.
Fixpoint sum n := if n is m.+1 then n + sum m else 0.

Theorem sum_square n : 2 * sum n = n * n.+1.
Proof.
  elim: n => [|n IHn] /=.
  done.
  rewrite mulnDr.
  rewrite -[n.+2]addn2 mulnDr.
  rewrite [n.+1*n]mulnC -IHn.
  by rewrite addnC (mulnC _ 2).
Qed.
End Test_ssrnat.

(* 自己反映
論理式も書き換えで処理したい。そのために、ssrbool では論理演算子を型 bool の上の演算子として定義している。例えば、/\ は&&, \/ は||になる。二つの定義の間に行き来するために、
reflect という自己反映を表した宣言を使う。それが SSReflect の名前の由来である。 *)
Print reflect.
Inductive reflect (P : Prop) : bool -> Set :=
ReflectT : P -> reflect P true | ReflectF : ~ P -> reflect P false.
Check orP.
(* orP : forall b1 b2 : bool, reflect (b1 b2) (b1 || b2) *)

(* 表現の切り替えはビュー機構によって行われる。前に見た適用パターンを使う。move, case,
apply などの直後に/view を付けると、対処が可能な方向に変換される。=>の右でも使える。な
お、ビューとしては上の reflect 型 だででなく、同値関係 (P <-> Q) や普通の定理 (P -> Q) も使える。 *)
Module Test_ssrbool.
Variables a b c : bool.
Print andb.

Lemma andb_intro : a -> b -> a && b.
Proof.
  move=> a b.
  rewrite a.
  move=> /=.
  done.
  Restart.
  by move ->.
Qed.

Lemma andbC : a && b -> b && a.
Proof.
  case: a => /=.
  by rewrite andbT.
  done.
  Restart.
  by case: a => //= ->.
  Restart.
  by case: a; case: b.
Qed.

Lemma orbC : a || b -> b || a.
Proof.
  case: a => /=.
  by rewrite orbT.
  by rewrite orbF.
  Restart.
  move/orP => H.
  apply/orP.
  move: H => [Ha|Hb].
  by right.
  by left.
  Restart.
  by case: a; case: b.
Qed.

Lemma test_if x : if x == 3 then x*x == 9 else x !=3.
Proof.
  case Hx: (x == 3).
  by rewrite (eqP Hx).
  done.
  Restart.
  case: ifP.
  by move/eqP ->.
  move/negbT. done.
Qed.
End Test_ssrbool.

(* 自己反映があると自然数の証明もスムーズになる。*)
Theorem avg_prod2 m n p : m+n = p+p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  have Hp0 q: p <= q -> p-q = 0.
  by rewrite -subn_eq0 => /eqP.
  suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
  + by rewrite (Hp0 m).
  + by rewrite (Hp0 n).
  case: (leqP p m) => Hpm //=.
  case: (leqP p n) => Hpn //=.
  suff: m + n < p + p.
  by rewrite Hmn ltnn.
  by rewrite -addnS leq_add // ltnW.
Qed.

(* 数学関係の定理
こちらはモジュールが多過ぎて、簡単に紹介できる。よく使うもおとして、finset(fintype に基いた有限集合、基本的な線形代数は matrix、perm や vector、多項式は poly、素数は prime。*)

(* 練習問題 3.1 今までの課題を SSReflect の構文を使って書き換えてみる。 *)

