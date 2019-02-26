(* 4 Coq で定理の証明 *)

(* 
前述の Curry-Howard 同型のおかげで，Coq の中で直接に命題を書くことができる．その型を
満すプログラムが見付かれば，定理になる．
*)

(*
変数宣言 まずは，準備として論理変数の宣言を行う．Section というコマンドを使うと，局所
的な論理変数が宣言できるようになる．宣言自体は Variables コマンドを使う．そして，宣言範
囲が終ると End コマンドでセクションを閉じる．
*)

Section Koushin.
Variables P Q : Prop.
(* P is assumed *)
(* Q is assumed *)

(*
論理式自身は型であると先に説明したが，通常の型の型だった Set と異なり，論理式の型は Prop
になる．普段はあまり影響はないが，区別すると便利なことができる．
*)


(* 命題と証明プログラム *)

(*
まず，前の二つの恒真式を証明してみよう．
2 つ目は関数適用だけなので，簡単にできる．
*)

Theorem modus_ponens : P -> (P -> Q) -> Q. (* 名前を付けなければならない *)
Proof (fun p pq => pq p).
(* modus_ponens is defined *)

Print modus_ponens. (* 実際には関数定義と変わらない *)
(* modus_ponens = fun (p : P) (pq : P -> Q) => pq p *)
(* : P -> (P -> Q) -> Q  *)

(* しかし，一つ目ではデータの直積ではなく，命題の論理積を使ったので，作り方を調べなければならない．*)

Locate "/\". (* 論理積の定義を調べる *)
(* Notation Scope                   *)
(* "A /\ B" := and A B : type_scope *)

Print and.
(* Inductive and (A B : Prop) : Prop := conj : A -> B -> A / B *)

(* conj が論理積の証明の構成子だとわかる． *)
Theorem and_self : P -> P /\ P.
Proof (fun x => conj x x).
(* and_self is defined *)


(* 作戦 (tactic) の利用 *)

(*
上のように，プログラムを与えることで定理を証明することができる．しかし，複雑な定理に
なると，途中で出て来る命題が煩雑になり，正しいプログラムを書くのが至難の技になる．
通常は，定理は関数と違う定義方法を使う．証明モードに入り，作戦 (tactic) によって証明を
構築していく．各 tactic は導出規則と対応している．
 *)

Theorem modus_ponens' : P -> (P -> Q) -> Q. (* 異なる名前にする *)

(*
1 subgoal (* 証明の状況が表示される *)

P : Prop
Q : Prop

============================
P -> (P -> Q) -> Q
*)

Proof.
intros p pq. (* 仮定に名前を付ける (抽象) *)

(*
p : P
pq : P -> Q
============================
Q
 *)

apply pq. (* 目標を関数 pq の結果とみなす (適用) *)

(*
p : P
pq : P -> Q
============================
P
*)

assumption.
(* Proof completed. *)
Qed.
(* modus_ponens’ is defined *)

(* 実際の証明をもう一度みよう．*)

Theorem modus_ponens'' : P -> (P -> Q) -> Q.
Proof.
intros p pq.
apply pq.
assumption.
Qed.

(* and_self について同じことをする．*)
Theorem and_self' : P -> P /\ P.
Proof.
intros p.

(*
1 subgoal
p : P
============================
P /\ P
*)

split. (* 論理積の導入 (∧ 導入) *)

(*
2 subgoals (* 前提が二つある *)
p : P
============================
P

subgoal 2 is:
P
*)

assumption. (* 順番に解いていく *)

(*
1 subgoal
p : P
============================
P
*)

assumption.
Qed.

(* and_self’ is defined *)

Print and_self'. (* 実際の定義は前と変わらない *)

(* and_self’ = fun p : P => conj p p *)
(* : P -> P /\ P *)

(* セクションを閉じる *)
End Koushin.

Print and_self.
(* and_self = *) (* 必要な変数が定義に挿入される *)
(* fun (P : Prop) (x : P) => conj x x *)
(* : forall P : Prop, P -> P /\ P     *)


(* 否定に関する定理 *)
(* 証明状態の表示が作戦を読みにくくするので，これ以降は省くことにする．自分で Coq の中で実行して，確認して下さい．*)
Section Negation.

Variables P Q : Prop.
Theorem DeMorgan : ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof.
  unfold not. (* ~ の定義を展開する *)
  intros npq.
  split; intros q. (* ; で両方の subgoal について intros q を行う *)
  apply npq.
  left. (* ∨ 導入の左を使う *)
  assumption.
  apply npq.
  right.
  assumption.
Qed.
(* DeMorgan is defined *)

(*
しかし，双対的な定理 (￢(P ∧ Q) ⊃ ￢P ∨ ￢Q) は直観主義論理ではなりたたない．
Hypothesisコマンドによって二重否定の除去を仮定すると証明できる．ちなみに，Hypothesis コマンドはVariables の異名でしかなくて，動作は全く同じである．
*)

Hypothesis classic : forall P, ~~P -> P. (* 任意の P について *)
(* classic is assumed *)

Theorem DeMorgan' : ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros npq.
  apply classic.
  intro nnpq.
  apply npq.
  clear npq. (* 不要な仮定を忘れる *)
  split; apply classic.
  intros np.
  apply nnpq.
  left.
  assumption.
  intros np; apply nnpq; right; assumption.
Qed.
(* DeMorgan’ is defined *)
End Negation.

(* 仮定を破壊する *)

(*
Coq の帰納的データ型に対して，値を破壊しながら中身を取り出すという tactic が便利であ
る．直接に対応する論理規則はないが，当然ながら他の論理規則から同じ結果を導くことは可能である．
*)

Section Destruct.
Variables P Q : Prop.
Theorem and_comm : P /\ Q -> Q /\ P.
Proof.
  intros pq.
  destruct pq as [p q]. (* 中身を取り出す *)
  split; assumption. (* 一気に終らせる *)
Qed.
(* and_comm is defined *)

Theorem or_comm : P \/ Q -> Q \/P.
Proof.
  intros pq.
  destruct pq as [p | q]. (* 場合が二つある *)
  right; assumption.
  left; assumption.
Qed.
(* or_comm is defined *)
End Destruct.

(* 論理規則と tactic の対応 *)

(*
論理規則 型付け規則 作戦
公理 変数 assumption
⊃ 導入 抽象 intros h
⊃ 除去 適用 apply h
矛盾 elimtype False
∧ 導入 直積 split
∧ 除去 射影 destruct h as [h1 h2]
∨ 導入 直和 left, right
∨ 除去 match destruct h as [h1 | h2]
*)


(* 練習問題 4.1 以下の定理を Coq で証明せよ．*)
Section Coq2.
Variables P Q R : Prop.

Theorem imp_trans : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
Admitted.
Theorem not_false : ~False.
Proof.
Admitted.
Theorem double_neg : P -> ~~P.
Proof.
Admitted.
Theorem contraposition : (P -> Q) -> ~Q -> ~P.
Proof.
Admitted.
Theorem and_assoc : P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
Admitted.
Theorem and_distr : P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
Proof.
Admitted.
Theorem absurd : P -> ~P -> Q.
Proof.
Admitted.

End Coq2.
