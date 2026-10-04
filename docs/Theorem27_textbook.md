# Theorem27.lean 解説

> 対象: [`Theorem27.lean`](../Theorem27.lean)（定理27の入口）。このファイルには宣言がなく、他のファイルを読み込むだけです。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| `#print axioms` | その定理が依存する公理を表示する検査命令。標準の 3 公理だけならよい。 |
| 標準公理 | `propext`, `Classical.choice`, `Quot.sound`。Mathlib の数学が使う標準的な公理。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理27（**無明起行**）の 3 つのファイルを読み込み、主要な定理について `#print axioms` で、**標準公理のみ**を使っていることを確認する入口です。

| ファイル | 内容 | 解説書 |
| --- | --- | --- |
| `Tomabechi/Theorem27/Abstract.lean` | 型つき状態・無明の分類・目標の外の残差の下降 | [解説](Tomabechi_Theorem27_Abstract_textbook.md) |
| `Tomabechi/Theorem27/Actuator.lean` | 条件 27-A：制御入力・Dini 微分・アクチュエータへの帰属 | [解説](Tomabechi_Theorem27_Actuator_textbook.md) |
| `Tomabechi/Theorem27/Connection.lean` | 定理26のフィードバックの流れへの接続（(27.6)〜(27.10)） | [解説](Tomabechi_Theorem27_Connection_textbook.md) |

### ファイルのコメント（日本語訳）

> （このファイルにはモジュールコメントはなく、`import` と `#print axioms` だけです。）

### このファイルが証明していないこと

何も証明していません。内容は上で示したファイルにあります。

## コメント修正記録

（なし）
