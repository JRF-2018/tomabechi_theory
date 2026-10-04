# Tomabechi/Examples/Theorem22_LubStaircase.lean 解説

> 対象: [`Tomabechi/Examples/Theorem22_LubStaircase.lean`](../Tomabechi/Examples/Theorem22_LubStaircase.lean)（定理22の Python 例（LUB 階段）の Lean 根拠（前提充足の範囲））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22（LUB 階段）の Python 例（`examples/theorem22_lub_staircase.py`）の、**前提充足の範囲の** Lean 根拠です。束 \(\mathbb L=\mathrm{Finset}(\mathrm{Fin}\,8)\)（Python のビット集合）、更新 \(u_{n+1}=u_n\vee v_{n+1}\)（(22.1)）、段 \(n\) の谷の中心 \(x_n=|u_n|\)、ガウス谷 \(\tilde V_n(x)=-A\exp(-(x-x_n)^2/(2\sigma^2))\)（\(A=2\)、\(\sigma=\tfrac32\)）、局所球の半径 \(r=1\)。

- **(22.1)(22.3)**：一般補題 `lub_update_is_strict` / `lub_update_strict_iff` を、Python の 3 つの列に適用し、各 \(|u_n|\) を確認します。A（1 要素ずつ）、B（6 要素 → 2 要素）、C（\(v\le u_n\) の入力が混じる）。
- **局所強凸性**：ガウス谷は \(|x-x_n|<\sigma\) で \(\tilde V_n''>0\)。\(r=1<\sigma=\tfrac32\) の球の上で \(\tilde V_n''>0\) を証明します。
- **到達可能性**：A（\(\delta=1\)）では前段の終点が次段の局所球 \(B(x_{n+1},r)\) の中、B（\(\delta=6\)）では球の外。後者は、定理22の「切替状態が次段の吸引域に入る」前提が成り立たないことの例です。

### 0.2 このファイルが証明していないこと

- **範囲外**：段階列の ODE 解、時間尺度の分離、一般の段階定理 (22.4)(22.5)、定理23-B 核の適用（H-stage 入力の構成が必要）。Python の挙動の数値は証明しません（今後の課題。トップの `README.md` を参照）。
- Python を \(\sigma=1\to\tfrac32\) に変更しました（球 \(r=1\) の中で強凸になるため）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理22の Python 例（`examples/theorem22_lub_staircase.py`）の Lean 根拠（前提充足の範囲）
>
> 束 \(\mathbb L=\mathrm{Finset}(\mathrm{Fin}\,8)\)（Python のビット集合）、\(u_{n+1}=u_n\vee v_{n+1}\)（(22.1)）、段 \(n\) の谷の中心 \(x_n=|u_n|\)、ガウス谷 \(\tilde V_n(x)=-A\exp(-(x-x_n)^2/(2\sigma^2))\)（\(A=2\)、\(\sigma=3/2\)）、局所球半径 \(r=1\)。
>
> * (22.1)(22.3)：一般補題 `lub_update_is_strict` / `lub_update_strict_iff` を、Python の 3 列 A（1 要素ずつ）、B（6 要素→2 要素）、C（\(v\le u_n\) の入力が混じる）に適用し、各 \(|u_n|\) を確認。
> * 局所強凸性：ガウス谷は \(|x-x_n|<\sigma\) で \(\tilde V_n''>0\)。\(r=1<\sigma=3/2\) の球上で \(\tilde V_n''>0\) を証明。
> * 到達可能性：A（\(\delta=1\)）では前段の終点が次段の局所球 \(B(x_{n+1},r)\) 内、B（\(\delta=6\)）では球外。後者は、定理22の「切替状態が次段の吸引域に入る」前提が成り立たないことの例である。
>
> 範囲外：段階列の ODE 解、時間尺度分離、一般の段階定理 (22.4)(22.5)、定理23-B 核の適用（H-stage 入力の構成が必要）。Python の挙動の数値は証明しない。

### 0.4 節見出しのコメント（日本語訳）

> ## 束側：(22.1)(22.3)
>
> ## Python のパラメータ \(A=2\)、\(\sigma=3/2\)、\(r=1\)

名前空間は `Tomabechi.Examples.Theorem22Staircase`（`open Tomabechi.Theorem22 Tomabechi.Examples.Gaussian`）。

---

<a id="Tomabechi.Examples.Theorem22Staircase.L8"></a>

## 定義 `L8`

### 式

$$\mathbb L=\mathrm{Finset}(\mathrm{Fin}\,8)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

8 個の要素の部分集合の束（Python のビット集合）。包含で順序づけ、\(\vee\)（和集合）が最小上界です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem22Staircase.uA"></a>

## 定義 `uA`

### 式

$$u_0=\emptyset,\ u_{n+1}=u_n\cup\{n\}$$

### Lean のコメント（日本語訳）

> A：1 要素ずつ。\(u_0=\emptyset\)。

### 定義の説明

列 A：要素を 1 つずつ加える LUB の列。

### 証明の概略

1. 再帰で定義（\(\{0\},\{0,1\},\dots\)）。

----

<a id="Tomabechi.Examples.Theorem22Staircase.A_cards"></a>

## 定理 `A_cards`

### 式

$$(|u_0|,\dots,|u_4|)=(0,1,2,3,4)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

列 A の各段の要素数。

### 証明の概略

1. `decide`（有限の計算）。

----

<a id="Tomabechi.Examples.Theorem22Staircase.A_updates_strict"></a>

## 定理 `A_updates_strict`

### 式

$$u_n<u_n\vee\{n\}\quad(n=0,1,2,3)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

列 A の各更新が**厳密に増える**（(22.1)(22.3)：新しい要素が加わる）。

### 証明の概略

1. `lub_update_is_strict`（`¬ v ≤ u_n` なら \(u_n<u_n\vee v\)）を各 \(n\) で適用し、前提 `¬ v ≤ u_n` は `decide`（有限の計算）。

----

<a id="Tomabechi.Examples.Theorem22Staircase.uB"></a>

## 定義 `uB`

### 式

$$u_0=\emptyset,\ u_1=\{0,\dots,5\},\ u_2=\{0,\dots,7\}$$

### Lean のコメント（日本語訳）

> B：6 要素 \(\{0..5\}\) を一度に、次に \(\{6,7\}\)。

### 定義の説明

列 B：一度に大きく増える LUB の列。

### 証明の概略

1. 再帰で定義。

----

<a id="Tomabechi.Examples.Theorem22Staircase.B_cards"></a>

## 定理 `B_cards`

### 式

$$(|u_0|,|u_1|,|u_2|)=(0,6,8)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

列 B の各段の要素数。

### 証明の概略

1. `decide`。

----

<a id="Tomabechi.Examples.Theorem22Staircase.uC"></a>

## 定義 `uC`

### 式

$$u_0=\emptyset,\ u_1=\{0\},\ u_2=\{0\}\ (\text{2回目の }\{0\}),\ u_3=\{0,1\}$$

### Lean のコメント（日本語訳）

> C：\(v\le u_n\) の入力（2 回目の \(\{0\}\)）では \(u_n\) は増えない（`lub_update_strict_iff`）。

### 定義の説明

列 C：既に含まれる入力が混じる LUB の列。

### 証明の概略

1. 再帰で定義。

----

<a id="Tomabechi.Examples.Theorem22Staircase.C_cards"></a>

## 定理 `C_cards`

### 式

$$(|u_0|,\dots,|u_3|)=(0,1,1,2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

列 C の各段の要素数（2 段目は増えない）。

### 証明の概略

1. `decide`。

----

<a id="Tomabechi.Examples.Theorem22Staircase.C_second_input_not_strict"></a>

## 定理 `C_second_input_not_strict`

### 式

$$\neg\bigl(u_1<u_1\vee\{0\}\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

2 回目の \(\{0\}\) は既に \(u_1\) に含まれるので、更新は厳密には増えない（(22.3) の「iff」の否定側）。

### 証明の概略

1. \(\{0\}\le u_1\) なので \(u_1\vee\{0\}=u_1\)。

----

<a id="Tomabechi.Examples.Theorem22Staircase.C_first_and_third_strict"></a>

## 定理 `C_first_and_third_strict`

### 式

$$u_0<u_0\vee\{0\}\ \wedge\ u_2<u_2\vee\{0,1\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

1 回目と 3 回目の入力では厳密に増える。

### 証明の概略

1. `lub_update_is_strict` を適用し、前提（新しい要素が加わること）は `decide`。

----

<a id="Tomabechi.Examples.Theorem22Staircase.centerA"></a>

## 定義 `centerA`

### 式

$$x_n=|u_n|$$

### Lean のコメント（日本語訳）

> Python の谷の中心 \(x_n=|u_n|\)（A 列）。

### 定義の説明

段 \(n\) の谷の中心を、LUB の要素数にとる。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem22Staircase.centerB"></a>

## 定義 `centerB`

### 式

$$x_n=|u_n|\ (\text{B 列})$$

### Lean のコメント（日本語訳）

> B 列。

### 定義の説明

B 列の谷の中心。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem22Staircase.python_well_strongly_convex"></a>

## 定理 `python_well_strongly_convex`

### 式

$$|x-c|\le1\Rightarrow\mathrm{ddwell}_{2,3/2,c}(x)>0$$

### Lean のコメント（日本語訳）

> 各段の谷は \(r=1<\sigma=3/2\) の球で強凸。

### 補題の説明

**ガウス谷の局所強凸性**（\(A=2\)、\(\sigma=\frac32\)、\(r=1\)）。

### 証明の概略

1. `Gaussian.ddwell_pos`（\(A>0\)、\(r<\sigma\)）を適用。

----

<a id="Tomabechi.Examples.Theorem22Staircase.A_switch_state_in_next_ball"></a>

## 定理 `A_switch_state_in_next_ball`

### 式

$$\forall n<4,\ |x_n-x_{n+1}|\le1$$

### Lean のコメント（日本語訳）

> A（\(\delta=1\)）：前段の終点（中心 \(x_n\)）は、次段の局所球 \(B(x_{n+1},1)\) の中。

### 補題の説明

**到達可能性（成立）**：列 A では中心が 1 ずつ動くので、前段の終点は次段の局所球に入ります。

### 証明の概略

1. \(n=0,1,2,3\) に場合分け（`interval_cases`）し、`centerA`・`uA` を展開して \(|x_n-x_{n+1}|=1\) を `norm_num` で計算。

----

<a id="Tomabechi.Examples.Theorem22Staircase.B_switch_state_outside_next_ball"></a>

## 定理 `B_switch_state_outside_next_ball`

### 式

$$\neg\,|x_0-x_1|\le1$$

### Lean のコメント（日本語訳）

> B（\(\delta=6\)）：前段の終点（中心 0）は、次段の局所球 \(B(6,1)\) の外。定理22の「切替状態が次段の吸引域に入る」前提が成り立たない。

### 補題の説明

**到達可能性（不成立）**：列 B では中心が 0 から 6 へ飛ぶので、前段の終点は次段の局所球の外です。**前提が破れる例**で、原文の定理22の反例ではありません。

### 証明の概略

1. `centerB`・`uB` を展開すると \(x_0=|u_B(0)|=0\)、\(x_1=|u_B(1)|=6\)（要素数）。
2. \(|0-6|=6>1\) を `norm_num` で示す。

----


## コメント修正記録

（なし）
