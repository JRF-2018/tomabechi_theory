# Tomabechi/Consistency/ConsistencyC2_EntropyBalance.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC2_EntropyBalance.lean`](../Tomabechi/Consistency/ConsistencyC2_EntropyBalance.lean)（可算無限層のエントロピー収支（定理15→23-A の具体モデル））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理15（エントロピーの収支）から定理23（諸行無常）**を、**可算無限個の層**を持つ具体的なモデルで、全部の前提を明示して成り立たせるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「可算層のエントロピー収支」（C2）にあたります。

モデルは次のとおりです。

* **完全状態** \(z=(q,y)\)：\(q\) は認知状態、\(y\) は環境・物理の観測量。
* **軌道** \(q(t)=1-e^{-t}\)、\(y(t)=t-q(t)^2\)。
* **正の層** \(n=0,1,2,\dots\) の重み \(w_n=2^{-(n+1)}\)（総和 1）。各層の意味エントロピーは同じ \(1+q^2\)。物理層（添字 0）は別枠でエントロピー 0。
* **一般化エントロピー** \(S=y+\sum_nw_n(1+q^2)=t+1\)。生成率は \(\Pi\equiv1\)。
* 粗視化の射影は恒等写像（具体例として A3・A4 を型で記録）。

定理15の仮定 A1〜A5・A6′・A7 が成り立つことを、一つずつ証明し、可算無限層の入口に渡して、**軌道は同じ状態に戻らない**（定理23第一部）を得ます。追加の明示条件 H-sum（有限部分和の一様可積分性・a.e. 収束・端点の総和可能性）もここで満たします。

### 0.2 このファイルが証明していないこと

* 状態は二次元（認知と環境）の具体モデルで、**全層が同じ状態空間と同じ意味エントロピー**を使います。層ごとに異なるエントロピーを持つ一般のモデルではありません。
* A4（粗視化でエントロピーは減らない。等号は可逆な場合に限る）の「可逆」は、この具体例では射影が恒等であることによって成り立ちます。
* 原文は、意味エントロピーの汎関数が Shannon 型であることを要求していません。ここでは認知座標の二次式で与えています。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 各正層を `n+1` で列挙し、物理層 `0` は別枠に置く。層重みは幾何級数、全層の意味エントロピーは同じ状態観測量とする。完全状態には環境観測量も含め、その観測量自身をエントロピーに使う。以下の射影は層を粗視化しても状態を保つ具体例であり、A3/A4 を型付きで記録する。

---

<a id="Tomabechi.Consistency.C2.uniformIntegrable_of_bound_two"></a>

## 補題 `uniformIntegrable_of_bound_two`

### 式

$$
|f_i|\le2\ \text{(a.e.)}\Rightarrow\{f_i\}\ \text{は一様可積分}
$$

### Lean のコメント（日本語訳）

> 有限測度空間の上で、一様に有界な可測関数の族は一様可積分である。有限部分和の H-sum で使う、具体的な上界の形で述べる。

### 補題の説明

有限測度空間の上で、一様に有界な可測関数の族は、一様可積分です。有限部分和の H-sum（可算層の和の条件）で使う、具体的な上界（2）の形で述べます。

### 証明の概略

1. 一様可積分性の定義（等可積分性と \(L^1\) 有界性）を、上界 2 から示す。
2. 任意の \(\varepsilon>0\) に対し、\(\delta=\varepsilon/2\) を取ると、測度が \(\delta\) 以下の集合の上の積分は \(2\delta=\varepsilon\) 以下。
3. 全体の積分も、\(2\times\)全測度で有界。

----

<a id="Tomabechi.Consistency.C2.absolutelyContinuous_of_hasDerivAt"></a>

## 補題 `absolutelyContinuous_of_hasDerivAt`

### 式

$$
f'\ \text{連続}\Rightarrow f\ \text{は有限区間で絶対連続}
$$

### Lean のコメント（日本語訳）

> 連続的に微分可能なスカラーの観測量は、どの有限区間でも絶対連続である。

### 補題の説明

連続的に微分可能な（導関数が連続な）実数値の関数は、有限区間で絶対連続です。

### 証明の概略

1. \(f(t)=f(a)+\int_a^tf'\)（微積分の基本定理）。
2. 導関数 \(f'\) は連続なので区間可積分。積分は絶対連続、定数も絶対連続。和も絶対連続。

----

<a id="Tomabechi.Consistency.C2.CompleteState"></a>

## 定義 `CompleteState`

### 式

$$
\mathbb R\times\mathbb R
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

**完全状態**の型です。第 1 座標が認知状態 \(q\)、第 2 座標が環境・物理の観測量 \(y\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.PositiveLayer"></a>

## 定義 `PositiveLayer`

### 式

$$
\mathbb N
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

**正の層**の添字の型です。層 \(n\) は、原文の添字 \(n+1\) に対応します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.cognitiveCoordinate"></a>

## 定義 `cognitiveCoordinate`

### 式

$$
z\mapsto z_1
$$

### Lean のコメント（日本語訳）

> 第1座標を認知状態、第2座標を環境・物理観測と読む。

### 定義の説明

完全状態の第 1 座標（認知状態）を取り出します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.physicalCoordinate"></a>

## 定義 `physicalCoordinate`

### 式

$$
z\mapsto z_2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

完全状態の第 2 座標（環境・物理の観測量）を取り出します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalPositiveIndex"></a>

## 定義 `originalPositiveIndex`

### 式

$$
n\mapsto n+1
$$

### Lean のコメント（日本語訳）

> 正層 n は原文の添字 n+1 に対応する。

### 定義の説明

正の層 \(n\) は、原文の層の添字 \(n+1\) に対応します（原文の添字 0 は物理層）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalLayerIndexSet"></a>

## 定義 `originalLayerIndexSet`

### 式

$$
\{0,1,2,\dots\}\subset\mathbb R
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

原文の層の添字の集合 \(\mathcal A\)（非負の整数）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalLayerIndexSet_countable"></a>

## 補題 `originalLayerIndexSet_countable`

### 式

$$
\mathcal A\ \text{は可算}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の添字の集合は可算です。

### 証明の概略

1. 自然数からの像（`countable_range`）。

----

<a id="Tomabechi.Consistency.C2.originalLayerIndexSet_nonnegative"></a>

## 補題 `originalLayerIndexSet_nonnegative`

### 式

$$
\mathcal A\subseteq[0,\infty)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の添字は非負です。

### 証明の概略

1. 自然数の非負性。

----

<a id="Tomabechi.Consistency.C2.originalPositiveIndex_pos"></a>

## 補題 `originalPositiveIndex_pos`

### 式

$$
n+1>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の層の原文の添字は正です。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.C2.originalPositiveIndex_injective"></a>

## 補題 `originalPositiveIndex_injective`

### 式

$$
n+1=m+1\Rightarrow n=m
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の層から原文の添字への対応は単射です。

### 証明の概略

1. \(n+1=m+1\) から \(n=m\)（`omega`）。

----

<a id="Tomabechi.Consistency.C2.originalPositiveRealIndex"></a>

## 定義 `originalPositiveRealIndex`

### 式

$$
n\mapsto(n+1:\mathbb R)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

正の層の原文の添字を、実数として見たものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalPositiveRealIndex_pos"></a>

## 補題 `originalPositiveRealIndex_pos`

### 式

$$
>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実数の添字は正です。

### 証明の概略

1. 自然数の添字が正であること（キャスト）。

----

<a id="Tomabechi.Consistency.C2.originalPositiveRealIndex_injective"></a>

## 補題 `originalPositiveRealIndex_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実数の添字への対応も単射です。

### 証明の概略

1. 自然数のキャストの単射性と、整数の添字の単射性。

----

<a id="Tomabechi.Consistency.C2.layerWeight"></a>

## 定義 `layerWeight`

### 式

$$
w_n=2^{-(n+1)}
$$

### Lean のコメント（日本語訳）

> 正の幾何重み `2^(-(n+1))`。

### 定義の説明

正の層 \(n\) の重み \(w_n=2^{-(n+1)}\) です（幾何級数で、和が 1）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.layerWeight_pos"></a>

## 補題 `layerWeight_pos`

### 式

$$
w_n>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みは正です。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Consistency.C2.positiveLayer_infinite"></a>

## 補題 `positiveLayer_infinite`

### 式

$$
\text{層は無限個}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の層は無限個あります（可算無限層）。

### 証明の概略

1. 自然数は無限（型クラスの自動解決）。

----

<a id="Tomabechi.Consistency.C2.layerWeight_summable"></a>

## 補題 `layerWeight_summable`

### 式

$$
\sum w_n<\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みの和は収束します。

### 証明の概略

1. 幾何級数 \(\sum(1/2)^n\) は収束（公比 \(1/2<1\)）。\(w_n=\tfrac12(1/2)^n\) なので、定数倍も収束。

----

<a id="Tomabechi.Consistency.C2.layerWeight_tsum"></a>

## 補題 `layerWeight_tsum`

### 式

$$
\sum_n w_n=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みの総和は 1 です。

### 証明の概略

1. 幾何級数の和 \(\sum(1/2)^n=2\)（`tsum_geometric_of_lt_one`）。\(w_n=\tfrac12(1/2)^n\) なので和は \(\tfrac12\cdot2=1\)。

----

<a id="Tomabechi.Consistency.C2.layerWeight_sum_le_one"></a>

## 補題 `layerWeight_sum_le_one`

### 式

$$
\sum_{n\in s}w_n\le1\ (s\ \text{有限})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限個の層の重みの和は 1 以下です。

### 証明の概略

1. 有限和は、非負の項の無限和以下（`sum_le_tsum`）。無限和は 1。

----

<a id="Tomabechi.Consistency.C2.layerEntropy"></a>

## 定義 `layerEntropy`

### 式

$$
H_n(z)=1+q^2
$$

### Lean のコメント（日本語訳）

> 意味エントロピーは状態の認知座標の `1+q²`。

### 定義の説明

正の層の**意味エントロピー**です。状態の認知座標 \(q\) について \(1+q^2\)（全層で同じ観測量）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.physicalEntropy"></a>

## 定義 `physicalEntropy`

### 式

$$
S_{\mathrm{phys}}(z)=y
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

物理エントロピーは、環境・物理の観測量 \(y\)（第 2 座標）です。完全状態には環境の観測量も含め、その観測量自身をエントロピーに使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.physicalLayerEntropy"></a>

## 定義 `physicalLayerEntropy`

### 式

$$
H_0(z)=0
$$

### Lean のコメント（日本語訳）

> 物理層のエントロピーは独立に0とし、正層列挙へ混ぜない。

### 定義の説明

物理層（添字 0）のエントロピーは、独立に 0 と置き、正の層の列挙には混ぜません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalLayerEntropy"></a>

## 定義 `originalLayerEntropy`

### 式

$$
H_a(z)=\begin{cases}0&a=0\\1+q^2&a>0\end{cases}
$$

### Lean のコメント（日本語訳）

> 原文の全層添字では `0` を物理層、`a>0` を正層として扱う。

### 定義の説明

原文の全層の添字では、\(a=0\) を物理層（エントロピー 0）、\(a>0\) を正の層（\(1+q^2\)）として扱います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalLayerEntropy_physical"></a>

## 補題 `originalLayerEntropy_physical`

### 式

$$
H_0=\text{物理層のエントロピー}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

添字 0 は物理層のエントロピーです。

### 証明の概略

1. 定義の `if` の条件が成り立つ（`simp`）。

----

<a id="Tomabechi.Consistency.C2.originalLayerEntropy_positive"></a>

## 補題 `originalLayerEntropy_positive`

### 式

$$
H_{n+1}=H_n^{\text{正層}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

原文の添字 \(n+1\) は、正の層 \(n\) の意味エントロピーに一致します。

### 証明の概略

1. `if` の条件が偽（`simp`）。

----

<a id="Tomabechi.Consistency.C2.originalProject"></a>

## 定義 `originalProject`

### 式

$$
\pi_{\beta\leftarrow\alpha}=\mathrm{id}
$$

### Lean のコメント（日本語訳）

> 原文の全層状態は同じ完全状態空間で表し、粗視化射影を恒等写像にする。

### 定義の説明

原文の全層の状態を、同じ完全状態空間で表し、**粗視化の射影を恒等写像**にします（A3・A4 の具体例）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalProjection"></a>

## 定義 `originalProjection`

### 式

$$
\pi_{\beta\leftarrow\alpha}=\mathrm{id}\quad(\beta\le\alpha)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(\beta\le\alpha\) に対する射影（恒等写像）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.originalProjection_measurable"></a>

## 補題 `originalProjection_measurable`

### 式

$$
\pi\ \text{は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は可測です（恒等写像）。

### 証明の概略

1. 恒等写像は可測（`measurable_id`）。

----

<a id="Tomabechi.Consistency.C2.originalProjection_reflexive"></a>

## 補題 `originalProjection_reflexive`

### 式

$$
\pi_{\alpha\leftarrow\alpha}=\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同じ層への射影は恒等写像です（A3 の \(\pi_{\alpha\leftarrow\alpha}=\mathrm{id}\)）。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C2.originalProjection_compose"></a>

## 補題 `originalProjection_compose`

### 式

$$
\pi_{\gamma\leftarrow\beta}\circ\pi_{\beta\leftarrow\alpha}=\pi_{\gamma\leftarrow\alpha}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影の合成則（半群性、A3）です。

### 証明の概略

1. 両辺とも恒等写像（`rfl`）。

----

<a id="Tomabechi.Consistency.C2.originalProject_measurable"></a>

## 補題 `originalProject_measurable`

### 式

$$
\pi\ \text{は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

狭義の粗視化の射影も可測です。

### 証明の概略

1. `measurable_id`。

----

<a id="Tomabechi.Consistency.C2.originalProject_reflect"></a>

## 補題 `originalProject_reflect`

### 式

$$
\pi(z)=z
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は状態を変えません。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C2.originalProject_bijective"></a>

## 補題 `originalProject_bijective`

### 式

$$
\pi\ \text{は全単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は全単射です（恒等写像）。

### 証明の概略

1. `Function.bijective_id`。

----

<a id="Tomabechi.Consistency.C2.originalProject_compose"></a>

## 補題 `originalProject_compose`

### 式

$$
\pi_{\gamma\leftarrow\beta}\circ\pi_{\beta\leftarrow\alpha}=\pi_{\gamma\leftarrow\alpha}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

狭義の粗視化の射影の合成則です。

### 証明の概略

1. 両辺とも恒等写像（`rfl`）。

----

<a id="Tomabechi.Consistency.C2.originalLayer_coarse_graining"></a>

## 補題 `originalLayer_coarse_graining`

### 式

$$
H_\beta(\pi z)\ge H_\alpha(z),\ \text{等号なら}\ \exists y,\ \pi y=z
$$

### Lean のコメント（日本語訳）

> A4：正の層は同じエントロピーと恒等の射影を持つので、粗視化はエントロピーを保ち、等号のときは可逆である。

### 補題の説明

A4（粗視化でエントロピーは減らない。等号なら射影は可逆）です。正の層は同じエントロピーと恒等の射影を持つので、粗視化はエントロピーを保ち、等号のとき逆元（\(y=z\)）が存在します。

### 証明の概略

1. 正の層同士では、エントロピーが同じなので \(\ge\) は等号で成り立つ（`rfl` で処理）。
2. 等号の場合は \(y=z\) を取る（射影が恒等だから）。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_nonnegative"></a>

## 補題 `layerEntropy_nonnegative`

### 式

$$
H_n(z)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

意味エントロピーは非負です。

### 証明の概略

1. \(1+q^2\ge1>0\)（`positivity`）。

----

<a id="Tomabechi.Consistency.C2.project"></a>

## 定義 `project`

### 式

$$
\pi_{\beta\leftarrow\alpha}=\mathrm{id}\quad(\beta<\alpha)
$$

### Lean のコメント（日本語訳）

> 各正層の射影。

### 定義の説明

正の層の間の射影（恒等写像）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.project_measurable"></a>

## 補題 `project_measurable`

### 式

$$
\pi\ \text{は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は可測です。

### 証明の概略

1. `measurable_id`。

----

<a id="Tomabechi.Consistency.C2.project_reflect"></a>

## 補題 `project_reflect`

### 式

$$
\pi(z)=z
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影は状態を変えません。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Consistency.C2.project_compose"></a>

## 補題 `project_compose`

### 式

$$
\pi\circ\pi=\pi
$$

### Lean のコメント（日本語訳）

> 射影の合成則。

### 補題の説明

射影の合成則です。

### 証明の概略

1. 両辺とも恒等写像。

----

<a id="Tomabechi.Consistency.C2.coarse_graining_entropy"></a>

## 補題 `coarse_graining_entropy`

### 式

$$
H_\beta(\pi z)\ge H_\alpha(z),\ \text{等号なら}\ \exists y,\ \pi y=z
$$

### Lean のコメント（日本語訳）

> 粗視化で層エントロピーは保存される。等号の場合の逆向きも明示する。

### 補題の説明

粗視化で、層のエントロピーは保存されます（不等式は等号）。等号の場合の逆向き（元に戻せること）も明示します。

### 証明の概略

1. 射影が恒等なので、エントロピーは等しい（`rfl`）。
2. 等号の逆向きは \(y=z\)。

----

<a id="Tomabechi.Consistency.C2.trajectory"></a>

## 定義 `trajectory`

### 式

$$
t\mapsto\bigl(q(t),\ t-q(t)^2\bigr),\quad q(t)=1-e^{-t}
$$

### Lean のコメント（日本語訳）

> 観測軌道。`q'=1-q`、`y'=q` を環境を含む完全状態上で実現する。

### 定義の説明

**観測軌道**です。認知状態 \(q(t)=1-e^{-t}\)（\(q'=1-q\)）、環境の観測量 \(y(t)=t-q(t)^2\) です。環境を含む完全状態の上で、この軌道を実現します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.DirectSumState"></a>

## 定義 `DirectSumState`

### 式

$$
\prod_n(\mathbb R\times\mathbb R)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの状態の直和（直積）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.layerDomain"></a>

## 定義 `layerDomain`

### 式

$$
\text{各層の領域}=\text{全体}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の状態の領域は、完全状態の全体です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.layerDomain_measurable"></a>

## 補題 `layerDomain_measurable`

### 式

$$
\text{領域は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各層の領域は可測です（全体）。

### 証明の概略

1. `MeasurableSet.univ`。

----

<a id="Tomabechi.Consistency.C2.trajectory_continuous"></a>

## 補題 `trajectory_continuous`

### 式

$$
\text{軌道は連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は連続です。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Consistency.C2.trajectory_measurable"></a>

## 補題 `trajectory_measurable`

### 式

$$
\text{軌道は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は可測です。

### 証明の概略

1. 連続なので可測。

----

<a id="Tomabechi.Consistency.C2.diagonalEmbedding"></a>

## 定義 `diagonalEmbedding`

### 式

$$
z\mapsto(z,z,z,\dots)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同じ完全状態を、全層に置いた直和の元（対角）にする写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.diagonalEmbedding_injective"></a>

## 補題 `diagonalEmbedding_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角埋め込みは単射です。

### 証明の概略

1. 0 番の層を見る。

----

<a id="Tomabechi.Consistency.C2.directSumTrajectory"></a>

## 定義 `directSumTrajectory`

### 式

$$
t\mapsto\mathrm{diag}(\text{trajectory}(t))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

軌道を直和に置いたものです（全層で同じ状態）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.directSumTrajectory_measurable"></a>

## 補題 `directSumTrajectory_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

直和の軌道は可測です。

### 証明の概略

1. 各層の成分が可測（`measurable_pi_lambda`）。

----

<a id="Tomabechi.Consistency.C2.directSumTrajectory_projection"></a>

## 補題 `directSumTrajectory_projection`

### 式

$$
\text{直和軌道}_n=\text{trajectory}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

直和の軌道の各層の成分は、元の軌道です。

### 証明の概略

1. 定義（`rfl`）。

----

<a id="Tomabechi.Consistency.C2.directSumTrajectory_is_diagonal"></a>

## 補題 `directSumTrajectory_is_diagonal`

### 式

$$
\text{直和軌道}=\mathrm{diag}(\text{trajectory})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

直和の軌道は、軌道の対角埋め込みです。

### 証明の概略

1. 定義（`rfl`）。

----

<a id="Tomabechi.Consistency.C2.qCoordinate"></a>

## 定義 `qCoordinate`

### 式

$$
q(t)=1-e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

認知座標 \(q(t)=1-e^{-t}\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.alive"></a>

## 定義 `alive`

### 式

$$
[0,\infty)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

生きている時間の集合です（\(t\ge0\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.production"></a>

## 定義 `production`

### 式

$$
\Pi(t)\equiv1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

エントロピーの**生成率** \(\Pi\) は、常に 1 です（A7 の \(\Pi\ge0\)・可積分）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.production_intervalIntegrable"></a>

## 補題 `production_intervalIntegrable`

### 式

$$
\Pi\ \text{は区間可積分}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生成率は有限区間で可積分です（定数）。

### 証明の概略

1. 連続関数は区間可積分。

----

<a id="Tomabechi.Consistency.C2.cognitiveEntropyRate"></a>

## 定義 `cognitiveEntropyRate`

### 式

$$
2q(t)e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各正の層のエントロピーの時間変化率 \(\tfrac{d}{dt}(1+q^2)=2q\,q'=2q\,e^{-t}\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.physicalEntropyRate"></a>

## 定義 `physicalEntropyRate`

### 式

$$
1-2q(t)e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

物理エントロピーの時間変化率 \(y'=1-2q\,e^{-t}\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.continuous_cognitiveEntropyRate"></a>

## 補題 `continuous_cognitiveEntropyRate`

### 式

$$
\text{連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知エントロピーの変化率は連続です。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Consistency.C2.continuous_physicalEntropyRate"></a>

## 補題 `continuous_physicalEntropyRate`

### 式

$$
\text{連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理エントロピーの変化率は連続です。

### 証明の概略

1. 定数と連続関数の差。

----

<a id="Tomabechi.Consistency.C2.cognitiveCoordinate_hasDerivAt_pre"></a>

## 補題 `cognitiveCoordinate_hasDerivAt_pre`

### 式

$$
\frac{d}{dt}q=e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知座標の微分は \(e^{-t}\) です（準備の版）。

### 証明の概略

1. \(e^{-s}\) の微分は \(-e^{-t}\)。\(1-\cdot\) で符号が反転。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_hasDerivAt_pre"></a>

## 補題 `layerEntropy_hasDerivAt_pre`

### 式

$$
\frac{d}{dt}H_n=2q\,e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層のエントロピーの微分は \(2q\,e^{-t}\) です（準備の版）。

### 証明の概略

1. \(q'=e^{-t}\)（前の補題）。\(1+q^2\) の微分は \(2q\,q'\)。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_deriv_eq_rate_pre"></a>

## 補題 `layerEntropy_deriv_eq_rate_pre`

### 式

$$
\operatorname{deriv}H_n=\text{rate}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層のエントロピーの微分は、変化率 `cognitiveEntropyRate` に等しいです（準備の版）。

### 証明の概略

1. 前の補題の微分の値を、定義と比べる。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_deriv_eq_rate"></a>

## 補題 `layerEntropy_deriv_eq_rate`

### 式

$$
\operatorname{deriv}H_n=\text{rate}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層のエントロピーの微分は、変化率に等しいです。

### 証明の概略

1. 準備の版をそのまま使う。

----

<a id="Tomabechi.Consistency.C2.finiteCognitiveRate"></a>

## 定義 `finiteCognitiveRate`

### 式

$$
\sum_{n\in s}w_n\,\frac{d}{dt}H_n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

有限個の層の集合 \(s\) についての、重みつきの変化率の和です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.cognitiveEntropyRate_bounds"></a>

## 補題 `cognitiveEntropyRate_bounds`

### 式

$$
t\ge0\Rightarrow0\le\text{rate}\le2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生きている時間（\(t\ge0\)）では、変化率は 0 以上 2 以下です。

### 証明の概略

1. \(0\le e^{-t}\le1\)、したがって \(0\le q\le1\)。\(\text{rate}=2q\,e^{-t}\in[0,2]\)。

----

<a id="Tomabechi.Consistency.C2.finiteCognitiveRate_continuous"></a>

## 補題 `finiteCognitiveRate_continuous`

### 式

$$
\text{連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限和の変化率は連続です。

### 証明の概略

1. \(\text{rate}\) を重みの有限和 \(\times\) 共通の変化率に直す。連続関数の定数倍。

----

<a id="Tomabechi.Consistency.C2.finiteCognitiveRate_bounds"></a>

## 補題 `finiteCognitiveRate_bounds`

### 式

$$
t\ge0\Rightarrow0\le\text{有限和}\le2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限個の層の変化率の和は、0 以上 2 以下です（**一様な上界**）。

### 証明の概略

1. 有限和 \(=(\sum_s w_n)\times\text{rate}\)。重みの有限和は 0 以上 1 以下。変化率は 0 以上 2 以下。

----

<a id="Tomabechi.Consistency.C2.generalizedEntropy"></a>

## 定義 `generalizedEntropy`

### 式

$$
S(z)=y+\sum_nw_n\,(1+q^2)
$$

### Lean のコメント（日本語訳）

> この完全状態上の時間非依存一般化エントロピー。

### 定義の説明

この完全状態の上の、時間に依存しない**一般化エントロピー**です。物理エントロピー \(y\) に、重みつきの意味エントロピーの和を足したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C2.weightedLayerEntropy_tsum"></a>

## 補題 `weightedLayerEntropy_tsum`

### 式

$$
\sum_nw_n(1+q^2)=1+q^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みつきの意味エントロピーの和は \(1+q^2\) です（重みの総和が 1）。

### 証明の概略

1. 各項を、\((1+q^2)\times w_n\) の形に並べ替える。定数倍と重みの総和 1（`layerWeight_tsum`）。

----

<a id="Tomabechi.Consistency.C2.weightedLayerEntropy_summable"></a>

## 補題 `weightedLayerEntropy_summable`

### 式

$$
\text{重みつきの意味エントロピーは総和可能}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みつきの意味エントロピーの和は収束します（A6′(i) の端点の総和可能性）。

### 証明の概略

1. 各項は \((1+q^2)\,w_n\)。重みが総和可能（`layerWeight_summable`）なので、定数倍も。

----

<a id="Tomabechi.Consistency.C2.trajectory_cognitive_nonneg"></a>

## 補題 `trajectory_cognitive_nonneg`

### 式

$$
t\ge0\Rightarrow q(t)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生きている時間では、認知座標は非負です。

### 証明の概略

1. \(e^{-t}\le1\) から \(q=1-e^{-t}\ge0\)。

----

<a id="Tomabechi.Consistency.C2.generalizedEntropy_trajectory"></a>

## 補題 `generalizedEntropy_trajectory`

### 式

$$
S(\text{trajectory}(t))=t+1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道に沿った一般化エントロピーは、**\(t+1\)** です（時間に比例して増える）。

### 証明の概略

1. \(y+(1+q^2)=(t-q^2)+(1+q^2)=t+1\)。

----

<a id="Tomabechi.Consistency.C2.generalizedEntropy_hasDerivAt"></a>

## 補題 `generalizedEntropy_hasDerivAt`

### 式

$$
\frac{d}{dt}S=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般化エントロピーの微分は 1（生成率）です。

### 証明の概略

1. \(S=t+1\) の微分。

----

<a id="Tomabechi.Consistency.C2.cognitiveCoordinate_hasDerivAt"></a>

## 補題 `cognitiveCoordinate_hasDerivAt`

### 式

$$
\frac{d}{dt}q=e^{-t}
$$

### Lean のコメント（日本語訳）

> 生きている区間で、`q(t)=1-exp(-t)` の変化率は `exp(-t)` である。

### 補題の説明

生きている区間で、\(q(t)=1-e^{-t}\) の変化率は \(e^{-t}\) です。

### 証明の概略

1. \(e^{-s}\) の微分は \(-e^{-t}\)。\(1-\cdot\) で符号が反転。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_hasDerivAt"></a>

## 補題 `layerEntropy_hasDerivAt`

### 式

$$
\frac{d}{dt}H_n=2q\,e^{-t}
$$

### Lean のコメント（日本語訳）

> 個々の層のエントロピーの変化率は、正のどの時刻でも 0 でない。

### 補題の説明

各層のエントロピーの微分は \(2q\,e^{-t}\) で、正の時刻ではすべて 0 でありません。

### 証明の概略

1. \(q'=e^{-t}\)。\(1+q^2\) の微分は \(2q\,q'\)。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_rate_pos"></a>

## 補題 `layerEntropy_rate_pos`

### 式

$$
t>0\Rightarrow\frac{d}{dt}H_n>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の時刻では、各層のエントロピーは**厳密に増加**します（微分が正）。

### 証明の概略

1. 微分は \(2q\,e^{-t}\)。\(t>0\) で \(q>0\)、\(e^{-t}>0\)。

----

<a id="Tomabechi.Consistency.C2.qCoordinate_hasDerivAt"></a>

## 補題 `qCoordinate_hasDerivAt`

### 式

$$
\frac{d}{dt}q=e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知座標 `qCoordinate` の微分は \(e^{-t}\) です。

### 証明の概略

1. `qCoordinate` は軌道の認知座標に等しい。前の補題。

----

<a id="Tomabechi.Consistency.C2.physicalEntropy_along_eq"></a>

## 補題 `physicalEntropy_along_eq`

### 式

$$
S_{\mathrm{phys}}(\text{trajectory}(t))=t-q(t)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道に沿った物理エントロピーは \(t-q^2\) です。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.C2.physicalEntropy_hasDerivAt"></a>

## 補題 `physicalEntropy_hasDerivAt`

### 式

$$
\frac{d}{dt}S_{\mathrm{phys}}=1-2q\,e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理エントロピーの微分は \(1-2q\,e^{-t}\) です。

### 証明の概略

1. \(t\) の微分 1 から、\(q^2\) の微分 \(2q\,q'\) を引く。

----

<a id="Tomabechi.Consistency.C2.layerEntropy_ac"></a>

## 補題 `layerEntropy_ac`

### 式

$$
H_n(\text{trajectory}(t))\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層のエントロピーは、有限区間で絶対連続です（A2）。

### 証明の概略

1. 微分が連続な変化率（`absolutelyContinuous_of_hasDerivAt`）。

----

<a id="Tomabechi.Consistency.C2.physicalEntropy_deriv_eq_rate"></a>

## 補題 `physicalEntropy_deriv_eq_rate`

### 式

$$
\operatorname{deriv}S_{\mathrm{phys}}=\text{rate}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理エントロピーの微分は、変化率に等しいです。

### 証明の概略

1. 前の補題の微分の値と定義。

----

<a id="Tomabechi.Consistency.C2.physicalEntropy_ac"></a>

## 補題 `physicalEntropy_ac`

### 式

$$
S_{\mathrm{phys}}(\text{trajectory}(t))\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理エントロピーは、有限区間で絶対連続です（A5）。

### 証明の概略

1. 微分が連続な変化率。

----

<a id="Tomabechi.Consistency.C2.weightedLayerRate_tsum"></a>

## 補題 `weightedLayerRate_tsum`

### 式

$$
\sum_nw_n\frac{d}{dt}H_n=2q\,e^{-t}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みつきの層の変化率の和は、\(2q\,e^{-t}\) です。

### 証明の概略

1. 各層の変化率が同じ値。重みの総和 1 を使う（`tsum_mul_left`）。

----

<a id="Tomabechi.Consistency.C2.theorem15_A7_pointwise"></a>

## 補題 `theorem15_A7_pointwise`

### 式

$$
\frac{dS_{\mathrm{phys}}}{dt}=-\sum_nw_n\frac{dH_n}{dt}+\Pi
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理15の A7（エントロピーの収支）が、各時刻で成り立ちます。\(1-2qe^{-t}=-(2qe^{-t})+1\)。

### 証明の概略

1. 物理エントロピーの微分（\(1-2qe^{-t}\)）と、重みつき変化率の和（\(2qe^{-t}\)）を書き換える。生成率は 1。

----

<a id="Tomabechi.Consistency.C2.theorem15_A6_endpoint_summable"></a>

## 補題 `theorem15_A6_endpoint_summable`

### 式

$$
\sum_nw_nH_n(\text{trajectory}(t))<\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

A6′(i)：端点での総和可能性です。

### 証明の概略

1. `weightedLayerEntropy_summable`。

----

<a id="Tomabechi.Consistency.C2.theorem15_A6_prefix_tendsto"></a>

## 補題 `theorem15_A6_prefix_tendsto`

### 式

$$
\sum_{i<k}w_{p_i}\frac{dH_{p_i}}{dt}\to\sum_nw_n\frac{dH_n}{dt}
$$

### Lean のコメント（日本語訳）

> 層の微分の級数は、各点で、その総和に収束する。これが A6′(ii) の、列挙に沿った a.e. の極限を与える（実際はすべての時刻で成り立つ）。

### 補題の説明

層の微分の級数は、全体の和に各時刻で収束します。これが A6′(ii) の、列挙に沿った「ほとんど至る所での極限」を与えます（実際にはすべての時刻で成り立ちます）。

### 証明の概略

1. 各項は \(w_n\times\text{rate}\) で、総和可能。
2. 総和可能な級数の部分和は、列挙の順序によらず全体の和に収束する。

----

<a id="Tomabechi.Consistency.C2.theorem15_A6_allFinite_UI"></a>

## 補題 `theorem15_A6_allFinite_UI`

### 式

$$
\{\sum_{n\in s}w_n\,H_n'\}_{s\ \text{有限}}\ \text{は一様可積分}
$$

### Lean のコメント（日本語訳）

> 有限部分集合の微分の和は、生きているどの有限区間でも一様に有界であり、したがって有限部分集合の族の全体がそこで一様可積分である。

### 補題の説明

有限個の層の微分の和は、生きているどの有限区間でも一様に有界なので、有限部分集合の族の全体が一様可積分です（A6′(ii)）。

### 証明の概略

1. 区間の測度は有限。
2. 各有限和は連続で可測、かつ 2 以下（`finiteCognitiveRate_bounds`）。
3. 一様に有界な可測関数の族は一様可積分（`uniformIntegrable_of_bound_two`）。

----

<a id="Tomabechi.Consistency.C2.c2_theorem23_nonrecurrence"></a>

## 定理 `c2_theorem23_nonrecurrence`

### 式

$$
t_1<t_2\Rightarrow\text{trajectory}(t_2)\ne\text{trajectory}(t_1)
$$

### Lean のコメント（日本語訳）

> 可算無限層の 15→23-A の入口を、具体的な完全状態の軌道に適用する。指定したモデルについての証人である。

### 補題の説明

可算無限層の定理15→23-A の入口を、具体的な完全状態の軌道に適用します。**軌道は決して元の状態に戻らない**（諸行無常）。指定したモデルについての証人です。

### 証明の概略

1. 定理15の可算無限層の入口（`theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence`）に、重みの正値性・意味エントロピーの非負性・軌道・生成率・生きている時間を渡す。
2. 区間での生成率の積分は \(b-a\)（定数の積分）で正。
3. A2・A5・A6′・A7 の前件は、このファイルの補題で供給する。

----

<a id="Tomabechi.Consistency.C2.production_integral"></a>

## 補題 `production_integral`

### 式

$$
\int_a^b\Pi=b-a
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生成率の積分は \(b-a\) です。

### 証明の概略

1. 定数の積分（`integral_const`）。

----

<a id="Tomabechi.Consistency.C2.production_strict"></a>

## 補題 `production_strict`

### 式

$$
a<b\Rightarrow\int_a^b\Pi>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生きている時間の区間では、生成の積分は正です。

### 証明の概略

1. 積分 \(=b-a>0\)。

----

<a id="Tomabechi.Consistency.C2.theorem15_23A_strict_production"></a>

## 補題 `theorem15_23A_strict_production`

### 式

$$
\int_a^b\Pi>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理15→23-A に必要な「厳密な生成」（積分が正）です。

### 証明の概略

1. `production_strict`。

----

<a id="Tomabechi.Consistency.C2.state_nonrepeats"></a>

## 補題 `state_nonrepeats`

### 式

$$
a<b\Rightarrow\text{trajectory}(a)\ne\text{trajectory}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は、異なる時刻で同じ状態にはなりません。

### 証明の概略

1. 同じ状態だと仮定すると、一般化エントロピーが等しい。ところが \(S=t+1\) なので \(a+1=b+1\)、\(a=b\) で矛盾。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
