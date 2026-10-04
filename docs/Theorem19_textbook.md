# Theorem19.lean 解説

> 対象: [`Theorem19.lean`](../Theorem19.lean)（定理19：ゴール条件付き制御容量の抽象核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19（**ゴール条件付き制御容量**）の抽象的な核です。「抽象度（束の元 \(a\)）ごとに、許容される問題・方策の組があり、それぞれにスコア（条件付き相互情報量）がある。その上限が**制御容量**で、抽象度が上がれば容量は減らない」ということを、**問題の型が抽象度ごとに違ってもよい**依存型の族に対して証明します（`Theorem22.lean`/`Capacity.lean` の、問題の型が共通の場合の拡張）。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `dependentLayerCapacity` | 型が抽象度ごとに異なる許容対のスコアの上限 |
| `dependentCapacity_nondecreasing_of_scorePreservingEmbedding` | 評価値を保つ単射な埋め込みで、容量は減らない |
| `bottom_top_capacity_bounds` | 最下位 \(0\) が最小、最上位 \(\top\) が最大の容量 |
| `zeroCapacity_of_zeroGoalEntropy` | ゴールのエントロピーが 0 なら容量も 0 |
| `endpointNormalization*`, `endpointAffine_unique` | 両端を 0 と 1 に固定するアフィン正規化（厳密増加・一意） |
| `admissibleProblemPolicyPairs`, `problemPolicy_doubleSup_eq_pairSup` | 問題・方策の二重の上限と、許容対の上限の同一視 |

### 0.3 このファイルが証明していないこと

- このファイルの抽象核は、「**容量を定理19の条件付き相互情報量（CMI）と同一視する**」ものではありません。CMI のスコア、問題ごとの分布・有限性の条件は、**入力データ**です。
- 容量の単調性は、層間の埋め込みが**評価値を保つ**という仮定から導きます。この仮定を論文のモデルで確かめることは別の作業です。
- スコアが非負・上に有界・許容集合が空でないことは、仮定として受け取ります。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理19：ゴール条件付き制御容量**
>
> 定理22にある、共通の型のスコア容量の API を、抽象度ごとに異なる問題の型をもつ、依存型の族へ拡張する。層間の単射・許容性・評価の保存から、容量の単調性を導き、束の端点、有限ゴールの条件付き相互情報量への適用、端点の正規化を整理する。このファイルの抽象核は、「容量を定理19の CMI と同一視する」ものではない。CMI のスコア、およびその問題ごとの分布・有限性の条件は、入力データである。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem19`。`open Tomabechi.Theorem22`。

---

<a id="Tomabechi.Theorem19.dependentLayerCapacity"></a>

## 定義 `dependentLayerCapacity`

### 式

$$\mathrm{cap}(a)=\sup\{\text{score}_a(x)\mid x\in\text{admissible}(a)\}\quad(x\in A_a)$$

### Lean のコメント（日本語訳）

> 各抽象度で問題の型自体が異なる、許容される問題・方策の対のスコアの上限。

### 定義の説明

`Capacity.lean` の `layerCapacity` の、問題の型 \(A_a\) が抽象度 \(a\) ごとに違う版です。

### 証明の概略

1. 定義：`sSup (score a '' admissible a)`。

----

<a id="Tomabechi.Theorem19.dependentCapacity_nondecreasing_of_scorePreservingEmbedding"></a>

## 補題 `dependentCapacity_nondecreasing_of_scorePreservingEmbedding`

### 式

$$a\le b,\ \text{score}_b(\iota(x))=\text{score}_a(x)\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 問題の型が異なる層でも、評価の値を保つ単射により、容量は減少しない。原文の 19 の単射の条件を保ち、問題の族・方策の族をまとめた対を `A a` とする。

### 補題の説明

抽象度が上がると、下の層の許容対を上の層の許容対へ（スコアを保って）埋め込めるので、上限（容量）は減りません。

### 証明の概略

1. 下の層のスコア集合の各元は、埋め込みで上の層のスコアとして実現されるので、上の層の上限以下。
2. `csSup_le` で下の層の上限も上の層の上限以下（15 行）。

----

<a id="Tomabechi.Theorem19.bottom_top_capacity_bounds"></a>

## 補題 `bottom_top_capacity_bounds`

### 式

$$\mathrm{cap}(\bot)\le\mathrm{cap}(a)\le\mathrm{cap}(\top)$$

### Lean のコメント（日本語訳）

> 原文の \(0\) と \(\top\) が、容量の最小値・最大値を与えることを、単調性から、端点の比較として述べる。

### 補題の説明

束の最下位 \(\bot\)（論文の 0）が容量の最小、最上位 \(\top\) が最大です。どんな抽象度 \(a\) も \(\bot\le a\le\top\) なので、単調性から従います。

### 証明の概略

1. `bot_le`・`le_top` と、上の単調性の補題を 2 回適用（9 行）。

----

<a id="Tomabechi.Theorem19.zeroCapacity_of_zeroGoalEntropy"></a>

## 補題 `zeroCapacity_of_zeroGoalEntropy`

### 式

$$0\le I\le H,\ H=0\ \Longrightarrow\ \sup I=0$$

### Lean のコメント（日本語訳）

> 物理層の全問題で、条件付きのゴールのエントロピーが零なら、各問題の \(I(G;Y|X)\le H(G|X)\) という情報の不等式から、容量も零となる。この抽象版では、有限ゴールの CMI の不等式と、零のエントロピーを明示的な入力にする。

### 補題の説明

「ゴールの不確かさがない（\(H=0\)）なら、得られる情報も 0」という、物理層（最下位）の容量が 0 になることの抽象版です。

### 証明の概略

1. 各スコアは \(0\le\text{score}\le\text{entropy}=0\) で 0。
2. 全部 0 なので上限も 0（非空・有界、`csSup_le` と `le_csSup`、11 行）。

----

<a id="Tomabechi.Theorem19.endpointNormalization"></a>

## 定義 `endpointNormalization`

### 式

$$\nu(x)=\frac{x-\mathrm{lo}}{\mathrm{hi}-\mathrm{lo}}$$

### Lean のコメント（日本語訳）

> 正の端点の差のもとでの、両端を固定するアフィンの正規化。

### 定義の説明

容量 \(x\) を、最小値 `lo` を 0、最大値 `hi` を 1 にする 1 次関数で規格化したものです。

### 証明の概略

1. 定義：`(x - lo) / (hi - lo)`。

----

<a id="Tomabechi.Theorem19.endpointNormalization_values"></a>

## 補題 `endpointNormalization_values`

### 式

$$\nu(\mathrm{lo})=0,\ \ \nu(\mathrm{hi})=1\quad(\mathrm{lo}<\mathrm{hi})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

端点がそれぞれ 0 と 1 に写ります。

### 証明の概略

1. 代入して計算（\(\mathrm{hi}-\mathrm{lo}\ne0\)、`div_self`）。

----

<a id="Tomabechi.Theorem19.endpointNormalization_strictMono"></a>

## 補題 `endpointNormalization_strictMono`

### 式

$$\mathrm{lo}<\mathrm{hi}\ \Longrightarrow\ \nu\ \text{は厳密増加}$$

### Lean のコメント（日本語訳）

> 両端の容量の差が正なら、原文 19 のアフィンの正規化は、容量の値について厳密に増加する。

### 補題の説明

正規化しても大小関係は保たれます（正の係数の 1 次関数）。

### 証明の概略

1. `div_lt_div_of_pos_right` など、分母が正の割り算の単調性。

----

<a id="Tomabechi.Theorem19.endpointAffine_unique"></a>

## 補題 `endpointAffine_unique`

### 式

$$f(x)=mx+c,\ f(\mathrm{lo})=0,\ f(\mathrm{hi})=1\ \Longrightarrow\ f=\nu$$

### Lean のコメント（日本語訳）

> 端点を 0 と 1 へ写すアフィン関数は一意である。正の容量を含む原文の正規化における、「一意」の内容を明示する。

### 補題の説明

端点を 0 と 1 に写す 1 次関数は 1 つしかありません（2 点を通る直線は一意）。

### 証明の概略

1. \(m\,\mathrm{lo}+c=0\)、\(m\,\mathrm{hi}+c=1\) から \(m=1/(\mathrm{hi}-\mathrm{lo})\)、\(c=-\mathrm{lo}/(\mathrm{hi}-\mathrm{lo})\)（`linarith`、19 行）。

----

<a id="Tomabechi.Theorem19.admissibleProblemPolicyPairs"></a>

## 定義 `admissibleProblemPolicyPairs`

### 式

$$\{(d,\pi)\mid d\in\text{problems},\ \pi\in\text{policies}(d)\}$$

### Lean のコメント（日本語訳）

> 問題 \(d\) と、その型に依存する方策 \(\pi\) の、許容対。各問題の方策の集合は、空でもよい。

### 定義の説明

問題 \(d\) と、その問題に対する許容な方策 \(\pi\) の組（依存和型 \(\Sigma\,d,\mathrm{Policy}(d)\) の部分集合）です。

### 証明の概略

1. 定義：`{q | q.1 ∈ problems ∧ q.2 ∈ policies q.1}`。

----

<a id="Tomabechi.Theorem19.problemPolicy_doubleSup_eq_pairSup"></a>

## 補題 `problemPolicy_doubleSup_eq_pairSup`

### 式

$$\sup_{d}\sup_{\pi}\text{score}(d,\pi)=\sup_{(d,\pi)}\text{score}(d,\pi)$$

### Lean のコメント（日本語訳）

> 原文 19 の、問題/方策の二重の上限と、許容対の上限の同一視。非負のスコア・全許容対の非空性・有限容量だけを使う。各問題の方策の非空性は要求せず、空の内側の集合の実数の `sSup`＝0 を、全体の容量の非負性で扱う。

### 補題の説明

「問題ごとに方策の上限をとり、それの問題についての上限をとる」二重の上限が、「組全体の上限」に等しい、という標準的な事実です。内側の集合が空のときの規約（Lean の `sSup ∅ = 0`）が問題になるので、スコアの非負性を使って処理します。

### 証明の概略

1. （\(\le\)）各問題の内側の上限は、その問題の許容対のスコアの上限以下（空なら 0、非負性で全体の上限以上）。
2. （\(\ge\)）各許容対のスコアは、その問題の内側の上限以下、したがって二重の上限以下（37 行）。

----


## コメント修正記録

（なし）
