# Theorem15.lean 解説

> 対象: [`Theorem15.lean`](../Theorem15.lean)（定理15(I)：A2/A5/A6′/A7 から一般化エントロピーの積分収支へ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| Tendsto | 関数の極限を表す Lean の述語 `Filter.Tendsto`。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| Vitali の収束定理 | 一様可積分かつ a.e. 収束するなら \(L^1\) 収束する。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理15（エントロピー収支）の**積分形**を証明するファイルです。物理エントロピーと、可算個の認知層のエントロピーの重み付き和（一般化エントロピー）について、

$$S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int_a^b\Pi_{\text{gen}}(t)\,dt,\qquad \int_a^b\Pi_{\text{gen}}\ge0$$

を、論文の仮定 **A2・A5・A6′・A7** から導きます（`EntropyBalance.lean` の部品を使い、定理23の入口に接続します）。

### 0.2 仮定の対応

| 記号 | 内容 | このファイルでの形 |
| --- | --- | --- |
| A2 | 各認知層のエントロピーが（時間の関数として）絶対連続 | `hA2` |
| A5 | 物理エントロピーが絶対連続 | `hA5` |
| A6′(i) | 各時刻で重み付き層エントロピーの和が有限（総和可能） | `hA6finiteA/B`（軌道上の各時刻） |
| A6′(ii) | 有限な層の部分集合の族について、生成率の和が**一様可積分**、列挙の prefix 列は a.e. 収束 | `hA6UI`, `hA6ae` |
| A7 | 閉じた系の交換式：\(\Pi_{\text{phys}}=-\sum_\ell w_\ell\Pi_\ell+\Pi_{\text{tot}}\)、総生成率は非負 | `hA7`, `hA7nonnegative` |

### 0.3 証明の流れ

1. 有限の層の部分和について、A2/A5 から**端点の収支**を導く（有限段ごと）。
2. A6′ の一様可積分性（全有限部分集合の族）を、列挙の prefix 列へ制限する（量化の制限）。
3. Vitali の定理で、生成率の部分和が \(L^1\) 収束し、極限へ収支を移す（`EntropyBalance.lean`）。
4. A7 で、極限の生成率を総生成率に同定する。

### 0.4 このファイルが証明していないこと

- **A7（交換式）と符号条件**は、**独立した仮定**として入力します。物理的な導出は目標に含めません（ファイル冒頭のコメントのとおり）。
- **A6′** の各部分は、論文の再掲版（認知宇宙論 §3.7）と、自由エネルギー論文の別版とで、量化（各時刻 vs 初期時刻のみ）が異なります。主定理では A6′(i) を**軌道の各時刻での総和可能性**として、A6′(ii) を**全有限部分集合族の一様可積分性**として表現します。
- 条件 23-A（厳密な正値性）はここでは扱いません（`Theorem15_23.lean`）。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理15(I)：A6′ 型の Vitali 極限から、一般化エントロピーの収支へ**
>
> このモジュールは、定理15の積分形を、定理23の収支の入口に接続する。物理エントロピーと認知層の端点の部分和の収支は、A2/A5 から有限段ごとに導き、A6′ 型の一様可積分性・a.e. 収束で、極限へ移す。A7 の交換式と符号条件は、入力の仮定として保持する。
>
> **原文の監査**：認知宇宙論 §3.7 の A6′(i) は各時刻での総和の有限性であり、自由エネルギー論文の別版では初期時刻での有限性で、量化が異なる。主定理では、A6′(i) を軌道の各時刻での総和可能性として表現し、A6′(ii) の全有限部分集合族から、列挙の prefix 列の一様可積分性を導く。A7 の物理・認知の交換式自体は証明せず、独立の仮定として用いる。

（もとのコメントが日本語なのでそのまま写しています。コメント中の「原文」は、苫米地論文を指します。）名前空間は `Tomabechi.Theorem15`。`open Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem15.A6PrimeIntervalData"></a>

## 構造体 `A6PrimeIntervalData`

### 式

$$\text{measurable},\ \ \text{UniformIntegrable}\ (L^1),\ \ \Pi_n(t)\to\Pi(t)\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 固定された有限の時間測度についての A6′ 型のデータ：列挙された有限の生成の和は一様可積分で、完全な重み付きの層の生成率に、ほとんど至るところで収束する。

### 定義の説明

A6′ の「極限への移行に必要な 3 条件」を束ねた命題（`Prop`）です：(i) 各部分和が可測、(ii) 一様可積分、(iii) a.e. 収束。Vitali の定理を使う条件です。

### 証明の概略

1. 構造体（命題）なので証明はない。

----

<a id="Tomabechi.Theorem15.uniformIntegrable_prefix_of_finiteFamily"></a>

## 補題 `uniformIntegrable_prefix_of_finiteFamily`

### 式

$$\{\Pi_s\}_{s\subset\text{Layer finite}}\ \text{一様可積分}\ \Longrightarrow\ \{\Pi_{\text{prefix}_n}\}_n\ \text{一様可積分}$$

### Lean のコメント（日本語訳）

> A6′ は、すべての有限の層の部分集合について、一様可積分性を量化する。その族を、有限の prefix の任意の列挙に沿って制限しても、一様可積分性は保たれる。これは、既存の列についての Vitali の定理が必要とする、量化の制限を、ちょうど包む。

### 補題の説明

「すべての有限部分集合の族」が一様可積分なら、その部分族（prefix の列）も一様可積分です（部分族は、元の族の定数・条件をそのまま満たす）。

### 証明の概略

1. 一様可積分性の定義（可測性と、\(\forall\varepsilon\,\exists\delta\) の条件 `unifIntegrable_iff`、\(L^1\) の有界性）を、部分族へ制限する（14 行）。

----

<a id="Tomabechi.Theorem15.uniformIntegrable_add_fixed_rate"></a>

## 補題 `uniformIntegrable_add_fixed_rate`

### 式

$$\{\Pi_s\}\ \text{一様可積分},\ \Pi_{\text{phys}}\in L^1\ \Longrightarrow\ \{\Pi_{\text{phys}}+\Pi_s\}\ \text{一様可積分}$$

### Lean のコメント（日本語訳）

> 固定された物理の生成率を、有限の認知の部分和のすべてに加えても、一様可積分性は保たれる。物理の生成率についての `MemLp` の前提は、A5 の絶対連続性のデータと、その導関数の有限区間での可積分性から従う。

### 補題の説明

1 つの可積分関数（定数の族）を足しても、一様可積分性は保たれます（可積分関数の定数の族は一様可積分）。

### 証明の概略

1. 可積分関数の定数の族は一様可積分（`uniformIntegrable_const`）。
2. 一様可積分な族の和は一様可積分（`UniformIntegrable.add`）。族の \(L^1\) 有界性は \(C_1+C_2\)（19 行）。

----

<a id="Tomabechi.Theorem15.uniformIntegrable_enumerated_total_prefix_of_A6Prime"></a>

## 補題 `uniformIntegrable_enumerated_total_prefix_of_A6Prime`

### 式

$$\text{A6′(ii)}\ \Longrightarrow\ \{\Pi_{\text{phys}}+\Pi_{\text{prefix}_n}\}_n\ \text{一様可積分}$$

### Lean のコメント（日本語訳）

> 任意の有限の部分集合についての A6′ の一様可積分性の前提は、したがって、物理の生成率を加えたあと、認知の prefix の任意の列挙された列について、一様可積分性を与える。

### 補題の説明

上の 2 つの補題の組み合わせです：全有限部分集合族の一様可積分性 ⇒ prefix 列の一様可積分性 ⇒ 物理の生成率を足しても一様可積分。

### 証明の概略

1. `uniformIntegrable_prefix_of_finiteFamily` で prefix 列に制限。
2. `uniformIntegrable_add_fixed_rate` で物理の生成率を足す（9 行）。

----

<a id="Tomabechi.Theorem15.sum_fin_enumeration_eq_sum_image"></a>

## 補題 `sum_fin_enumeration_eq_sum_image`

### 式

$$\sum_{i<n}f(e(i))=\sum_{a\in e(\{0,\dots,n-1\})}f(a)$$

### Lean のコメント（日本語訳）

> 列挙の最初の \(n\) 項を並べ替えることは、その像の有限集合についての和を取ることと、ちょうど同じである。

### 補題の説明

列挙 \(e:\mathbb N\simeq\text{Layer}\) の最初の \(n\) 個の層についての和は、その像（有限集合）についての和に一致します。

### 証明の概略

1. `Finset.sum_bij`（全単射 \(i\mapsto e(i)\) による和の並べ替え）、単射性は列挙の単射性（15 行）。

----

<a id="Tomabechi.Theorem15.enumerated_tsum_partial_tendsto_of_summable"></a>

## 補題 `enumerated_tsum_partial_tendsto_of_summable`

### 式

$$\text{Summable }f\ \Longrightarrow\ \sum_{i<n}f(e(i))\to\sum'_{a}f(a)$$

### Lean のコメント（日本語訳）

> 層のエントロピーの項の点ごとの総和可能性は、それらの列挙された有限和の端点の収束を与える。これは A6′(i) の軌道に局所的な形であり、軌道から外れた状態での総和可能性を必要としない。

### 補題の説明

総和可能な級数は、列挙の順で足した部分和が総和に収束します（並べ替えても和は同じ）。`EntropyBalance.lean` の `enumerated_partial_total_entropy_tendsto` と同様です。

### 証明の概略

1. 列挙で並べ替えた級数も総和可能で、`tsum` が等しい（`Equiv.tsum_eq`）。
2. 部分和の収束（`HasSum.tendsto_sum_nat`、11 行）。

----

<a id="Tomabechi.Theorem15.theorem15_trajectory_integral_balance"></a>

## 定理 `theorem15_trajectory_integral_balance`

### 式

$$S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int_a^b\Pi_{\text{tot}}\,dt\ \ \wedge\ \ \int_a^b\Pi_{\text{tot}}\ge0$$

### Lean のコメント（日本語訳）

> 定理15(I) の、軌道に局所的な、エンドツーエンドの形。A2/A5 を絶対連続性として、A6′(i) を各軌道の時刻での総和可能性として、A6′(ii) を**すべての**有限の層の部分集合についての一様可積分性と、a.e. の prefix 収束として、A7 を非負で可積分な生成率つきの交換式として符号化する（可積分性は Vitali から従う）。軌道から外れた状態での大域的な総和可能性は要らない。

### 補題の説明

**定理15(I) の主定理**（可算層）：軌道上の端点 \(a,b\) での総和可能性（A6′(i)）、有限部分集合族の一様可積分性（A6′(ii)）、prefix 列の a.e. 収束、交換式 A7 から、一般化エントロピーの端点の差が総生成率の積分に等しく、積分が非負であることを示します。

### 証明の概略

1. 有限測度 \(\mu=\mathrm{volume}|_{(a,b]}\) を取る。物理・各層のエントロピーの導関数は、A2/A5 の絶対連続性から区間可積分。
2. A6′(ii) の「全有限部分集合の和の一様可積分性」から、列挙した層の prefix 和の列に、物理の項を足したものの一様可積分性を得る（`uniformIntegrable_enumerated_total_prefix_of_A6Prime`）。
3. A6′(i) の a.e. 収束と A7 の打ち消し \(\sigma_{\rm phys}+\sum w\pi=\Pi\) から、部分和の生成率が a.e. で総生成率 \(\Pi\) に収束することを示す。
4. 両端点の層和が総和可能なので、部分和のエントロピーが両端点で総エントロピーに収束する（`enumerated_tsum_partial_tendsto_of_summable`）。
5. 各 \(n\) の有限層の収支は、A2/A5 の導関数から `finite_layer_entropy_balance_of_component_derivatives`（Theorem23）で得る。
6. 一様可積分性・a.e. 収束・端点の極限を `countable_layer_entropy_balance_of_uniformIntegrable`（Theorem23、Vitali の収束定理）に渡して、\(S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\) を得る（183 行）。

----

<a id="Tomabechi.Theorem15.theorem15_finite_layer_integral_balance"></a>

## 定理 `theorem15_finite_layer_integral_balance`

### 式

$$\text{有限層}:\ S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int_a^b\Pi_{\text{tot}}\ \wedge\ \int\Pi_{\text{tot}}\ge0$$

### Lean のコメント（日本語訳）

> 定理15(I) の有限層の形。有限の部分和の極限は自明であり、A2/A5 の成分ごとの収支と、有限の A7 の交換式が、同じ一般化エントロピー生成の収支を与える。これは、上の可算無限の定理を補う。

### 補題の説明

層が有限個の場合は、列挙も Vitali の極限も要りません（部分和が全体）。`EntropyBalance.lean` の有限層の収支を使います。

### 証明の概略

1. `finite_layer_entropy_balance_of_component_derivatives`（EntropyBalance）で総収支。
2. A7 で生成率を総生成率に置き換え、非負性を a.e. 非負の積分として得る（65 行）。

----

<a id="Tomabechi.Theorem15.generalized_rate_tendsto_of_A7"></a>

## 補題 `generalized_rate_tendsto_of_A7`

### 式

$$\Pi_{\text{cog},n}\to\Pi_{\text{cog}},\ \ \Pi_{\text{phys}}=-\Pi_{\text{cog}}+\Pi_{\text{tot}}\ \Longrightarrow\ \Pi_{\text{phys}}+\Pi_{\text{cog},n}\to\Pi_{\text{tot}}\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> A7 の交換の恒等式は、有限の認知の生成率の prefix の収束を、有限の一般化生成率の収束に変える。交換式は、論文の定理のとおり、明示的なほとんど至るところの前提のまま残る。

### 補題の説明

A7 を使うと、物理の生成率に認知の部分和を足した量の極限が、総生成率になります。

### 証明の概略

1. a.e. の各点で、`Tendsto.const_add` と A7 の書き換え（8 行）。

----

<a id="Tomabechi.Theorem15.generalized_entropy_balance_of_A6Prime"></a>

## 補題 `generalized_entropy_balance_of_A6Prime`

### 式

$$\text{有限段の収支}\ +\ \text{A6′}\ +\ \text{端点の収束}\ \Longrightarrow\ S(b)-S(a)=\int\Pi$$

### Lean のコメント（日本語訳）

> すべての有限層の打ち切りが、その積分された収支に従うなら、A6′ の Vitali の条件は、完全な一般化エントロピーの収支を与える。これは、定理23が使う一般的な積分形の橋である。上のエンドツーエンドの軌道の定理は、有限の収支を A2/A5 から導き、A6′/A7 の生成率の収束と、prefix の一様可積分性の前提を与える。

### 補題の説明

`EntropyBalance.lean` の `countable_layer_entropy_balance_of_uniformIntegrable` と同じ内容を、`A6PrimeIntervalData` を使った形で述べたものです。

### 証明の概略

1. `A6PrimeIntervalData` から、可測性・一様可積分性・a.e. 収束を取り出し、`countable_layer_entropy_balance_of_uniformIntegrable`（EntropyBalance）を適用（6 行）。

----

<a id="Tomabechi.Theorem15.model_generalized_entropy_balance_of_A6Prime"></a>

## 補題 `model_generalized_entropy_balance_of_A6Prime`

### 式

$$\text{GeneralizedEntropyModel}\ +\ \text{A6′}\ +\ \text{有限段の収支}\ \Longrightarrow\ S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int\Pi$$

### Lean のコメント（日本語訳）

> モデルに特有の版：重み付きの層のエントロピーの級数の点ごとの絶対収束が端点の極限を与え、有限の打ち切りの収支と A6′ のデータが、区間の収支を与える。

### 補題の説明

`GeneralizedEntropyModel`（`EntropyBalance.lean`）では総和可能性がモデルのフィールドなので、端点の収束は自動的に成り立ちます。

### 証明の概略

1. `enumerated_countable_layer_entropy_balance_of_uniformIntegrable`（EntropyBalance）を、`A6PrimeIntervalData` から適用（5 行）。

----

<a id="Tomabechi.Theorem15.theorem15_integral_balance_of_A2_A5_A6Prime_A7"></a>

## 定理 `theorem15_integral_balance_of_A2_A5_A6Prime_A7`

### 式

$$\begin{aligned}
&\text{A2: }S_{\rm phys},H_k\ \text{が }[a,b]\text{ で AC（導関数 a.e. が }\dot S_{\rm phys}=\sigma_{\rm phys},\ \dot H_k=\pi_k\text{）}\\
&\text{A6′(ii): }\bigl\{\textstyle\sum_{k\in s}w_k\pi_k\bigr\}_{s\text{ 有限}}\ \text{が }[a,b]\text{ 上で一様可積分},\quad
\text{A6′(i): }\textstyle\sum_{i<n}w_{e(i)}\pi_{e(i)}\to\sum_k w_k\pi_k\ \text{a.e.}\\
&\text{A7: }\sigma_{\rm phys}=-\textstyle\sum_kw_k\pi_k+\Pi\ \text{a.e.},\qquad \Pi\ge0\ \text{a.e.}\\
&\Longrightarrow\ S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\,dt\ \ \wedge\ \ \int_a^b\Pi\,dt\ge0
\end{aligned}$$
（\(S_{\rm gen}=S_{\rm phys}+\sum_kw_kH_k\)。A7 は原文の独立公理で、ここでは導出せず仮定。）

### Lean のコメント（日本語訳）

> 有限区間上の定理15(I)：成分ごとの A2/A5 の正則性、任意の有限部分集合についての A6′ の仮定、A7 の交換式から。有限の収支は成分の導関数から生成される。A6′ の一様可積分性は、まずすべての有限の部分集合から、列挙の prefix に制限される。A7 は、それらの a.e. の生成率の極限を、物理の総生成と同一視する。

### 補題の説明

上の `theorem15_trajectory_integral_balance` を、`GeneralizedEntropyModel`（`EntropyBalance.lean`）のモデルの言葉で述べた版です。

### 証明の概略

1. `GeneralizedEntropyModel` の言葉で、`theorem15_trajectory_integral_balance` と同じ筋の議論を行う（この定理自体は、それを呼ぶのではなく、モデルのフィールドを使って再構成する）：A6′ のデータ `A6PrimeIntervalData` から prefix 和の一様可積分性（`uniformIntegrable_enumerated_total_prefix_of_A6Prime`）。
2. A7 から部分和の生成率の a.e. 極限（`generalized_rate_tendsto_of_A7`）、有限層の収支は `enumerated_partial_entropy_balance_of_component_derivatives`（Theorem23）、区間積分と制限測度の積分の一致は `intervalIntegral_eq_integral_restrict_Ioc`。
3. これらを `model_generalized_entropy_balance_of_A6Prime` に渡して総収支を得て、散逸の非負性から積分が非負（149 行）。

----


## コメント修正記録

（なし）
