# Theorem3.lean 解説

> 対象: [`Theorem3.lean`](../Theorem3.lean)（定理3：抽象的共有TCZへの収束（LUB表象））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理3（**抽象的な共有 TCZ への収束**）：各主体が、抽象度の**束**（完備束 \(L\)）の中のある元（その主体の「世界」）を表象し、全主体の世界の**最小上界（LUB）** \(L^\*=\bigvee_iW_i\) へ、各主体の表象が**指数的に近づく**ことを示します。定理2の共有残差 \(\Phi_2\) に、「LUB 表象への距離の 2 乗」（抽象残差）を重み \(\eta_i\) で加えた \(\Phi_3\) が指数的に散逸する、という条件のもとで成り立ちます。

束の元の間の距離は、束を**ユークリッド空間への順序埋め込み** \(\iota:L\hookrightarrow\mathbb R^m\) で測ります。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 座標空間とユークリッドノルム | `CoordinateSpace`, `euclideanCoordinateNorm*` |
| 抽象共有系 | `AbstractSharedSystem`, `lub`, `abstractResidual*`, `potential`, `statePotential`, `stateTCZ` |
| 定理2との接続 | `statePairSharedPotential` |
| 距離の指数評価 | `theorem3_two_distance_bounds_of_ac_ae_descent`, `..._tendsto_...` |
| 到達可能 TCZ での統合 | `theorem3_reachable_state_tcz_*` |
| LUB 表象の収束 | `weightedAbstractResidual_le_potential`, `abstractResidual_exponential_bound`, `lub_representation_exponential_convergence`, `lub_representation_tendsto` |

### 0.3 このファイルが証明していないこと

- **LUB 表象の実現可能性**、**零集合（共有 TCZ）の非空性**、**散逸**、**距離の誤差境界**は、**入力の条件**です。最適方策だけから導くとは主張しません（ファイル冒頭のコメントのとおり）。
- 主体の状態の型と束の元の型を同一視せず、`abstraction`（状態 → 束）と順序埋め込み `ι` を通じて接続します。異なる状態の型の間の比較は、明示的な写像（`stateMap`）に集約します。
- LUB 表象への収束（`lub_representation_*`）は、状態空間上の距離収束ではなく、**抽象表象だけ**の結論です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理3：抽象的な共有 TCZ への収束**
>
> 束の LUB と各主体の状態を、同じ型で扱わず、束への写像と順序埋め込みを通じて、抽象残差を定義する。定理2型の共有残差に、抽象残差を正の重みで加えた Lyapunov 量の指数散逸を条件として、各主体の LUB 表象への定量的な収束を示す。LUB 表象の実現可能性、零集合の非空性、散逸および距離の誤差境界は、入力の条件であり、最適方策だけから導くとは主張しない。

名前空間は `Tomabechi.Theorem3`。`open Filter`。

---

<a id="Tomabechi.Theorem3.CoordinateSpace"></a>

## 定義 `CoordinateSpace`

### 式

$$\mathbb R^m=\{x:\mathrm{Fin}\ m\to\mathbb R\}$$

### Lean のコメント（日本語訳）

> 抽象度の束の元を、Euclid 空間へ埋め込む。

### 定義の説明

束の元を座標のベクトルとして表す空間です（成分ごとの順序をもつ）。

### 証明の概略

1. 定義：`Fin m → ℝ` の別名。

----

<a id="Tomabechi.Theorem3.euclideanCoordinateNorm"></a>

## 定義 `euclideanCoordinateNorm`

### 式

$$\|x\|_2=\sqrt{\textstyle\sum_ix_i^2}$$

### Lean のコメント（日本語訳）

> 座標の関数の型の上の、Euclid ノルム。`CoordinateSpace` は、順序の埋め込みが必要とする成分ごとの順序を保ち、この明示的なノルムは、既定の Pi の sup ノルムではなく、`EuclideanSpace ℝ (Fin m)` に一致する。

### 定義の説明

通常の長さ（2 乗和の平方根）です。`Fin m → ℝ` の既定のノルムは最大値ノルムなので、別に定義します。

### 証明の概略

1. 定義：`Real.sqrt (∑ i, x i ^ 2)`。

----

<a id="Tomabechi.Theorem3.euclideanCoordinateNorm_nonneg"></a>

## 補題 `euclideanCoordinateNorm_nonneg`

### 式

$$\|x\|_2\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平方根は非負です。

### 証明の概略

1. `Real.sqrt_nonneg`。

----

<a id="Tomabechi.Theorem3.euclideanCoordinateNorm_eq_zero_iff"></a>

## 補題 `euclideanCoordinateNorm_eq_zero_iff`

### 式

$$\|x\|_2=0\ \Longleftrightarrow\ x=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

長さが 0 なのは零ベクトルだけです。

### 証明の概略

1. 平方根が 0 ⇔ 中身が 0、2 乗和が 0 ⇔ 各成分が 0。

----

<a id="Tomabechi.Theorem3.euclideanCoordinateNorm_eq_EuclideanSpace_norm"></a>

## 補題 `euclideanCoordinateNorm_eq_EuclideanSpace_norm`

### 式

$$\|x\|_2=\|x\|_{\mathbb R^m}$$

### Lean のコメント（日本語訳）

> この明示的な座標の公式は、\(\mathbb R^m\) の通常の Euclid 空間の構造が使うノルムとちょうど同じである。

### 補題の説明

定義したノルムが、Mathlib の `EuclideanSpace` のノルムと一致することの確認です。

### 証明の概略

1. `EuclideanSpace.norm_eq`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem"></a>

## 構造体 `AbstractSharedSystem`

### 式

$$\text{State}_i,\ \ \text{abstraction}_i:\text{State}_i\to L,\ \ W_i\in L,\ \ \iota:L\hookrightarrow\mathbb R^m\ (\text{順序埋め込み})$$

### Lean のコメント（日本語訳）

> 有限主体の状態・抽象の写像・世界のラベル・表象の埋め込みをもつ、型つきのデータ。`lub` は、全世界のラベルの束の上の上限である。

### 定義の説明

主体 \(i\)（有限個）の状態の型、状態から束への抽象化の写像 `abstraction`、各主体の世界 `worlds`（束の元）、束から座標空間への順序埋め込み \(\iota\) をまとめた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.lub"></a>

## 定義 `lub`

### 式

$$L^\*=\bigvee_iW_i$$

### Lean のコメント（日本語訳）

> 原文の \(L^\*=\bigvee_iW_i\)。

### 定義の説明

全主体の世界の最小上界（束の上限）です。

### 証明の概略

1. 定義：`⨆ i, D.worlds i`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual"></a>

## 定義 `abstractResidual`

### 式

$$A_i(x_i)=\|\iota(\text{abstraction}_i(x_i))-\iota(L^\*)\|_2^2$$

### Lean のコメント（日本語訳）

> LUB 表象への 2 乗距離。状態の型と束の要素の型は、`abstraction` と \(\iota\) を介して接続する。

### 定義の説明

主体 \(i\) の表象が、全体の LUB \(L^\*\) からどれだけ離れているか（2 乗距離）です。

### 証明の概略

1. 定義：`euclideanCoordinateNorm (D.ι (D.abstraction i x) - D.ι D.lub) ^ 2`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual_nonneg"></a>

## 補題 `abstractResidual_nonneg`

### 式

$$A_i\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

2 乗なので非負です。

### 証明の概略

1. `sq_nonneg`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual_eq_zero_iff"></a>

## 補題 `abstractResidual_eq_zero_iff`

### 式

$$A_i=0\ \Longleftrightarrow\ \text{abstraction}_i(x_i)=L^\*$$

### Lean のコメント（日本語訳）

> 抽象残差が零であることは、束の表象が LUB そのものに等しいことと同値である。

### 補題の説明

距離 0 ⇔ 表象が LUB に一致（\(\iota\) の単射性）。

### 証明の概略

1. ノルムが 0 ⇔ 差が零ベクトル、順序埋め込みの単射性（`OrderEmbedding.injective`）。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.potential"></a>

## 定義 `potential`

### 式

$$\Phi_3(t)=\Phi_2(t)+\sum_i\eta_i\,A_i(x_i(t))$$

### Lean のコメント（日本語訳）

> 共有 Lyapunov 量に LUB の残差を加えた、定理3の総残差。

### 定義の説明

共有残差 \(\Phi_2\)（定理2）に、各主体の LUB 表象への距離の 2 乗を重み \(\eta_i\) で加えたものです（軌道に沿ったスカラー関数）。

### 証明の概略

1. 定義：`shared t + ∑ i, η i * D.abstractResidual i (trajectory i t)`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.statePotential"></a>

## 定義 `statePotential`

### 式

$$\Phi_3(x,t)=\Phi_2(x,t)+\sum_i\eta_iA_i(x_i)$$

### Lean のコメント（日本語訳）

> 状態の上で定義した、定理3の総残差 \(\Phi_3(x,t)=\Phi_2(x,t)+\sum_i\eta_iA_i(x_i)\)。軌道に沿うスカラー関数だけでなく、TCZ を定義する状態の関数としても保持する。

### 定義の説明

上の `potential` を、状態 \(x\) の関数として定義したものです（TCZ の定義に使う）。

### 証明の概略

1. 定義：同じ形。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.stateTCZ"></a>

## 定義 `stateTCZ`

### 式

$$\{x\in K\mid\Phi_3(x,t)=0\}$$

### Lean のコメント（日本語訳）

> 閉の到達可能な領域内の、定理3の共有 TCZ。零条件は、状態の上の同じ \(\Phi_3\) を使う。

### 定義の説明

\(\Phi_3=0\)（全員が共有 TCZ にあり、表象が LUB に一致）となる状態の集合です。

### 証明の概略

1. 定義：`{x ∈ K | D.statePotential .. x t = 0}`。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.statePairSharedPotential"></a>

## 定義 `statePairSharedPotential`

### 式

$$\Phi_2^{(3)}(x,t)=\Phi_2^{\text{Thm2}}(\text{stateMap}(x),t)$$

### Lean のコメント（日本語訳）

> 定理3の状態を、明示的な写像で定理2の状態へ移し、正準の共有残差 \(\Phi_2\) を評価する。異なる状態の型の間の比較は、この写像に集約し、根拠のない型の同一視を避ける。

### 定義の説明

定理2の共有残差を、定理3の状態の関数として使うための橋です（状態の型の違いを `stateMap` で吸収）。

### 証明の概略

1. 定義：定理2の `StatePairResidualSystem.potential` を `stateMap` で引き戻す。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.theorem3_two_distance_bounds_of_ac_ae_descent"></a>

## 定理 `theorem3_two_distance_bounds_of_ac_ae_descent`

### 式

$$\operatorname{dist}(x(t),\text{sharedTCZ})\le\sqrt{C\Phi_3(t_0)}e^{-c(t-t_0)},\ \ \|\iota(\text{abstraction}_i(x_i(t)))-\iota(L^\*)\|_2\le\sqrt{\tfrac{\Phi_3(t_0)}{\eta_i}}e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 絶対連続性・a.e. の下降と、共有の零集合の距離の誤差境界から、同じ総残差 \(\Phi_3\) を使って、共有 TCZ への状態距離と、LUB 表象の距離の両方に指数の評価を与える、定理3の有限時間の合成。指数の包絡そのものは仮定せず、定理1の比較の核から導く。

### 補題の説明

**定理3の主結論（有限時間）**：状態の距離（共有 TCZ へ）と、各主体の LUB 表象への距離が、どちらも速さ \(c\) で指数的に減ります。指数散逸を仮定せず、絶対連続性と a.e. 下降から導きます。

### 証明の概略

1. 総残差 \(\Phi_3\) は共有残差と \(\sum_j\eta_jA_j\) の和で、各項が非負なので \(\Phi_3\ge0\)。
2. 定理1の `lyapunov_exponential_decay_of_ac_ae_derivative` で \(\Phi_3(t)\le\Phi_3(t_0)e^{-2c(t-t_0)}\)。
3. 状態距離：`individual_tcz_distance_decay_of_ac_ae_derivative`（共有 TCZ への距離の指数評価）。
4. LUB 表象への距離：\(\eta_iA_i\le\Phi_3\)（和の 1 項）と `Theorem2.component_exponential_bound` から \(A_i\le\frac{\Phi_3(t_0)}{\eta_i}e^{-2c(t-t_0)}\)。\(\|\iota(\varphi_i(x_i))-\iota(L^\ast)\|=\sqrt{A_i}\) として平方根をとる（74 行）。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent"></a>

## 定理 `theorem3_two_distances_tendsto_of_ac_ae_descent`

### 式

$$\begin{aligned}
&\Phi_3=\Phi_{\rm shared}+\sum_j\eta_jA_j\ \ (A_j=\|\iota(\varphi_j(x_j))-\iota(L^\ast)\|^2),\quad \eta_i>0,\ c,C>0\\
&\forall T\ge t_0:\ \Phi_3\ \text{が }[t_0,T]\text{ で AC},\ \Phi_3'\le-2c\Phi_3\ \text{a.e.},\quad
\forall s\ge t_0:\ \mathrm{dist}(x(s),\Omega_3(s))^2\le C\,\Phi_3,\ \Omega_3(s)\ne\emptyset\\
&\Longrightarrow\ \ \mathrm{dist}(x(s),\Omega_3(s))\to0\ \ \wedge\ \ \|\iota(\varphi_i(x_i(s)))-\iota(L^\ast)\|\to0\quad(s\to\infty)
\end{aligned}$$
（\(L^\ast=\)LUB。収束は仮定した下降・誤差境界から導く条件付き結論。）

### Lean のコメント（日本語訳）

> 各終端時刻での原文の条件を、状態距離と、LUB 表象の距離の、大域的な指数収束へ繋ぐ。指数散逸は入口に置かず、各有限区間の AC・a.e. の下降から、比較の補題で導く。

### 補題の説明

`t → ∞` での収束版です。

### 証明の概略

1. 上の定理と `exponential_envelope_tendsto_zero`（Theorem2）。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.theorem3_reachable_state_tcz_quantitative_conclusion"></a>

## 定理 `theorem3_reachable_state_tcz_quantitative_conclusion`

### 式

$$\text{閉到達可能 TCZ（}\Phi_3=0\text{）への距離・LUB 表象の距離の指数評価と極限}$$

### Lean のコメント（日本語訳）

> 状態の上の総残差から、閉の到達可能な TCZ を作り、同じ \(\Phi_3\) の散逸から、共有の状態距離・LUB 表象の距離の定量的な評価と、極限を得る、定理3の統合の入口。`sharedAt` は、原文の共有残差 \(\Phi_2\) を、状態と時刻の関数として与える。

### 補題の説明

到達可能集合の閉包を領域 \(K\) にした統合版です。

### 証明の概略

1. 定理1の `closedLoopReachableSet` を \(K\) として、上の 2 つの定理を適用。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.theorem3_reachable_state_tcz_from_statePairSystem"></a>

## 定理 `theorem3_reachable_state_tcz_from_statePairSystem`

### 式

$$\text{定理2の}\ \Phi_2\ \text{を}\ \text{stateMap}\ \text{で引き戻した}\ \Phi_3\ \Longrightarrow\ \text{指数評価・両極限}$$

### Lean のコメント（日本語訳）

> P1→P2 の、状態の型つきの接続。定理2の正準の `StatePairResidualSystem.potential` を、明示的な状態の写像で、定理3の状態へ引き戻して \(\Phi_2\) とし、同じ \(\Phi_3\) の零集合を目標に、指数の評価と、両方の極限を得る。写像そのものの、原文のモデルの上での構成は、別途、入力として残る。

### 補題の説明

定理2（状態対版）と定理3を実際に接続した統合定理です。

### 証明の概略

1. `statePairSharedPotential` を `sharedAt` として、`theorem3_reachable_state_tcz_quantitative_conclusion` を適用。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.weightedAbstractResidual_le_potential"></a>

## 補題 `weightedAbstractResidual_le_potential`

### 式

$$\eta_iA_i\le\Phi_3$$

### Lean のコメント（日本語訳）

> 共有項と抽象残差の項が非負なら、総残差が、各重み付きの抽象残差を支配する。

### 補題の説明

総残差は、各主体の（重み付き）抽象残差以上です。

### 証明の概略

1. 非負項の和は各項以上（`Finset.single_le_sum`）。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.abstractResidual_exponential_bound"></a>

## 補題 `abstractResidual_exponential_bound`

### 式

$$A_i(x_i(t))\le\frac{\text{initialBound}}{\eta_i}e^{-2c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 共有残差の散逸から、LUB の埋め込み空間での、各主体の 2 乗距離の、明示的な指数の上界を得る。正の重み・非負性・指数散逸を、仮定として保つ。

### 補題の説明

各主体の LUB 表象への距離の 2 乗が指数的に減ります。

### 証明の概略

1. `weightedAbstractResidual_le_potential` と指数散逸、重み \(\eta_i>0\) で割る。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.lub_representation_exponential_convergence"></a>

## 定理 `lub_representation_exponential_convergence`

### 式

$$\|\iota(\text{abstraction}_i(x_i(t)))-\iota(L^\*)\|_2\le\sqrt{\tfrac{\text{initialBound}}{\eta_i}}\,e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 原文の主要な結論：LUB の順序埋め込みの表象への距離が、指数率 \(c\) で減衰する。これは、状態空間の上の距離の収束を主張せず、原文の型つきの抽象表象だけを結論する。

### 補題の説明

**定理3の核心**：各主体の（抽象）表象が、全員の世界の最小上界 \(L^\*\) へ速さ \(c\) で指数収束します。

### 証明の概略

1. 上の補題の平方根をとる（`Real.sqrt_le_sqrt`、`Real.sqrt_mul_self` など）。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.lub_representation_tendsto"></a>

## 定理 `lub_representation_tendsto`

### 式

$$\|\iota(\text{abstraction}_i(x_i(t)))-\iota(L^\*)\|_2\to0\ (t\to\infty)$$

### Lean のコメント（日本語訳）

> 指数の評価から、原文に記された \(t\to\infty\) の、LUB 表象の収束を得る。

### 補題の説明

指数の包絡で抑えられるので 0 に収束します。

### 証明の概略

1. `exponential_envelope_tendsto_zero`（Theorem2）。

----


## コメント修正記録

（なし）
