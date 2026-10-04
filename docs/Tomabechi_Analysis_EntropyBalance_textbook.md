# Tomabechi/Analysis/EntropyBalance.lean 解説

> 対象: [`Tomabechi/Analysis/EntropyBalance.lean`](../Tomabechi/Analysis/EntropyBalance.lean)（定理15(I)・23 の共有エントロピー収支（一般化エントロピー・非再帰））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| Vitali の収束定理 | 一様可積分かつ a.e. 収束するなら \(L^1\) 収束する。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（無常：**エントロピーが厳密に増え、完全な状態は二度と繰り返さない**）の中心になる、**エントロピー収支**の解析ファイルです。定理15（エントロピー収支）と定理23が共用する部品として分離されています。

- 一般化エントロピー \(S_{\text{gen}}=S_{\text{phys}}+\sum_\ell w_\ell S_\ell\)（物理エントロピー＋層ごとのエントロピーの重み付き和）を定義します。
- 微分形の収支 \(S_{\text{gen}}'=\Pi_{\text{gen}}\) と、第二法則（生成率 \(\Pi_{\text{gen}}\ge0\)）から、端点のエントロピー差を**生成率の積分**に等置します。
- 条件 23-A（生存区間では生成率の積分が**厳密に正**）のもとで、エントロピーは厳密増加し、したがって**完全状態は繰り返さない**（非再帰）ことを示します。

### 0.2 構成

| 節 | 内容 |
| --- | --- |
| 1. 基本の収支 | 区間積分と測度、絶対連続性＋a.e. 微分 ⇒ 端点の収支、第二法則 ⇒ 非負、非再帰（一般の完全状態） |
| 2. 一般化エントロピーのモデル | `GeneralizedEntropyModel`、有限・可算層の総生成率、非負性、厳密な積分の正値性（成分の活動から） |
| 3. 可算層の総和 | `totalEntropy`、層の列挙による部分和、極限、項別微分（一様可算和可能な上界） |
| 4. A6′ による極限移行 | 一様可積分性（Vitali）で、有限層の収支を可算層へ |
| 5. 有限層・可算層の非再帰 | 成分の微分式・第二法則・活動から条件 23-A を導いて、非再帰まで |

### 0.3 用語

- **条件 23-A**：生存している時刻の間で、総生成率の積分が厳密に正（持続的な厳密散逸）。
- **A6′**：可算層の生成率の部分和が一様可積分で、a.e. に収束する（定理15の仮定）。
- **A7**：閉じた系の交換式（物理層の生成率が、認知層の生成率の重み付き和の符号反転と、総生成率の和）。
- **完全状態**：物理・全層・環境・記憶・履歴など、エントロピーが一価に定まるために必要な変数をすべて含む状態。

### 0.4 このファイルが証明していないこと

- **成分ごとの収支式・微分式は仮定**です（省略された定理15の力学から導くものではありません）。
- **条件 23-A（厳密な積分の正値性）**は、仮定として置くか、成分の連続性・非負性・活動（`…_of_component_activity`）から導きます。「持続的な厳密散逸」自体を物理的に確かめる作業ではありません。
- **完全状態**にエントロピーが一価に定まるように必要な変数が入っていることは、Lean では判定できない**解釈上の前提**です（人工的な時計の座標を足して非再帰を強制してはいけない）。
- 可算層で項別微分を使う版は、一様可算和可能な上界を仮定します（論文の A6′（一様可積分性）より**強い**仮定）。A6′ だけを使う版は `…_of_uniformIntegrable` です。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **共有エントロピー収支解析**
>
> 定理15(I) と定理23が共用する、区間積分・一般化エントロピー・有限層／可算層の収支の核。証明本文と公開名前空間 `Tomabechi.Theorem23` は、旧モジュールから移動したまま保持する。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem23`。`open Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem23.intervalIntegral_eq_integral_restrict_Ioc"></a>

## 補題 `intervalIntegral_eq_integral_restrict_Ioc`

### 式

$$\int_a^bf\,dt=\int f\ d\bigl(\text{volume}|_{(a,b]}\bigr)\quad(a\le b)$$

### Lean のコメント（日本語訳）

> 増加する区間では、Lebesgue の区間積分は、体積測度を半開区間に制限した測度での積分である。

### 補題の説明

区間積分 \(\int_a^b\) を、測度を半開区間 \((a,b]\) に制限した積分として書き直します。以降、測度論的な議論（Vitali など）で使います。

### 証明の概略

1. `intervalIntegral.integral_of_le`（\(a\le b\) のとき区間積分は \(\text{Ioc}\) 上の積分）と、`uIoc` の定義（4 行）。

----

<a id="Tomabechi.Theorem23.entropy_balance_of_absolute_continuity"></a>

## 補題 `entropy_balance_of_absolute_continuity`

### 式

$$S\ \text{絶対連続},\ \ S'(t)=\Pi(t)\ \text{a.e.}\ \Longrightarrow\ S(b)-S(a)=\int_a^b\Pi\,dt$$

### Lean のコメント（日本語訳）

> 絶対連続性と、ほとんど至るところのエントロピーの収支は、式 (23.1) の証明で使う端点の生成の恒等式を与える。
> 日本語の要約：絶対連続性と、ほとんど至るところの微分の収支から、エントロピーの差を、生成率の区間積分に等置する。

### 補題の説明

微積分学の基本定理（絶対連続版）：絶対連続な関数の端点の差は、導関数の積分です。導関数が生成率にほぼ至るところ等しいので、生成率の積分に置き換えられます。

### 証明の概略

1. 絶対連続な関数について \(S(b)-S(a)=\int_a^bS'\)（`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`）。
2. a.e. で \(S'=\Pi\) なので積分を置き換える（`intervalIntegral.integral_congr_ae`、8 行）。

----

<a id="Tomabechi.Theorem23.entropy_balance_and_nonnegative_production"></a>

## 補題 `entropy_balance_and_nonnegative_production`

### 式

$$\Pi\ge0\ \text{a.e.}\ \Longrightarrow\ S(b)-S(a)=\int_a^b\Pi\ \wedge\ \int_a^b\Pi\ge0$$

### Lean のコメント（日本語訳）

> 定理23で使う、微分形の完全なエントロピーの橋：絶対連続性とほとんど至るところの収支の法則が、端点のエントロピーの差を与える。一方、第二法則の符号 \(\Pi_{\text{gen}}\ge0\) が、非負の総生成を与える。持続的な厳密散逸は、なお別の条件（23-A）である。
> 日本語の要約：微分の収支に、第二法則のほとんど至るところの非負性を加えて、端点のエントロピーの差と、積分した生成率の非負性を得る。

### 補題の説明

上の補題に、第二法則（生成率が a.e. 非負）を加えて、エントロピーの差が**非負**であることまで得ます。

### 証明の概略

1. 上の補題で収支の等式。
2. 非負関数の積分は非負（`intervalIntegral.integral_nonneg_of_ae` 型、12 行）。

----

<a id="Tomabechi.Theorem23.complete_state_never_repeats_of_absolute_continuity"></a>

## 補題 `complete_state_never_repeats_of_absolute_continuity`

### 式

$$\int_{t_1}^{t_2}\Pi>0\ \&\ \text{絶対連続な収支}\ \Longrightarrow\ \text{state}(t_2)\neq\text{state}(t_1)$$

### Lean のコメント（日本語訳）

> 持続的な厳密なエントロピー生成は、論文の a.e. エントロピー生成の式が、絶対連続な完全状態の軌道について与えられているとき、正確な再帰を排除する。したがって、短い順序の議論で使う端点の収支は、別に仮定されるのではなく、省略された定理15の収支の微分形から導かれる。
> 日本語の要約：エントロピーが完全状態の一価の関数として定義され、絶対連続な収支と条件 23-A が成り立つとき、状態は繰り返さない。

### 補題の説明

**非再帰の核心**：状態が時刻 \(t_1\) と \(t_2\) で同じなら、エントロピーも同じで、エントロピーの差 \(0\) が生成率の積分（\(>0\)）に等しくなって矛盾します。

### 証明の概略

1. `entropy_balance_of_absolute_continuity` で \(S(t_2)-S(t_1)=\int\Pi>0\)。
2. 状態が同じなら \(S(t_2)=S(t_1)\) で矛盾（11 行）。

----

<a id="Tomabechi.Theorem23.complete_state_never_repeats_of_strict_entropy_balance"></a>

## 補題 `complete_state_never_repeats_of_strict_entropy_balance`

### 式

$$S(t_2)-S(t_1)=\int_{t_1}^{t_2}\Pi>0\ \Longrightarrow\ \text{state}(t_2)\neq\text{state}(t_1)$$

### Lean のコメント（日本語訳）

> エントロピー収支の積分形だけで、非再帰には十分である。絶対連続性と点ごとの微分方程式は、この収支への 1 つの道であり、A6′ の有限和の極限の定理は別の道である。
> 日本語の要約：全区間の積分の収支と条件 23-A から、完全状態の非再帰を直接導く。

### 補題の説明

上の補題で、収支の**積分形**だけを仮定した版です（収支の導出の経路に依らない）。

### 証明の概略

1. 同じ議論：状態が等しければエントロピー差は 0、積分は正で矛盾（9 行）。

----

<a id="Tomabechi.Theorem23.complete_state_entropy_and_nonrecurrence"></a>

## 補題 `complete_state_entropy_and_nonrecurrence`

### 式

$$\Longrightarrow\ 0\le S(t_2)-S(t_1)\ \wedge\ 0<S(t_2)-S(t_1)\ \wedge\ \text{state}(t_2)\neq\text{state}(t_1)$$

### Lean のコメント（日本語訳）

> 定理23のエントロピーの節の完全状態の形。ほとんど至るところの第二法則の不等式が非減少の一般化エントロピーを与え、条件 23-A の厳密な積分の不等式が再帰を排除する。エントロピー汎関数は、論文の証明が要求するとおり、完全状態の一価の関数である。呼び出し側の `State` は、エントロピーを一価にするために必要な、物理・全層・環境・記憶・履歴の変数を含むことを意図している。非再帰を強制するためだけに、人工的な時計の座標で拡大してはならない。Lean は、任意の型からその意味的な除外を判定できないので、それはこのインターフェースの解釈の一部として残る。
> 日本語の要約：第二法則による非減少、条件 23-A による厳密増加、および完全状態の非再帰をまとめる。

### 補題の説明

定理23のエントロピーの節の結論（非減少・厳密増加・非再帰）を、1 つの定理にまとめます。

### 証明の概略

1. `entropy_balance_and_nonnegative_production` で非負、条件 23-A（`hstrict`）で厳密に正。
2. `complete_state_never_repeats_of_absolute_continuity` で非再帰（14 行）。

----

<a id="Tomabechi.Theorem23.complete_state_entropy_and_nonrecurrence_of_continuous_production"></a>

## 補題 `complete_state_entropy_and_nonrecurrence_of_continuous_production`

### 式

$$\Pi\ \text{連続・非負},\ \exists t\,(\Pi(t)>0)\ \Longrightarrow\ \text{厳密増加・非再帰}$$

### Lean のコメント（日本語訳）

> 区間ごとに連続な生成率は、局所的な持続的活動から、条件 23-A の厳密な積分の形が従うようにする：生成率は各生存区間の全体で非負で、その区間のある点で厳密に正である。a.e. のエントロピー収支と合わせて、積分の不等式自体を仮定せずに、エントロピーの厳密増加と非再帰が得られる。
> 日本語の要約：生成率の連続性・区間上の非負性と、各生存区間の中で一度は正になる条件から、条件 23-A を導く。

### 補題の説明

条件 23-A を、より基本的な条件（生成率が連続で非負で、各区間のどこかで正）から**導く**版です。連続な非負関数が 1 点で正なら積分は正（`intervalIntegral.integral_pos`）。

### 証明の概略

1. 連続・非負・ある点で正から、区間積分が正（`intervalIntegral.integral_pos`）。
2. `complete_state_entropy_and_nonrecurrence` を適用（19 行）。

----

<a id="Tomabechi.Theorem23.GeneralizedEntropyModel"></a>

## 構造体 `GeneralizedEntropyModel`

### 式

$$S_{\text{gen}}(z)=S_{\text{phys}}(z)+\sum_\ell w_\ell\,S_\ell(z),\quad w_\ell>0,\ \ \sum_\ell w_\ell S_\ell(z)\ \text{は絶対収束}$$

### Lean のコメント（日本語訳）

> 定理23で使う一般化エントロピーのデータ：物理エントロピーと、層ごとのエントロピーの重み付き和。\(\mathbb R\) 上の `Summable` は、重み付きの層の級数が絶対収束する（したがって総エントロピーが定義される）ことを意味する。収支の法則とその微分可能性の帰結は、総和可能性だけからは従わないので、別の仮定として残る。
> 日本語の要約：物理エントロピー・層別エントロピー・正の重み・状態ごとの絶対収束をまとめるデータ構造。

### 定義の説明

フィールド：物理エントロピー `physicalEntropy`、層エントロピー `layerEntropy`、層の重み `layerWeight`（すべて正）、そして「各状態で重み付き層エントロピーの和が絶対収束」`weightedLayerTerms_summable` です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem23.finiteGeneralizedEntropyProduction"></a>

## 定義 `finiteGeneralizedEntropyProduction`

### 式

$$\Pi_{\text{gen}}(t)=\Pi_{\text{phys}}(t)+\sum_\ell w_\ell\,\Pi_\ell(t)$$

### Lean のコメント（日本語訳）

> 有限層の特殊化での総エントロピー生成。
> 日本語の要約：有限個の層の重み付き総エントロピー生成率を定義する。

### 定義の説明

物理層の生成率と、層ごとの生成率の重み付き和の和です。

### 証明の概略

1. 定義：`physicalProduction t + ∑ layer, layerWeight layer * layerProduction layer t`。

----

<a id="Tomabechi.Theorem23.finite_generalized_production_nonnegative_of_components"></a>

## 補題 `finite_generalized_production_nonnegative_of_components`

### 式

$$w_\ell\ge0,\ \Pi_{\text{phys}}\ge0,\ \Pi_\ell\ge0\ (\text{a.e.})\ \Longrightarrow\ \Pi_{\text{gen}}\ge0\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 物理層と層ごとの生成が非負なら、有限層の区間上でほとんど至るところ総生成も非負である。ここでは、すべての層の重みが正であることが本質的である。
> 日本語の要約：各成分の生成率のほとんど至るところの非負性と、層の重みの非負性から、総生成率の非負性を導く。

### 補題の説明

各成分が非負で重みが非負なら、重み付き和も非負です（有限個の a.e. 条件をまとめます）。

### 証明の概略

1. 有限個の \(\forall^\mu\) をまとめる（`ae_all_iff`）。
2. 各点で、非負の項の有限和が非負（12 行）。

----

<a id="Tomabechi.Theorem23.finite_generalized_production_nonnegative_on_alive"></a>

## 補題 `finite_generalized_production_nonnegative_on_alive`

### 式

$$\forall\ \text{生存区間},\ \text{成分の第二法則}\ \Longrightarrow\ \Pi_{\text{gen}}\ge0\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> すべての生存区間にわたる、成分ごとの第二法則の前提をまとめる。結果は、有限層のエントロピー/非再帰の定理が受け付ける、a.e. の生成の符号のインターフェースとちょうど同じである。
> 日本語の要約：各生存区間での成分ごとの第二法則を、総生成率の符号の条件にまとめる。

### 補題の説明

前の補題を、すべての生存区間の対 \((t_1,t_2)\) に対して述べた版です。

### 証明の概略

1. 各区間で `finite_generalized_production_nonnegative_of_components` を適用（7 行）。

----

<a id="Tomabechi.Theorem23.countable_generalized_production_nonnegative_on_alive"></a>

## 補題 `countable_generalized_production_nonnegative_on_alive`

### 式

$$\text{可算層},\ \Pi_{\text{phys}}\ge0,\ \Pi_\ell\ge0\ \Longrightarrow\ \Pi_{\text{phys}}+\sum'_\ell w_\ell\Pi_\ell\ge0\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 可算個の層については、成分ごとのほとんど至るところの第二法則の不等式は、総生成についても同じ不等式を意味する。総和可能な導関数の優関数は、重み付きの生成の級数が、ほとんどすべての時刻で本当に総和可能であることを保証し、発散する級数に対する `tsum` の既定値に頼らないようにする。
> 日本語の要約：可算の各層の a.e. の第二法則と、一様な総和可能な上界から、総生成率の a.e. の非負性を導く。

### 補題の説明

可算和（`tsum`）は、総和可能でないと 0 になる規約があるので、総和可能性（優関数 `derivativeBound` が総和可能）を保証します。そのうえで非負の項の `tsum` は非負です。

### 証明の概略

1. 可算個の層についての a.e. 条件をまとめる（`ae_all_iff`、`Countable`）。
2. 各点で重み付き生成の級数が総和可能（優関数で押さえられる）、非負項の `tsum` は非負（`tsum_nonneg`、20 行）。

----

<a id="Tomabechi.Theorem23.finite_generalized_production_strict_integral_of_component_activity"></a>

## 補題 `finite_generalized_production_strict_integral_of_component_activity`

### 式

$$\text{各成分が連続・非負},\ \text{どれかが正になる}\ \Longrightarrow\ \int_{t_1}^{t_2}\Pi_{\text{gen}}>0$$

### Lean のコメント（日本語訳）

> 有限層のエントロピーのモデルで、成分ごとの連続性と非負性が、どれか 1 つの成分の持続的活動を、重み付きの総和についての条件 23-A の厳密な積分生成の節に変える。
> 日本語の要約：有限層で各成分が連続・非負なら、物理層または認知層の持続的な活動から、総生成率の区間積分が厳密に正になることを導く。

### 補題の説明

条件 23-A の**導出**：総生成率が連続で非負で、どこかで正なら積分は正、という議論を、成分の条件から行います。

### 証明の概略

1. 総生成率は連続（連続関数の和と定数倍、`continuousOn_finsetSum`）。
2. 非負性は各成分から。どこかで正（活動の仮定、重みが正）。`intervalIntegral.integral_pos` で積分が正（48 行）。

----

<a id="Tomabechi.Theorem23.countable_generalized_production_strict_integral_of_component_activity"></a>

## 補題 `countable_generalized_production_strict_integral_of_component_activity`

### 式

$$\text{可算層},\ \text{一様な総和可能な上界}\ \Longrightarrow\ \int_{t_1}^{t_2}\Pi_{\text{gen}}>0$$

### Lean のコメント（日本語訳）

> 有限の成分の活動の結果の、可算層の類似。一様な総和可能な上界は、重み付きの生成の級数を、各生存区間で連続にする。物理層またはどれか 1 つの認知層がその区間のどこかで厳密に活動していれば、他のすべての成分の非負性が、総生成の積分を厳密に正にする。
> 日本語の要約：一様な総和可能な上界により、総生成率の連続性を得て、物理層またはいずれかの認知層の活動から、区間積分の厳密な正値性を導く。

### 補題の説明

上の補題の可算版です。級数の連続性は `continuousOn_tsum`（一様な優関数）で得ます。

### 証明の概略

1. 重み付き生成の各項は連続、優関数が総和可能なので和も連続（`continuousOn_tsum`）。
2. 総生成率は連続・非負・どこかで正で、積分が正（`intervalIntegral.integral_pos`、55 行）。

----

<a id="Tomabechi.Theorem23.GeneralizedEntropyModel.totalEntropy"></a>

## 定義 `GeneralizedEntropyModel.totalEntropy`

### 式

$$S_{\text{gen}}(z)=S_{\text{phys}}(z)+\sum'_\ell w_\ell\,S_\ell(z)$$

### Lean のコメント（日本語訳）

> 物理エントロピーと、絶対収束する重み付き層エントロピーの級数に対応する、状態の汎関数。
> 日本語の要約：物理エントロピーと、収束する層ごとの重み付き和から、状態の汎関数を定義する。

### 定義の説明

一般化エントロピーの定義です（`tsum` を使うので、総和可能性はモデルのフィールドで保証）。

### 証明の概略

1. 定義：`model.physicalEntropy z + ∑' layer, model.layerWeight layer * model.layerEntropy layer z`。

----

<a id="Tomabechi.Theorem23.enumeratedPartialTotalEntropy"></a>

## 定義 `enumeratedPartialTotalEntropy`

### 式

$$S_n(t)=S_{\text{phys}}(\text{state}(t))+\sum_{k<n}w_{e(k)}\,S_{e(k)}(\text{state}(t))$$

### Lean のコメント（日本語訳）

> 可算無限個の層をもつ一般化エントロピーのモデルの有限の部分和。層全体の自然数による明示的な列挙を使う。

### 定義の説明

層を自然数 \(0,1,2,\dots\) で列挙して、最初の \(n\) 層だけを足した部分和（有限層）です。極限 \(n\to\infty\) で総エントロピーに近づきます。

### 証明の概略

1. 定義：`physicalEntropy + ∑ k : Fin n, layerWeight (enumeration k) * layerEntropy (enumeration k)`。

----

<a id="Tomabechi.Theorem23.enumeratedFiniteLayerModel"></a>

## 定義 `enumeratedFiniteLayerModel`

### 式

$$\text{Fin }n\ \text{層のモデル}$$

### Lean のコメント（日本語訳）

> 列挙の最初の \(n\) 層が誘導する、有限の `Fin n` のモデル。

### 定義の説明

最初の \(n\) 層だけを層とみなした `GeneralizedEntropyModel` です。有限層の補題（収支など）を、部分和に適用するために使います。

### 証明の概略

1. 定義：層の型を `Fin n`、層のエントロピー・重みを列挙で引き戻す（7 行）。

----

<a id="Tomabechi.Theorem23.enumeratedPartialTotalProduction"></a>

## 定義 `enumeratedPartialTotalProduction`

### 式

$$\Pi_n(t)=\Pi_{\text{phys}}(t)+\sum_{k<n}w_{e(k)}\Pi_{e(k)}(t)$$

### Lean のコメント（日本語訳）

> `enumeratedPartialTotalEntropy` と対になる生成率。

### 定義の説明

部分和エントロピーに対応する、部分和の総生成率です。

### 証明の概略

1. 定義：`physicalProduction t + ∑ k : Fin n, layerWeight (enumeration k) * layerProduction (enumeration k) t`。

----

<a id="Tomabechi.Theorem23.enumerated_partial_total_entropy_tendsto"></a>

## 補題 `enumerated_partial_total_entropy_tendsto`

### 式

$$S_n(t)\ \xrightarrow[n\to\infty]{}\ S_{\text{gen}}(\text{state}(t))$$

### Lean のコメント（日本語訳）

> `GeneralizedEntropyModel` に組み込まれた、状態ごとの絶対収束は、各時刻での、列挙された有限層のエントロピーの収束を意味する。これは、A6′ の収支の定理の端点の極限の前提を、モデルの定義から直接与える（列挙つきの可算無限層について）。
> 日本語の要約：層と自然数の全単射のもとで、状態ごとの総和可能性から、有限層のエントロピーの和の各時刻での収束を導く。

### 補題の説明

総和可能な級数の部分和は、和に収束します（列挙で並べ替えても和は同じ）。

### 証明の概略

1. 状態 \(z\) での項 \(a\mapsto w_ae_a(z)\) は総和可能（モデルのフィールド）。
2. 列挙の全単射で並べ替えた級数も総和可能で、`tsum` が等しい（`Equiv.tsum_eq`）。
3. 部分和は `tsum` に収束（`Summable.hasSum` と `HasSum.tendsto_sum_nat`、23 行）。

----

<a id="Tomabechi.Theorem23.finite_layer_total_entropy_derivative_of_component_derivatives"></a>

## 補題 `finite_layer_total_entropy_derivative_of_component_derivatives`

### 式

$$S_{\text{phys}}'=\Pi_{\text{phys}},\ S_\ell'=\Pi_\ell\ \Longrightarrow\ (S_{\text{phys}}+\sum_\ell w_\ell S_\ell)'=\Pi_{\text{gen}}\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 有限個の層では、成分ごとの a.e. の微分式を足すと、一般化された総エントロピーの微分式になる。成分の微分式自体は仮定であり、力学からは導かない。
> 日本語の要約：有限層の成分ごとの微分式を足して、総エントロピーの微分式を導く。

### 補題の説明

有限和の微分は微分の和です。

### 証明の概略

1. 各成分が a.e. で微分可能（有限個の a.e. 条件をまとめる）。
2. `HasDerivAt.sum` と定数倍の微分で和の微分（25 行）。

----

<a id="Tomabechi.Theorem23.finite_layer_model_total_entropy_derivative_of_component_derivatives"></a>

## 補題 `finite_layer_model_total_entropy_derivative_of_component_derivatives`

### 式

$$\Longrightarrow\ (S_{\text{gen}}\circ\text{state})'=\Pi_{\text{gen}}\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 有限層の微分の公式を、`GeneralizedEntropyModel.totalEntropy` の状態汎関数と明示的に同一視する。これは、定理23の完全状態の形で、成分ごとの収支の法則を使うために必要な直接の橋である。無限級数と微分の交換は主張しない。
> 日本語の要約：有限層の成分の微分式を、定義済みの総エントロピーの汎関数の a.e. の微分式に接続する。

### 補題の説明

上の補題の結論を `totalEntropy`（`tsum` で定義）で言い直します。有限層では `tsum` が有限和になるので一致します。

### 証明の概略

1. 有限型では `tsum` が `Finset.sum` に等しい（`tsum_fintype`）。前の補題を適用（7 行）。

----

<a id="Tomabechi.Theorem23.countable_layer_model_total_entropy_derivative_of_component_derivatives"></a>

## 補題 `countable_layer_model_total_entropy_derivative_of_component_derivatives`

### 式

$$\sum_\ell\|w_\ell\Pi_\ell\|\le\sum_\ell b_\ell<\infty\ \Longrightarrow\ S_{\text{gen}}'=\Pi_{\text{phys}}+\sum'_\ell w_\ell\Pi_\ell$$

### Lean のコメント（日本語訳）

> 可算個のエントロピー層について、各成分の点ごとの微分可能性と、すべての層の生成率の総和可能な上界が、重み付きのエントロピー級数の項別の微分を正当化する。優関数は時刻について一様である。これは、エントロピーの値の総和可能性だけで、微分と `tsum` の交換が許されると主張することなく、収支の法則への無限層の道を与える。
> 日本語の要約：可算層で、全時刻の成分の微分式と、時刻に一様な総和可能な上界を課すと、層の和の微分を項ごとに計算できる。

### 補題の説明

項別微分の定理（`hasDerivAt_tsum`）：微分の列が一様に総和可能な優関数で押さえられれば、級数の微分は微分の級数です。

### 証明の概略

1. 各層の項 \(t\mapsto w_\ell S_\ell(\text{state}(t))\) の微分が \(w_\ell\Pi_\ell\)（定数倍）。
2. 一様な優関数で `hasDerivAt_tsum`（Mathlib の項別微分）を適用。物理層の微分と足し合わせる。

----

<a id="Tomabechi.Theorem23.countable_layer_model_total_entropy_derivative_of_exchange_equation"></a>

## 補題 `countable_layer_model_total_entropy_derivative_of_exchange_equation`

### 式

$$\text{A7: }\Pi_{\text{phys}}=-\sum'_\ell w_\ell\Pi_\ell+\Pi_{\text{tot}}\ \Longrightarrow\ S_{\text{gen}}'=\Pi_{\text{tot}}$$

### Lean のコメント（日本語訳）

> 定理15の閉じた系の交換式 (A7) は、一般化エントロピーの微分での認知層の生成を打ち消す。結論は、ほとんど至るところ（より強い正則性のもとではここでは点ごとに）\(S_{\text{gen}}'=\Pi_{\text{gen}}\) である。項別微分の道は、総和可能な一様な優関数を使い、これは論文の一様可積分性の前提 A6′ より強い。
> 日本語の要約：定理15の A7 の交換式と、可算層の項別微分から、総エントロピーの微分が総生成率に等しいことを導く。

### 補題の説明

物理層の生成率が、認知層の生成率の和の符号反転に総生成率を足したもの（A7）なら、物理層と認知層の和をとると、認知層の寄与が打ち消されて総生成率だけが残ります。

### 証明の概略

1. `countable_layer_model_total_entropy_derivative_of_component_derivatives` で \(S'=\Pi_{\text{phys}}+\sum'w\Pi\)。
2. A7 を代入して整理する。

----

<a id="Tomabechi.Theorem23.countable_layer_partial_rates_tendsto_L1_of_uniformIntegrable"></a>

## 補題 `countable_layer_partial_rates_tendsto_L1_of_uniformIntegrable`

### 式

$$\text{一様可積分}\ \&\ \text{a.e. 収束}\ \Longrightarrow\ \lVert\Pi_n-\Pi\rVert_{L^1}\to0\quad(\text{有限測度})$$

### Lean のコメント（日本語訳）

> A6′ の一様可積分性とほとんど至るところの収束の前提は、任意の有限測度の時間領域で、生成率の有限の部分和の \(L^1\) 収束を与える。これは、上のより強い総和可能な優関数の道を弱めるために必要な Vitali の段階である。
> 日本語の要約：有限測度の領域では、A6′ の一様可積分性と a.e. の収束から、生成率の部分和の \(L^1\) 収束が従う。

### 補題の説明

**Vitali の収束定理**：有限測度空間で、可測な関数列が一様可積分で、a.e. に収束すれば、\(L^1\) で収束します。A6′ の条件を、積分の極限の交換に使えるようにします。

### 証明の概略

1. Mathlib の `MeasureTheory.tendstoInMeasure_iff_tendsto_Lp`／`tendsto_Lp_of_tendsto_ae`（Vitali の定理）を、\(p=1\) で適用する。

----

<a id="Tomabechi.Theorem23.countable_layer_entropy_balance_of_uniformIntegrable"></a>

## 補題 `countable_layer_entropy_balance_of_uniformIntegrable`

### 式

$$S_n(b)-S_n(a)=\int\Pi_n\ \&\ \text{端点で収束}\ \&\ \Pi_n\to\Pi\ (L^1)\ \Longrightarrow\ S(b)-S(a)=\int\Pi$$

### Lean のコメント（日本語訳）

> A6′ の Vitali の判定法を使った、有限層のエントロピーの収支の極限への移行。端点の収束と、生成率の \(L^1\) 収束は、可算の総和についての積分された収支を保つ。
> 日本語の要約：端点での部分和の収束と、A6′ 型の一様可積分性から、有限層の収支式を、可算層全体の積分された収支へ移す。

### 補題の説明

有限層の収支 \(S_n(b)-S_n(a)=\int\Pi_n\) の両辺で \(n\to\infty\) の極限をとります。左辺は端点の収束、右辺は \(L^1\) 収束から。

### 証明の概略

1. 左辺の極限：端点の部分和の収束（`hstart`, `hend`）。
2. 右辺の極限：\(L^1\) 収束から積分が収束（`countable_layer_partial_rates_tendsto_L1_of_uniformIntegrable` と `tendsto_integral_of_L1`）。
3. 極限の一意性で等式（`tendsto_nhds_unique`）。

----

<a id="Tomabechi.Theorem23.enumerated_countable_layer_entropy_balance_of_uniformIntegrable"></a>

## 補題 `enumerated_countable_layer_entropy_balance_of_uniformIntegrable`

### 式

$$\text{GeneralizedEntropyModel}\ \Longrightarrow\ S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int\Pi$$

### Lean のコメント（日本語訳）

> A6′ 型の \(L^1\) 収束が、実際の `GeneralizedEntropyModel` の積分された収支を与える：その端点の極限は、モデルの状態ごとの総和可能性から来るので、もはや別の仮定ではない。有限の部分収支の式は、極限の生成率を物理的な総生成と同一視することと同様に、明示的な入力のまま残る。
> 日本語の要約：総エントロピーのモデルの状態ごとの絶対収束で端点の極限を補い、A6′ 型の条件から、総収支を導く。

### 補題の説明

前の補題の端点の収束の前提を、モデルの総和可能性（`enumerated_partial_total_entropy_tendsto`）から自動的に満たす版です。

### 証明の概略

1. `enumerated_partial_total_entropy_tendsto` で端点の収束。
2. `countable_layer_entropy_balance_of_uniformIntegrable` を適用。

----

<a id="Tomabechi.Theorem23.enumerated_countable_layer_nonrecurrence_of_uniformIntegrable"></a>

## 補題 `enumerated_countable_layer_nonrecurrence_of_uniformIntegrable`

### 式

$$\text{A6′ 型}\ +\ \text{条件 23-A}\ \Longrightarrow\ S_{\text{gen}}(b)>S_{\text{gen}}(a),\ \ \text{state}(b)\neq\text{state}(a)$$

### Lean のコメント（日本語訳）

> 可算無限層のモデルでの、A6′ 型の道による (23.1) のエンドツーエンドの証明。各生存区間で、有限層の収支と、有限の生成率の一様可積分性が、総エントロピーの収支を与える。条件 23-A がそのとき厳密な増加を与え、正確な再帰を排除する。区間の測度は有限でなければならず、有限の収支・a.e. の極限・一様可積分性・厳密な生成は、明示的な入力のままである。
> 日本語の要約：区間ごとの A6′ 型の条件から総収支を導き、条件 23-A のもとで総エントロピーの厳密な増加と完全状態の非再帰を示す。

### 補題の説明

可算層で、**A6′（一様可積分性）だけ**を使って、非再帰まで示します。

### 証明の概略

1. `enumerated_countable_layer_entropy_balance_of_uniformIntegrable` で、列挙した可算層の総エントロピーの収支（\(S(b)-S(a)=\int\Pi\)）を得る。
2. 条件 23-A（任意の \(t_1<t_2\) で \(\int\Pi>0\)）から、総エントロピーが異なるので完全な状態も異なる、という非再帰の議論を行う（46 行）。

----

<a id="Tomabechi.Theorem23.countable_layer_entropy_series_absolutely_continuous"></a>

## 補題 `countable_layer_entropy_series_absolutely_continuous`

### 式

$$\sum_\ell\|w_\ell\Pi_\ell\|\le b_\ell\ (\text{総和可能})\ \Longrightarrow\ \sum'_\ell w_\ell S_\ell\ \text{は大域的に Lipschitz、したがって絶対連続}$$

### Lean のコメント（日本語訳）

> すべての重み付きの層の導関数についての、一様な総和可能な上界は、その総エントロピーの級数を、大域的に Lipschitz に、したがって、すべての有限区間で絶対連続にする。完全な一般化エントロピーを作るときには、物理エントロピーの絶対連続性だけは、別に与える必要がある。
> 日本語の要約：層別生成率に時刻に一様な総和可能な上界があれば、重み付き層エントロピーの和は、大域的に Lipschitz である。

### 補題の説明

導関数が一様に有界（\(\sum b_\ell\)）なので、層エントロピーの和は Lipschitz です。Lipschitz 関数は絶対連続です。

### 証明の概略

1. 導関数の \(\sup\) は \(\sum_\ell b_\ell\) で抑えられる（項別微分、`countable_layer_model_total_entropy_derivative_…` の議論）。
2. 平均値の不等式で Lipschitz（`lipschitzWith_of_nnnorm_deriv_le`）。Lipschitz は絶対連続。

----

<a id="Tomabechi.Theorem23.finite_layer_entropy_balance_of_component_balances"></a>

## 補題 `finite_layer_entropy_balance_of_component_balances`

### 式

$$\Delta S_{\text{phys}}=\int\Pi_{\text{phys}},\ \Delta S_\ell=\int\Pi_\ell\ \Longrightarrow\ \Delta S_{\text{gen}}=\int\Pi_{\text{gen}}$$

### Lean のコメント（日本語訳）

> 有限のエントロピー層については、成分ごとの端点の収支の法則を足すと、総エントロピーの収支の法則になる。区間の可積分性は明示的である。個々の成分の収支は仮定のままである。
> 日本語の要約：成分の端点の収支と可積分性から、有限和の総収支を導く。

### 補題の説明

有限和の積分は積分の有限和です（可積分性が必要）。

### 証明の概略

1. `intervalIntegral.integral_add`、`integral_finset_sum`、定数倍で、積分の和を整理する。

----

<a id="Tomabechi.Theorem23.finite_layer_entropy_balance_of_component_derivatives"></a>

## 補題 `finite_layer_entropy_balance_of_component_derivatives`

### 式

$$\text{各成分: 絶対連続}\ +\ \text{a.e. 微分式}\ \Longrightarrow\ \Delta S_{\text{gen}}=\int\Pi_{\text{gen}}$$

### Lean のコメント（日本語訳）

> 有限層のエントロピー収支を、成分ごとの微分の法則から導く。絶対連続性と a.e. の微分式が各端点の収支を与え、有限の加法性と区間の可積分性が総収支にまとめる。成分の微分式自体は、明示的な仮定である。
> 日本語の要約：各成分の絶対連続性・微分式から、総エントロピーの端点の収支を導く。

### 補題の説明

各成分について `entropy_balance_of_absolute_continuity` で端点の収支を得て、前の補題で足し合わせます。

### 証明の概略

1. 各成分で `entropy_balance_of_absolute_continuity`。
2. `finite_layer_entropy_balance_of_component_balances` を適用。

----

<a id="Tomabechi.Theorem23.enumerated_partial_entropy_balance_of_component_derivatives"></a>

## 補題 `enumerated_partial_entropy_balance_of_component_derivatives`

### 式

$$S_n(b)-S_n(a)=\int_a^b\Pi_n$$

### Lean のコメント（日本語訳）

> 最初の \(n\) 個の列挙された層は、含まれる各成分がそれ自身の絶対連続性と a.e. の微分の法則をもつとすぐに、有限のエントロピー収支を満たす。これは、A6′ の極限の道が使う有限の収支の前提を、成分レベルの定理15の収支のデータから導く。
> 日本語の要約：有限個の採用された層について、各成分の絶対連続性・微分式から、有限の部分和の収支を導く。

### 補題の説明

有限層の収支（`finite_layer_entropy_balance_of_component_derivatives`）を、最初の \(n\) 層のモデル（`enumeratedFiniteLayerModel`）に適用します。

### 証明の概略

1. `enumeratedFiniteLayerModel` に有限層の収支を適用し、部分和の定義に合わせて書き換える。

----

<a id="Tomabechi.Theorem23.enumerated_countable_layer_nonrecurrence_of_component_derivatives_and_uniformIntegrable"></a>

## 補題 `enumerated_countable_layer_nonrecurrence_of_component_derivatives_and_uniformIntegrable`

### 式

$$\text{成分の微分式}\ +\ \text{A6′}\ +\ \text{条件 23-A}\ \Longrightarrow\ \text{厳密増加・非再帰}$$

### Lean のコメント（日本語訳）

> 列挙された可算無限層についての (23.1) の、A6′ 型の完全に接続された証明。有限の部分収支は成分の微分の法則から導かれる。UI と a.e. の極限の前提は、各生存区間の、実際の有限の重み付き生成の和に課される。区間の測度は、Lebesgue 測度の `uIoc a b` への有限の制限である。
> 日本語の要約：成分別の微分式から有限の収支を導き、区間ごとの A6′ 型の条件と 23-A を用いて、可算層の総エントロピーの厳密増加と非再帰を示す。

### 補題の説明

上の 2 つを接続した版です：有限の部分収支を成分の微分式から導き（`enumerated_partial_entropy_balance_of_component_derivatives`）、A6′ で極限に移行します。

### 証明の概略

1. `enumerated_partial_entropy_balance_of_component_derivatives` で、各 prefix の有限収支を成分の導関数から得る（区間積分は `intervalIntegral_eq_integral_restrict_Ioc` で制限測度の積分に直す）。
2. 一様可積分性と合わせて `enumerated_countable_layer_entropy_balance_of_uniformIntegrable` で総収支を得て、条件 23-A から非再帰を導く（94 行）。

----

<a id="Tomabechi.Theorem23.finite_layer_model_entropy_growth_and_nonrecurrence"></a>

## 補題 `finite_layer_model_entropy_growth_and_nonrecurrence`

### 式

$$\text{成分の収支}\ +\ \text{第二法則}\ +\ \text{条件 23-A}\ \Longrightarrow\ \text{厳密増加・非再帰}$$

### Lean のコメント（日本語訳）

> 定理23のエントロピーの節の有限層の形。成分ごとの収支と、その区間の可積分性が、すべての生存区間で総収支を与える。総和の生成についての条件 23-A が、そのとき厳密なエントロピーの増加を与え、完全状態の再帰を排除する。これは有限層の特殊化である。成分の収支の法則は明示的な仮定のままなので、省略された定理15の力学を導くと主張するものではない。
> 日本語の要約：有限層の総収支、第二法則、条件 23-A から、エントロピーの増加と完全状態の非再帰を示す。

### 補題の説明

有限層の場合の、成分の収支から非再帰までの一連の議論をまとめます。

### 証明の概略

1. `finite_layer_entropy_balance_of_component_balances` で、成分ごとの収支から有限層モデルの総エントロピーの収支（`finiteGeneralizedEntropyProduction` の積分）を得る。
2. 散逸の積分が正（23-A）なので、総エントロピーが増え、したがって完全な状態が異なる（68 行）。

----

<a id="Tomabechi.Theorem23.finite_layer_model_entropy_growth_and_nonrecurrence_of_component_activity"></a>

## 補題 `finite_layer_model_entropy_growth_and_nonrecurrence_of_component_activity`

### 式

$$\text{成分の収支}\ +\ \text{連続性・非負性・活動}\ \Longrightarrow\ \text{厳密増加・非再帰}$$

### Lean のコメント（日本語訳）

> 有限層のエントロピーの収支に、成分ごとの第二法則と持続的活動を合わせると、定理23の厳密なエントロピー増加と非再帰が出る。総生成についての厳密な積分の条件は、すべての生存区間で、少なくとも 1 つの成分の連続性と活動から導かれる。
> 日本語の要約：有限層の成分の収支と、成分ごとの第二法則・持続的活動から、総生成率の厳密な積分を導き、完全状態の非再帰まで示す。

### 補題の説明

上の補題の条件 23-A を、成分の連続性・非負性・活動から**導く**版です。

### 証明の概略

1. `finite_generalized_production_strict_integral_of_component_activity` で 23-A。
2. 上の補題を適用。

----

<a id="Tomabechi.Theorem23.finite_layer_model_nonrecurrence_of_component_derivatives"></a>

## 補題 `finite_layer_model_nonrecurrence_of_component_derivatives`

### 式

$$\text{成分: 絶対連続}\ +\ \text{微分式}\ +\ \text{23-A}\ \Longrightarrow\ \text{非再帰}$$

### Lean のコメント（日本語訳）

> 成分ごとの微分の法則からの、定理23のエントロピーの結論の、有限層のエンドツーエンドの形。微分の法則と区間の可積分性は、明示的な入力のままである。
> 日本語の要約：有限層の成分の微分式を総収支に接続して、厳密増加と非再帰を導く。

### 補題の説明

**収支を成分の微分式から導く**版：成分の絶対連続性と a.e. の微分式から収支を得て、非再帰まで進みます。

### 証明の概略

1. 成分のエントロピーの導関数から、絶対連続性と収支を `entropy_balance_of_absolute_continuity` で成分ごとに得る。
2. それを `finite_layer_model_entropy_growth_and_nonrecurrence` に渡して、総エントロピーの増加と非再帰を得る（68 行）。

----

<a id="Tomabechi.Theorem23.finite_layer_model_nonrecurrence_of_component_derivatives_and_activity"></a>

## 補題 `finite_layer_model_nonrecurrence_of_component_derivatives_and_activity`

### 式

$$\text{成分: 微分式・絶対連続}\ +\ \text{連続・非負・活動}\ \Longrightarrow\ \text{非再帰}$$

### Lean のコメント（日本語訳）

> 条件 23-A の厳密な積分が、成分の活動から導かれる、定理23の有限層の微分の形。成分ごとの連続性と非負性は、ある物理的または層の生成が、そこで正になるとすぐに、各生存区間で総生成の正値性を意味する。
> 日本語の要約：成分の微分式・絶対連続性に加えて、成分ごとの連続性・非負性と持続的活動から、有限層の厳密増加・非再帰を導く。

### 補題の説明

上の補題の 23-A を、成分の活動から導く版です。

### 証明の概略

1. `finite_generalized_production_strict_integral_of_component_activity` で 23-A、`finite_layer_model_nonrecurrence_of_component_derivatives` を適用。

----

<a id="Tomabechi.Theorem23.generalized_entropy_model_nonrecurrence"></a>

## 補題 `generalized_entropy_model_nonrecurrence`

### 式

$$\text{totalEntropy}\ \Longrightarrow\ \text{非減少・厳密増加・非再帰}$$

### Lean のコメント（日本語訳）

> 明示的な物理＋層のエントロピーのモデルに特殊化した、定理23の非再帰の結論。モデルは、よく定義された絶対収束する級数を与える。絶対連続性、エントロピーの収支、第二法則の符号、厳密な生成は、なお仮定として述べる。
> 日本語の要約：一般化エントロピーのモデルの総和を、完全状態の条件付きの非再帰の定理につなぐ。

### 補題の説明

`complete_state_entropy_and_nonrecurrence` で、エントロピー汎関数を `model.totalEntropy` としたものです。

### 証明の概略

1. `complete_state_entropy_and_nonrecurrence` を `entropy := model.totalEntropy` で適用。

----

<a id="Tomabechi.Theorem23.countable_layer_model_nonrecurrence_of_component_derivatives"></a>

## 補題 `countable_layer_model_nonrecurrence_of_component_derivatives`

### 式

$$\text{可算層}\ +\ \text{総和可能な上界}\ +\ \text{成分の微分式}\ +\ \text{23-A}\ \Longrightarrow\ \text{非再帰}$$

### Lean のコメント（日本語訳）

> 定理23.1 の無限可算層のエンドツーエンドの特殊化。可算に総和可能な一様な上界と、点ごとの成分の微分の法則が、一般化エントロピーの収支を作る。絶対連続性・第二法則の符号・条件 23-A が、そのとき、エントロピーの増加と完全状態の非再帰を与える。
> 日本語の要約：無限可算層の一様な導関数の上界と、成分の微分式から総収支を作り、絶対連続性・第二法則・条件 23-A のもとで非再帰を結論する。

### 補題の説明

項別微分の道（一様な総和可能な上界、A6′ より強い仮定）で、可算層の非再帰を示します。

### 証明の概略

1. `countable_layer_model_total_entropy_derivative_of_component_derivatives` で、総エントロピーの導関数が成分の導関数の総和であることを得る。
2. `countable_layer_entropy_series_absolutely_continuous` で総エントロピーの絶対連続性を得る。
3. `generalized_entropy_model_nonrecurrence` に渡し、条件 23-A のもとで非再帰を導く（66 行）。

----

<a id="Tomabechi.Theorem23.absolutely_continuous_of_hasDerivAt_continuousOn"></a>

## 補題 `absolutely_continuous_of_hasDerivAt_continuousOn`

### 式

$$f'\ \text{連続}\ \Longrightarrow\ f\ \text{は}\ [a,b]\ \text{で絶対連続}$$

### Lean のコメント（日本語訳）

> コンパクトな区間上で、全時刻で微分可能で、導関数が連続な、実数値のエントロピー曲線は、そこで \(C^1\) であり、したがって絶対連続である。これは、生成率がすでに連続だと分かっているときに、別個の絶対連続性の前提を除く。
> 日本語の要約：区間上で導関数が連続な、全時刻で微分可能な関数の絶対連続性を示す。

### 補題の説明

\(C^1\) 関数は絶対連続です。導関数が連続（`derivative` が連続で `HasDerivAt`）なら \(C^1\)。

### 証明の概略

1. \(C^1\) の特徴づけ（微分可能で導関数が連続）で \(C^1\)。
2. `ContDiffOn.absolutelyContinuousOnInterval`（\(C^1\) ⇒ 絶対連続、`GradientFlow` でも使った補題）を適用。

----

<a id="Tomabechi.Theorem23.countable_layer_model_nonrecurrence_of_component_derivatives_and_second_law"></a>

## 補題 `countable_layer_model_nonrecurrence_of_component_derivatives_and_second_law`

### 式

$$\text{第二法則を成分ごとに仮定}\ \Longrightarrow\ \text{可算層の非再帰}$$

### Lean のコメント（日本語訳）

> 物理層と個々の認知層についての第二法則を述べた、可算層の非再帰の定理。総生成の非負性は、成分ごとの仮定と、微分に使うのと同じ一様な総和可能な優関数から導かれる。
> 日本語の要約：物理層・各認知層の第二法則から総生成率の非負性を導き、可算層の微分の収支と合わせて非再帰を示す。

### 補題の説明

上の定理の「総生成率の非負性」の仮定を、成分ごとの第二法則から導きます（`countable_generalized_production_nonnegative_on_alive`）。

### 証明の概略

1. `countable_generalized_production_nonnegative_on_alive` で総生成率が a.e. 非負。
2. `countable_layer_model_nonrecurrence_of_component_derivatives` を適用。

----

<a id="Tomabechi.Theorem23.countable_layer_model_nonrecurrence_of_component_derivatives_and_activity"></a>

## 補題 `countable_layer_model_nonrecurrence_of_component_derivatives_and_activity`

### 式

$$\text{連続・第二法則・活動}\ \Longrightarrow\ \text{可算層の非再帰（23-A の両方の部分を導く）}$$

### Lean のコメント（日本語訳）

> 条件 23-A の両方の部分が成分の仮定から導かれる、定理23.1 の可算層のエンドツーエンドの版：連続性、成分ごとの第二法則の不等式、すべての生存区間での少なくとも 1 つの成分の活動。微分と一様な優関数の仮定は、エントロピーの収支と、総生成の連続性を、なお与える。
> 日本語の要約：層ごとの微分・連続性・第二法則・区間ごとの活動から条件 23-A を構成し、可算層の総エントロピーの非再帰を導く。

### 補題の説明

可算層の場合の、最も基本的な仮定からの非再帰です。23-A の「非負性」と「厳密な積分の正値性」の両方を成分の条件から導きます。

### 証明の概略

1. `countable_generalized_production_nonnegative_on_alive` で非負性。
2. `countable_generalized_production_strict_integral_of_component_activity` で厳密な積分。
3. `countable_layer_model_nonrecurrence_of_component_derivatives` を適用。

----


## コメント修正記録

（なし）
