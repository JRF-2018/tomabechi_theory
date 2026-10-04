# Theorem2.lean 解説

> 対象: [`Theorem2.lean`](../Theorem2.lean)（定理2：共有TCZへの収束の有限主体コア）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| はさみうちの原理 | 0 以上で、0 に収束するものに抑えられた量は 0 に収束する。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理2（**共有 TCZ への収束**：複数の主体が互いに結びついて、全員が同じ目標領域 TCZ へ近づき、互いの表象が一致する）の**有限主体の核**です。

- 主体 \(i\)（有限個）ごとの**個人残差**（自分の目標からのずれ）と、結合辺 \(e\)（主体の対）ごとの**辺の不整合**（2 人の表象のずれ）を、正の重みで足した**共有残差** \(\Phi_2\) を定義します。
- \(\Phi_2\) が指数的に減るなら、各個人残差・各辺の不整合も**明示的な指数の上界**で減り、共有 TCZ への距離も指数的に減ることを示します。
- 結合グラフが連結なら、\(\Phi_2=0\)（共有 TCZ 上）で**全員の表象が一致**します。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 共有残差と評価 | `sharedResidual`, `weightedIndividual_le_*`, `weightedEdge_le_sharedResidual` |
| 連結性と一致 | `adjacent`, `representation_agreement_of_connected` |
| 指数の評価 | `component_exponential_bound`, `individual_residual_exponential_bound`, `edge_mismatch_exponential_bound`, `shared_tcz_distance_exponential_decay`, `exponential_envelope_tendsto_zero*` |
| 構造体（表象値の不整合） | `SharedResidualSystem` とその補題、`theorem2_conditional_conclusion`, `theorem2_tendsto_zero` |
| 構造体（状態対の不整合） | `StatePairResidualSystem` とその補題、`theorem2_state_pair_*`, `theorem2_reachable_*` |
| 両者の関係 | `toStatePairResidualSystem` と同定の補題 |

### 0.3 このファイルが証明していないこと

- **共有零集合（共有 TCZ）への距離の収束**には、論文どおり**非空性・下降条件（散逸）・誤差境界**が別に必要で、ここでは**導かず仮定**します（「共有残差 \(\Phi_2\) の a.e. 指数散逸」「距離の 2 乗 \(\le C\Phi_2\)」を入力として受け取る）。
- 結合や最適方策だけから、それらの条件が導かれるとは主張しません。**条件付き**の結論です。
- 辺の不整合関数の零点が「表象の一致」と同値であること（`mismatch_zero_iff`）は、構造体の**仮定**です。
- 主体と結合辺は**有限個**に限ります。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理2：共有 TCZ への収束の、有限主体の核**
>
> 有限個の主体・有限個の結合辺について、非負の個人残差と、辺の不整合を、正の重みで足した共有残差が、指数的に減衰するとき、各個人残差と各辺の不整合も、明示的な指数の上界をもつことを示す。共有の零集合への距離の収束には、原文どおり、別途、非空性・下降条件・誤差境界が必要であり、ここではそれらを導いたとは主張しない。

途中に、状態対の不整合を扱う節の説明コメントがあります：

> **状態の対に直接作用する辺の不整合**：旧 `SharedResidualSystem` は、\(S_{ij}\) を表象の値から計算する特殊形だった。以下では、主体の依存型の状態を直接受け取る、辺のコストを定義する。零点の条件だけが表象の一致を指定し、正の重み付きの有限和から、各成分の評価・連結な整合を得る。

さらに別の節の説明：

> 構造化された結果は、定理2の定量的な出力を、読みやすく、下流の証明が別々に使えるようにする。

名前空間は `Tomabechi.Theorem2`。`open Finset`、`open MeasureTheory`。

---

<a id="Tomabechi.Theorem2.sharedResidual"></a>

## 定義 `sharedResidual`

### 式

$$\Phi_2(t)=\sum_iw_i\,r_i(t)+\sum_e\gamma_e\,s_e(t)$$

### Lean のコメント（日本語訳）

> 個人の閾値の超過の残差と、有限個の結合辺の不整合を集約した、共有残差。辺の両端の順序は、入力のデータで固定される。対称性は、各辺の不整合の関数の側の条件で扱う。

### 定義の説明

個人ごとの「目標からのずれ」\(r_i\)（重み \(w_i\)）と、結合辺ごとの「2 人の表象のずれ」\(s_e\)（重み \(\gamma_e\)）の、重み付き和です。これが 0 であることが「全員が目標に到達し、表象が一致している」ことを表します。

### 証明の概略

1. 定義：`∑ i, w i * individual i t + ∑ e, γ e * edgeMismatch e t`。

----

<a id="Tomabechi.Theorem2.weightedIndividual_le_sum"></a>

## 補題 `weightedIndividual_le_sum`

### 式

$$w_ir_i\le\sum_jw_jr_j\quad(\text{各項が非負})$$

### Lean のコメント（日本語訳）

> 非負の個人の項は、個人残差の有限和以下である。

### 補題の説明

非負の項の和は、その中の 1 項以上です。

### 証明の概略

1. `Finset.single_le_sum`（非負項の和は各項以上）。

----

<a id="Tomabechi.Theorem2.weightedIndividual_le_sharedResidual"></a>

## 補題 `weightedIndividual_le_sharedResidual`

### 式

$$w_ir_i\le\Phi_2$$

### Lean のコメント（日本語訳）

> 定義した共有残差は、各個人の重み付きの残差を上回る。他の個人の項と辺の項が非負であることを仮定する。

### 補題の説明

共有残差は、各個人の（重み付き）残差以上です。

### 証明の概略

1. `weightedIndividual_le_sum` に非負の辺の項の和を足す。

----

<a id="Tomabechi.Theorem2.weightedEdge_le_sharedResidual"></a>

## 補題 `weightedEdge_le_sharedResidual`

### 式

$$\gamma_es_e\le\Phi_2$$

### Lean のコメント（日本語訳）

> 定義した共有残差は、各結合辺の重み付きの不整合を上回る。

### 補題の説明

辺の不整合も同様です。

### 証明の概略

1. 非負の項の和は各項以上（`Finset.single_le_sum`）。

----

<a id="Tomabechi.Theorem2.adjacent"></a>

## 定義 `adjacent`

### 式

$$i\sim j\ \Longleftrightarrow\ (i,j)\in\text{edges}\ \lor\ (j,i)\in\text{edges}$$

### Lean のコメント（日本語訳）

> 無向の辺として解釈した、有限グラフの隣接関係。

### 定義の説明

辺の向きを無視した隣接です。

### 証明の概略

1. 定義：`(i,j) ∈ edges ∨ (j,i) ∈ edges`。

----

<a id="Tomabechi.Theorem2.representation_agreement_of_connected"></a>

## 補題 `representation_agreement_of_connected`

### 式

$$\text{連結},\ \text{全辺で}\ h_i=h_j\ \Longrightarrow\ \forall i,j,\ h_i=h_j$$

### Lean のコメント（日本語訳）

> 連結なグラフでは、全辺の表象の一致から、全主体の間の表象の一致が従う。`connected` は隣接関係の反射推移閉包として与え、零点の同値性は `hEdgeEq` に明示する。

### 補題の説明

隣り合う主体どうしの表象が一致していれば、連結なグラフでは**全員の表象が一致**します（推移的に伝わる）。

### 証明の概略

1. `Relation.ReflTransGen` についての帰納法：各ステップで隣接する 2 人の表象が一致（`hEdgeEq`）。

----

<a id="Tomabechi.Theorem2.component_exponential_bound"></a>

## 補題 `component_exponential_bound`

### 式

$$a\,r(t)\le\Phi_2(t)\le\Phi_2(t_0)e^{-c(t-t_0)}\ \Longrightarrow\ r(t)\le\frac{\Phi_2(t_0)}{a}e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 集約された残差から、個人・辺ごとの誤差を取り出す、定量的な補題。重みの正値、全項の非負性、個別の項が共有残差以下であることを、明示的な入力にする。

### 補題の説明

共有残差が指数的に減るなら、各成分（重みで割った）も指数的に減る、という計算です。

### 証明の概略

1. 仮定の不等式を重み \(a>0\) で割る（`div_le_iff₀`）。

----

<a id="Tomabechi.Theorem2.exponential_envelope_tendsto_zero"></a>

## 補題 `exponential_envelope_tendsto_zero`

### 式

$$0\le f(t)\le A\,e^{-\lambda(t-t_0)},\ \lambda>0\ \Longrightarrow\ f(t)\to0$$

### Lean のコメント（日本語訳）

> 正の指数率をもつ非負関数が、指数の包絡で抑えられるなら、その関数は零へ収束する。

### 補題の説明

指数関数的に減る関数に抑えられた非負関数は 0 に収束します（はさみうち）。

### 証明の概略

1. `squeeze_zero` と `Real.tendsto_exp_neg_atTop_nhds_zero` 系。

----

<a id="Tomabechi.Theorem2.exponential_envelope_tendsto_zero_rate_two"></a>

## 補題 `exponential_envelope_tendsto_zero_rate_two`

### 式

$$f(t)\le A\,e^{-2c(t-t_0)}\ \Longrightarrow\ f(t)\to0$$

### Lean のコメント（日本語訳）

> \(\exp(-2ct)\) の包絡に対する、同じ比較の補題。

### 補題の説明

指数率が \(2c\) の場合です。

### 証明の概略

1. 上の補題の特別な場合。

----

<a id="Tomabechi.Theorem2.individual_residual_exponential_bound"></a>

## 補題 `individual_residual_exponential_bound`

### 式

$$r_i(t)\le\frac{\text{initialBound}}{w_i}e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 共有残差の指数の評価を、個人の残差へ適用した、定量的な帰結。有限和の各項が非負であるため、共有残差が個人の重み付きの残差を支配する。

### 補題の説明

各個人の残差も指数的に減ります。

### 証明の概略

1. `weightedIndividual_le_sharedResidual` と `component_exponential_bound`。

----

<a id="Tomabechi.Theorem2.edge_mismatch_exponential_bound"></a>

## 補題 `edge_mismatch_exponential_bound`

### 式

$$s_e(t)\le\frac{\text{initialBound}}{\gamma_e}e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 共有残差の指数の評価を、辺の不整合へ適用した、定量的な帰結。

### 補題の説明

各辺の不整合（2 人の表象のずれ）も指数的に減ります。

### 証明の概略

1. `weightedEdge_le_sharedResidual` と `component_exponential_bound`。

----

<a id="Tomabechi.Theorem2.shared_tcz_distance_exponential_decay"></a>

## 補題 `shared_tcz_distance_exponential_decay`

### 式

$$\Phi_2'\le-2c\Phi_2,\ \ \operatorname{dist}(x,\text{sharedTCZ})^2\le C\Phi_2\ \Longrightarrow\ \operatorname{dist}(x(t),\text{sharedTCZ})\le\sqrt{C\Phi_2(t_0)}\,e^{-c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 共有残差の指数的な散逸と、距離の誤差の境界から、共有 TCZ への定量的な収束を得る。`sharedPotential` の微分の条件と距離の境界は、入力の条件であり、結合や最適方策だけからそれらが導かれるとは主張しない。原文の共有零集合の族に対する、条件付きの結論である。

### 補題の説明

**共有 TCZ への距離の指数収束**：共有残差が指数的に減り（\(\Phi_2'\le-2c\Phi_2\)）、距離の 2 乗が共有残差の定数倍で抑えられる（誤差境界）なら、距離は \(e^{-c t}\) の速さで減ります。

### 証明の概略

1. 定理1の `individual_tcz_distance_decay_of_ac_ae_derivative`（AC・a.e. 下降・誤差境界から TCZ への距離の指数評価）を、共有残差 \(\Phi_2\) と共有 TCZ に対して適用する（19 行）。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem"></a>

## 構造体 `SharedResidualSystem`

### 式

$$\text{State}_i,\ \text{repr}_i,\ \text{endpoint}_e,\ r_i=\max(V_i-\theta_i,0),\ s_e(u,v),\ w_i,\gamma_e>0,\ s_e(u,v)=0\Leftrightarrow u=v$$

### Lean のコメント（日本語訳）

> 定理2の共有残差を、主体ごとの状態・個人残差・辺の不整合から組み立てるデータ。各辺のコストの零点の同値性は、原文の \(S_{ij}=0\iff h_i(x_i)=h_j(x_j)\) に対応する。

### 定義の説明

主体 \(i\) の状態 `State i`、表象への写像 `repr`、辺の端点 `endpoint`、個人残差（基礎ポテンシャルから閾値を引いた正の部分）、辺の不整合 `mismatch`（表象の値から計算：対称・非負・零点は表象の一致）、正の重み、をまとめた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.edgeResidual"></a>

## 定義 `edgeResidual`

### 式

$$S_{ij}(x_i,x_j)=s_e(h_i(x_i),h_j(x_j),t)$$

### Lean のコメント（日本語訳）

> 辺 \(e\) が評価する、対称な不整合 \(S_{ij}(x_i,x_j)\)。

### 定義の説明

辺 \(e\) の両端の主体の状態の表象を取り出して、不整合を計算します。

### 証明の概略

1. 定義：`D.mismatch e (D.repr ...) (D.repr ...) t`。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.potential"></a>

## 定義 `potential`

### 式

$$\Phi_2(x,t)=\sum_iw_ir_i+\sum_e\gamma_eS_e$$

### Lean のコメント（日本語訳）

> 主体ごとの非負の残差と、結合辺の非負の不整合を、正の重みで足した \(\Phi_2\)。

### 定義の説明

共有残差を、状態 \(x=(x_i)\) の関数として定義したものです。

### 証明の概略

1. 定義：`sharedResidual` と同じ形。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.potential_eq_zero_iff_components_eq_zero"></a>

## 補題 `potential_eq_zero_iff_components_eq_zero`

### 式

$$\Phi_2=0\ \Longleftrightarrow\ \forall i,\ r_i=0\ \wedge\ \forall e,\ S_e=0$$

### Lean のコメント（日本語訳）

> \(\Phi_2=0\) は、個人残差・辺の不整合の、同時の消失と同値である。正の重みと、全項の非負性を使う、定理2の共有零集合の、基本的な構造の補題。

### 補題の説明

共有残差が 0 になるのは、すべての成分が 0 のときだけです（全部非負で重みが正だから）。

### 証明の概略

1. 非負項の有限和が 0 ⇔ 各項が 0（`Finset.sum_eq_zero_iff_of_nonneg`）、重みが正。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.representations_agree_on_edges_of_potential_eq_zero"></a>

## 補題 `representations_agree_on_edges_of_potential_eq_zero`

### 式

$$\Phi_2=0\ \Longrightarrow\ h_i(x_i)=h_j(x_j)\ (\text{各辺の両端})$$

### Lean のコメント（日本語訳）

> 共有残差が零なら、各結合辺の上で、全主体の表象が一致する。

### 補題の説明

共有残差 0 なら、辺の両端の表象は一致します（辺の不整合 0 ⇔ 表象の一致）。

### 証明の概略

1. `potential_eq_zero_iff_components_eq_zero` と `mismatch_zero_iff`。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.systemAdjacent"></a>

## 定義 `systemAdjacent`

### 式

$$i\sim j\ \Longleftrightarrow\ \exists e,\ \text{endpoint}(e)=(i,j)\ \lor\ (j,i)$$

### Lean のコメント（日本語訳）

> 構造データ `endpoint` が定める、無向の隣接関係。

### 定義の説明

辺で結ばれた主体どうしの隣接です。

### 証明の概略

1. 定義：存在量化。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.representations_agree_of_connected"></a>

## 補題 `representations_agree_of_connected`

### 式

$$\Phi_2=0,\ \text{連結}\ \Longrightarrow\ \forall i,j,\ h_i(x_i)=h_j(x_j)$$

### Lean のコメント（日本語訳）

> 共有残差が零で、辺のグラフが連結なら、全主体の表象が一致する。

### 補題の説明

**共有 TCZ 上では全員の表象が一致する**（グラフが連結なら）という、定理2の結論の一つです。

### 証明の概略

1. 辺ごとの一致（上の補題）と `ReflTransGen` の帰納法。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.sharedTCZ"></a>

## 定義 `sharedTCZ`

### 式

$$\mathrm{sharedTCZ}(K,t)=\{x\in K\mid\Phi_2(x,t)=0\}$$

### Lean のコメント（日本語訳）

> 共有残差が零となる、閉の到達可能な領域の内の、時刻ごとの TCZ のスライス。

### 定義の説明

到達可能な領域 \(K\) の中で、共有残差が 0 になる点（=全員が目標に達し、表象が一致している状態）の集合です。

### 証明の概略

1. 定義：`{x ∈ K | D.potential x t = 0}`。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.theorem2_conditional_conclusion"></a>

## 定理 `theorem2_conditional_conclusion`

### 式

$$\operatorname{dist}(x(t),\text{sharedTCZ})\le\sqrt{C\Phi_2(t_0)}e^{-c(t-t_0)},\ \ r_i\le\tfrac{\Phi_2(t_0)}{w_i}e^{-2c(t-t_0)},\ \ s_e\le\tfrac{\Phi_2(t_0)}{\gamma_e}e^{-2c(t-t_0)},\ \ h_i=h_j\ (\text{on sharedTCZ})$$

### Lean のコメント（日本語訳）

> 定理2の条件付きの結論を、一括して返す。共通の Lyapunov 残差の AC・a.e. の指数散逸、共有 TCZ の非空性、距離の誤差境界を仮定し、共有 TCZ までの距離と、個人残差・辺の不整合の定量的な減衰を得る。さらに、連結性から、共有 TCZ の上では、全主体の表象が一致する。

### 補題の説明

**定理2の主結論（条件付き）**：共有 TCZ への距離（速さ \(c\)）、個人残差と辺の不整合（速さ \(2c\)）の指数減衰、共有 TCZ 上での表象の一致。仮定は、共有残差の絶対連続性・a.e. の指数散逸・距離の誤差境界・共有 TCZ の非空性です。

### 証明の概略

1. 共有残差 \(\Phi_2\) は個人残差と辺の不整合の重み付き和で、すべて非負。定理1の `lyapunov_exponential_decay_of_ac_ae_derivative` で \(\Phi_2(t)\le\Phi_2(t_0)e^{-2c(t-t_0)}\)。
2. 距離の評価は共有 TCZ に対する定理1の距離評価。
3. 個人残差・辺の不整合は、和の各項が \(\Phi_2\) 以下であること（`component_exponential_bound`）から、重みで割った指数評価。
4. 共有零集合上では、辺の不整合が 0 なので表象が連結なグラフの上で一致する（`representations_agree_of_connected`）（91 行）。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.theorem2_tendsto_zero"></a>

## 定理 `theorem2_tendsto_zero`

### 式

$$\text{全終端時刻で条件が成り立つ}\ \Longrightarrow\ \operatorname{dist},\ r_i,\ s_e\ \to0$$

### Lean のコメント（日本語訳）

> 任意の終端時刻で、上の条件付きの評価が使えるときの、定性的な収束の API。各結論は、指数の包絡から導く。共有残差・軌道・距離の境界に関する大域的な条件は、入力の仮定である。

### 補題の説明

指数の包絡（`exponential_envelope_tendsto_zero`）から、距離・個人残差・辺の不整合がすべて 0 に収束することを示します。

### 証明の概略

1. `theorem2_conditional_conclusion` を各終端時刻 \(t\) に適用し、`exponential_envelope_tendsto_zero(_rate_two)`。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem"></a>

## 構造体 `StatePairResidualSystem`

### 式

$$s_e:\ \text{State}_{e.1}\times\text{State}_{e.2}\to\mathbb R\ \ (\text{表象を経由しない状態対の不整合})$$

### Lean のコメント（日本語訳）

> 表象の写像を経由せず、辺の両端の状態に、直接作用する不整合のコスト。

### 定義の説明

`SharedResidualSystem` の拡張です。辺の不整合が表象の値ではなく**状態の対**に直接作用します（辺の向きの反転 `reverseEdge` と、反転に関する対称性を持つ）。零点の条件だけが表象の一致を指定します。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.potential"></a>

## 定義 `potential`

### 式

$$\Phi_2(x,t)=\sum_iw_ir_i(x_i,t)+\sum_e\gamma_es_e(x_{e.1},x_{e.2},t)$$

### Lean のコメント（日本語訳）

> 依存型の状態の上の \(\Phi_2\)。辺の項は、表象ではなく、状態の対を直接評価する。

### 定義の説明

状態対版の共有残差です。

### 証明の概略

1. 定義：有限和。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.potential_eq_zero_iff_components_eq_zero"></a>

## 補題 `potential_eq_zero_iff_components_eq_zero`

### 式

$$\Phi_2=0\ \Longleftrightarrow\ \text{個人残差・全状態辺不整合が同時に消える}$$

### Lean のコメント（日本語訳）

> \(\Phi_2=0\) は、個人残差と、全状態辺の不整合の、同時の消失と同値である。

### 補題の説明

`SharedResidualSystem` の版と同じ補題の状態対版です。

### 証明の概略

1. 非負項の有限和が 0 ⇔ 各項が 0。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.repr_eq_of_mismatch_eq_zero"></a>

## 補題 `repr_eq_of_mismatch_eq_zero`

### 式

$$s_e=0\ \Longrightarrow\ h_{e.1}(x_{e.1})=h_{e.2}(x_{e.2})$$

### Lean のコメント（日本語訳）

> 零になった、状態の辺のコストは、その端点の表象を一致させる。

### 補題の説明

`mismatch_zero_iff` そのものです。

### 証明の概略

1. `mismatch_zero_iff`。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.representations_agree_of_potential_eq_zero"></a>

## 補題 `representations_agree_of_potential_eq_zero`

### 式

$$\Phi_2=0,\ \text{連結}\ \Longrightarrow\ \forall i,j,\ h_i(x_i)=h_j(x_j)$$

### Lean のコメント（日本語訳）

> 共有残差が零なら、任意の連結なグラフで、全表象の一致が得られる。成分の零点の同値性だけを使う。

### 補題の説明

状態対版の連結性による表象の一致です。

### 証明の概略

1. `repr_eq_of_mismatch_eq_zero` と `ReflTransGen` の帰納法。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.sharedTCZ"></a>

## 定義 `sharedTCZ`

### 式

$$\{x\in K\mid\Phi_2(x,t)=0\}$$

### Lean のコメント（日本語訳）

> 閉の到達可能な領域に制限した、共有 TCZ。

### 定義の説明

状態対版の共有 TCZ です。

### 証明の概略

1. 定義：集合。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.theorem2_state_pair_conditional_conclusion"></a>

## 定理 `theorem2_state_pair_conditional_conclusion`

### 式

$$\begin{aligned}
&\text{仮定（区間 }[t_0,t]\text{ 上）：}\ \Phi_2(x(s),s)\ \text{が AC},\ \ \Phi_2'\le-2c\,\Phi_2\ \text{a.e.},\ \ \mathrm{dist}(x(s),\Omega_2(s))^2\le C\,\Phi_2,\ \ \Omega_2(s)\ne\emptyset,\ x(s)\in K\\
&\Longrightarrow\ \ \mathrm{dist}(x(t),\Omega_2(t))\le\sqrt{C\,\Phi_2(t_0)}\,e^{-c(t-t_0)},\quad
\text{個人残差}_i\le\frac{\Phi_2(t_0)}{w_i}e^{-2c(t-t_0)},\quad
\text{不整合}_e\le\frac{\Phi_2(t_0)}{w_e}e^{-2c(t-t_0)}\\
&\text{さらに（グラフが連結なら）共有零集合 }\Omega_2\text{ 上で全主体の表象が一致}
\end{aligned}$$
（\(\Omega_2=\)`sharedTCZ K`、\(w_i,w_e\) は個人・辺の重み。仮定は「条件付き」であり、導出していない。）

### Lean のコメント（日本語訳）

> 状態の対の不整合の版の、定理2。原文の、正準の個人残差・共有残差の AC/散逸・距離の誤差境界を入口にし、共有 TCZ への距離の指数評価、個人残差と状態対の不整合の指数評価、連結したグラフ上の表象の一致、個人残差の極限を、1 つの結論として返す。不整合は、端点の状態に直接作用し、表象の写像を通じた因子化を、仮定しない。

### 補題の説明

`theorem2_conditional_conclusion` の状態対版です（表象を経由しない辺の不整合）。

### 証明の概略

1. `SharedResidualSystem` 版と同じ筋：定理1の `lyapunov_exponential_decay_of_ac_ae_derivative`（\(\Phi_2\) の指数減衰）と `individual_tcz_distance_decay_of_ac_ae_derivative`（共有 TCZ への距離）。
2. 個人残差・辺の不整合は `component_exponential_bound`（各項 \(\le\Phi_2\)）で指数評価。
3. 零集合の特徴づけ `potential_eq_zero_iff_components_eq_zero` と `repr_eq_of_mismatch_eq_zero`（辺の不整合 0 なら表象が等しい）で、共有零集合上での表象の一致（103 行）。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.theorem2_state_pair_tendsto_zero"></a>

## 定理 `theorem2_state_pair_tendsto_zero`

### 式

$$\text{全終端時刻}\ \Longrightarrow\ \operatorname{dist},\ r_i,\ s_e\ \to0$$

### Lean のコメント（日本語訳）

> 状態の対の不整合の版の、大域的な収束。すべての終端時刻で、原文の区間の条件が成り立つとき、有限時刻の版から、距離・個人残差・各状態対の不整合の指数の包絡を取り出し、各々の極限を得る。

### 補題の説明

状態対版の収束です。

### 証明の概略

1. 上の定理と `exponential_envelope_tendsto_zero`。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.theorem2_reachable_state_pair_tendsto_zero"></a>

## 定理 `theorem2_reachable_state_pair_tendsto_zero`

### 式

$$\text{sharedTCZ を閉到達可能集合 }\overline{\bigcup_t\text{reachableAt}(t)}\text{ で作る}\ \Longrightarrow\ \text{極限}$$

### Lean のコメント（日本語訳）

> 定理2の共有 TCZ を、選択済みの共同方策の、時刻ごとの到達の集合から作った閉包へ接続する。軌道の所属・共有零のスライスの非空性・散逸・誤差境界は、同じ方策の到達データに対する入力として保ち、共有距離・個人残差・辺の不整合の極限を返す。

### 補題の説明

定理1の `closedLoopReachableSet`（時刻ごとの到達集合の閉包）を共有 TCZ の領域にした版です。

### 証明の概略

1. `closedLoopReachableSet`（Theorem1）を \(K\) として `theorem2_state_pair_tendsto_zero` を適用。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.ReachableStatePairConclusion"></a>

## 構造体 `ReachableStatePairConclusion`

### 式

$$\text{軌道は閉到達集合内},\ \text{定量評価},\ \text{共有 TCZ 上の表象一致},\ \text{距離}\to0,\ \ r_i\to0,\ \ s_e\to0$$

### Lean のコメント（日本語訳）

> （コメントなし：構造化された結果は、定理2の定量的な出力を、読みやすく、下流の証明が別々に使えるようにする。）

### 定義の説明

定理2の結論（軌道が閉到達集合にあること、定量的な指数評価、共有 TCZ 上の表象の一致、距離・個人残差・辺の不整合の極限）を、フィールドとして束ねた `Prop` の構造体です。

### 証明の概略

1. 構造体（命題）なので証明はない。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.theorem2_reachable_state_pair_quantitative_conclusion"></a>

## 定理 `theorem2_reachable_state_pair_quantitative_conclusion`

### 式

$$\text{ReachableStatePairConclusion}$$

### Lean のコメント（日本語訳）

> 同じ閉到達可能 TCZ の入口から、定理2の距離・個人残差・辺の不整合の指数率と、それぞれの極限を、まとめて返す。有限時間の部分は、条件付きの定量の核を、各終端時刻へ適用する。

### 補題の説明

`ReachableStatePairConclusion` のインスタンスを構成する定理です。

### 証明の概略

1. 軌道が到達可能集合に入ること（`mem_closedLoopReachableSet_of_mem_reachableAt`）から、軌道は閉到達可能集合 \(K\) に入る。
2. 各終端時刻 \(t\) に `theorem2_state_pair_conditional_conclusion`（\(K=\)`closedLoopReachableSet`）を適用して指数評価を得る。
3. 極限は `theorem2_state_pair_tendsto_zero`。これらを `ReachableStatePairConclusion` のフィールドにまとめる（62 行）。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.toStatePairResidualSystem"></a>

## 定義 `toStatePairResidualSystem`

### 式

$$\text{表象値の不整合}\ \hookrightarrow\ \text{各無向辺の 2 つの向き（重み半分）の状態対の不整合}$$

### Lean のコメント（日本語訳）

> 表象値の不整合の API を、各無向辺の、2 つの向きをもつ、状態対の API へ埋め込む。辺の重みを半分にするため、二方向を合計した共有残差は、元の \(\Phi_2\) と一致する。

### 定義の説明

旧版（表象値）を新版（状態対）の特殊ケースとして埋め込みます。辺 \(e\) を 2 本の向きつき辺 \((e,\text{true}),(e,\text{false})\) にして重みを半分にします。

### 証明の概略

1. 定義：`E × Bool` を辺の型にし、`reverseEdge` は Bool の反転、重みは半分。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.potential_toStatePairResidualSystem_eq"></a>

## 補題 `potential_toStatePairResidualSystem_eq`

### 式

$$\Phi_2^{\text{pair}}=\Phi_2$$

### Lean のコメント（日本語訳）

> 二方向・半重みの状態対の残差は、元の表象値の残差と一致する。

### 補題の説明

埋め込んでも共有残差は同じです（2 方向 × 半分の重み）。

### 証明の概略

1. 辺の和を `E × Bool` の和に展開し、2 つの向きで同じ値の半分ずつを足す。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.sharedTCZ_toStatePairResidualSystem_eq"></a>

## 補題 `sharedTCZ_toStatePairResidualSystem_eq`

### 式

$$\mathrm{sharedTCZ}^{\text{pair}}=\mathrm{sharedTCZ}$$

### Lean のコメント（日本語訳）

> 無向辺の状態対への持ち上げでも、時刻ごとの共有 TCZ は、元の集合と一致する。

### 補題の説明

埋め込んでも共有 TCZ は同じです。

### 証明の概略

1. 上の補題から集合として一致。

----

<a id="Tomabechi.Theorem2.SharedResidualSystem.edge_mismatch_toStatePairResidualSystem_eq"></a>

## 補題 `edge_mismatch_toStatePairResidualSystem_eq`

### 式

$$s^{\text{pair}}_{(e,\text{false})}=S_e$$

### Lean のコメント（日本語訳）

> 持ち上げた辺 \((e,\text{false})\) の直接の状態の不整合は、元の辺の残差そのものである。

### 補題の説明

埋め込んだ辺の不整合は、元の辺の不整合に一致します。

### 証明の概略

1. 定義の展開。

----


## コメント修正記録

（なし）
