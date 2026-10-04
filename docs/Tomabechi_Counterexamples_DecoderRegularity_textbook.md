# Tomabechi/Counterexamples/DecoderRegularity.lean 解説

> 対象: [`Tomabechi/Counterexamples/DecoderRegularity.lean`](../Tomabechi/Counterexamples/DecoderRegularity.lean)（定理19の出力σ代数の正則性が必要であることの反例（監査用の証人））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19・22の「**行動が目標を区別すれば CMI は \(H(G|X)\) に等しい**」という結論には、出力の空間 \(Y\) が**十分に正則**（目標の違いを観測できる可測構造をもつ）という仮定が**必要**であることを示す**反例（監査用の証人）**です。

具体例：出力の空間を「2 値の集合に**自明な σ 代数**（空集合と全体だけ）を与えたもの」`IndiscreteBit` にします。この空間では 2 つの値を**測度では区別できません**。

- 集合としては単射（`encode`）で、可測でもあるのに、**可測な左逆（復号器）がない**。
- 同時法則は「目標と無関係な定数出力」の法則と**一致**し、**相互情報量は 0**。
- ところが目標のエントロピーは \(\log2>0\)。したがって **CMI \(<H(G|X)\)**（情報を達成しない）。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 自明 σ 代数の 2 値の型と符号化 | `IndiscreteBit`, `encode`, `encode_injective`, `encode_measurable` |
| 可測な復号器がない | `no_measurable_leftInverse`, `not_all_action_graphs_measurable` |
| 測度として区別できない | `dirac_encode_eq`, `dirac_goal_encode_eq`, `klDiv_dirac_encode_eq_zero` |
| 2 値の等重みゴールの同時法則 | `binaryEncodedJoint`, `binaryConstantJoint`, ..._eq_constant, `binaryGoalMeasure` ほか |
| ゴールのエントロピー \(\log2\) | `binaryGoalEntropy_eq_log_two`, `binaryGoalEntropy_pos` |
| 相互情報量が 0 | `binaryEncodedJoint_mutualInformation_eq_zero`, `binaryEncodedJoint_information_lt_goalEntropy` |
| 条件付きの版（`Unit` 文脈） | `binaryContextLaw` と、その CMI が 0、`log 2` との比較 |

### 0.3 このファイルが証明していないこと（重要）

- これは**数学的な監査用の証人**であり、認知モデルの具体例ではありません。**定理19・22の原文そのものの反例ではありません**。標準 Borel 出力を含む、通常の**正則な**出力に対する反例でもありません。
- 「出力の可測構造が目標を区別できなければ、情報の達成は失敗する」という**仮定の必要性**を示すだけです。`MeasureCMI.lean` の定理が `MeasurableEq Y` や行動のグラフの可測性を仮定する理由の説明です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理19：出力の σ 代数の正則性が必要であることの反例（監査用の証人）**
>
> 出力の可測空間が、2 値のゴールを区別できない（自明な σ 代数）とき、集合として単射で可測な、有限ゴールの符号化でも、可測な左逆（復号器）は存在せず、KL 型の条件付き相互情報量は、ゴールのエントロピー `log 2` を達成しない。これは、「出力が標準 Borel 等の正則な空間である」という仮定を省けないことの、数学的な証人であり、定理19・22の原文そのものの反例ではない。

（コメント修正記録のとおり、修正した文章です。）名前空間は `Tomabechi.Theorem19_22.DecoderRegularityWitness`。`open Tomabechi.Theorem22`、`open MeasureTheory ProbabilityTheory`。

---

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.IndiscreteBit"></a>

## 構造体 `IndiscreteBit`

### 式

$$\{\text{bit}:\text{Bool}\},\ \ \sigma\text{-代数}=\{\varnothing,\text{全体}\}$$

### Lean のコメント（日本語訳）

> 出力の可測構造の監査用。2 値の集合に、自明な σ 代数だけを与える。認知モデルの具体例ではなく、単射性と可測な復元可能性の差を示す、数学的な証人である。

### 定義の説明

2 つの値 `true`/`false` を持つ型ですが、可測集合は空集合と全体だけ（**2 つの値を区別する集合が可測でない**）。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.instance@L28"></a>

## インスタンス `instance@L28`

### 式

$$\mathcal M=\bot\ (\text{自明な σ 代数})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`IndiscreteBit` の可測空間の構造を、最小の σ 代数（`⊥`）に定めます。

### 証明の概略

1. 定義：`MeasurableSpace IndiscreteBit := ⊥`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.encode"></a>

## 定義 `encode`

### 式

$$\mathrm{encode}(b)=\langle b\rangle$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`Bool` の値をそのまま `IndiscreteBit` に入れる符号化です（集合としては恒等写像）。

### 証明の概略

1. 定義：`⟨b⟩`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.encode_injective"></a>

## 補題 `encode_injective`

### 式

$$\mathrm{encode}\ \text{は単射}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

集合としては異なる値が異なる値に写ります。

### 証明の概略

1. コンストラクタの単射性。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.encode_measurable"></a>

## 補題 `encode_measurable`

### 式

$$\mathrm{encode}\ \text{は可測}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自明な σ 代数への写像は、逆像が空集合か全体になるので、いつでも可測です。

### 証明の概略

1. 可測空間 `⊥` への写像の可測性。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.no_measurable_leftInverse"></a>

## 補題 `no_measurable_leftInverse`

### 式

$$\neg\,\exists\,\text{可測な}\ r:\ r\circ\mathrm{encode}=\mathrm{id}$$

### Lean のコメント（日本語訳）

> 可測かつ単射の有限ゴールの符号化でも、出力の σ 代数がゴールを区別しないと、可測な左逆は存在しない。任意の可測な \(Y\) の版から、出力の分離性を省けないことの証人。

### 補題の説明

可測な復号器 \(r:\text{IndiscreteBit}\to\text{Bool}\) は定数写像しかありません（自明な σ 代数からの可測写像）。定数写像は `encode` の左逆になれません。

### 証明の概略

1. 可測な \(r\) は定数（逆像 \(\{r=\text{true}\}\) が空か全体）。
2. 定数なら \(r(\text{encode}\,\text{true})=r(\text{encode}\,\text{false})\) で、左逆の等式が両方成り立たず矛盾。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.not_all_action_graphs_measurable"></a>

## 補題 `not_all_action_graphs_measurable`

### 式

$$\neg\,\forall g,\ \{z\mid\mathrm{encode}(g)=z.2\}\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 可測な単射だけから、全ゴールの出力の一致の集合の可測性は導けない。単一の文脈・有限の 2 値のゴールの、監査用の証人であり、元の全体系の反証ではない。

### 補題の説明

`MeasureCMI.lean` で復号器の可測性に仮定した「行動のグラフ（出力の一致集合）の可測性」が、単射・可測から自動的には出ないことの確認です。

### 証明の概略

1. 一致集合 \(\{(u,y)\mid y=\text{encode}\,g\}\) は、自明な σ 代数では可測でない（空でも全体でもない）。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.dirac_encode_eq"></a>

## 補題 `dirac_encode_eq`

### 式

$$\delta_{\mathrm{encode}(b)}=\delta_{\mathrm{encode}(c)}$$

### Lean のコメント（日本語訳）

> 自明な σ 代数では、異なる符号の値は、Dirac の法則として区別できない。

### 補題の説明

可測集合が空か全体だけなので、どちらの点の Dirac 測度も同じ（全体に質量 1）です。

### 証明の概略

1. 測度の外延性：可測集合は空集合か全体だけで、どちらでも値が一致。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.dirac_goal_encode_eq"></a>

## 補題 `dirac_goal_encode_eq`

### 式

$$\delta_{(g,\mathrm{encode}\,b)}=\delta_{(g,\mathrm{encode}\,c)}$$

### Lean のコメント（日本語訳）

> ゴールは離散に観測できても、固定したゴールに付随する、出力の符号の値は、測度で区別できない。

### 補題の説明

ゴールを組にしても、出力側が区別できなければ Dirac 測度は同じです。

### 証明の概略

1. 積の σ 代数の生成集合（長方形）での値の一致。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.klDiv_dirac_encode_eq_zero"></a>

## 補題 `klDiv_dirac_encode_eq_zero`

### 式

$$\mathrm{KL}(\delta_{\mathrm{encode}\,b}\Vert\delta_{\mathrm{encode}\,c})=0$$

### Lean のコメント（日本語訳）

> 異なる符号の値の出力法則の間の KL は零。集合の上の単射性は、法則の識別性を保証しない。

### 補題の説明

測度として等しいので KL は 0 です。

### 証明の概略

1. `dirac_encode_eq` と `klDiv_self`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint"></a>

## 定義 `binaryEncodedJoint`

### 式

$$P=\tfrac12\delta_{(\text{true},\mathrm{encode}\,\text{true})}+\tfrac12\delta_{(\text{false},\mathrm{encode}\,\text{false})}$$

### Lean のコメント（日本語訳）

> 等重みの 2 値のゴールの、決定論的な符号化の同時法則。

### 定義の説明

目標が等確率で `true`/`false`、出力がそれを符号化した値、という同時法則です。

### 証明の概略

1. 定義：2 つの Dirac 測度の 1/2 ずつの混合。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryConstantJoint"></a>

## 定義 `binaryConstantJoint`

### 式

$$Q=\tfrac12\delta_{(\text{true},\mathrm{encode}\,\text{false})}+\tfrac12\delta_{(\text{false},\mathrm{encode}\,\text{false})}$$

### Lean のコメント（日本語訳）

> 同じゴールの混合に、定数の出力を付けた法則。

### 定義の説明

目標は同じ分布で、出力は目標に関係なく一定、という同時法則です。

### 証明の概略

1. 定義：同上（出力を定数に）。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_eq_constant"></a>

## 補題 `binaryEncodedJoint_eq_constant`

### 式

$$P=Q$$

### Lean のコメント（日本語訳）

> 単射の符号化と定数の出力は、この可測な出力では、同時法則として一致する。

### 補題の説明

**出力が目標を区別できないので、符号化した出力と定数の出力は同じ法則**です。

### 証明の概略

1. `dirac_goal_encode_eq` で各項が等しい。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_kl_constant_eq_zero"></a>

## 補題 `binaryEncodedJoint_kl_constant_eq_zero`

### 式

$$\mathrm{KL}(P\Vert Q)=0$$

### Lean のコメント（日本語訳）

> 2 つの同時法則の間の KL は零。これは、まだ CMI の参照の法則との同定ではない。

### 補題の説明

\(P=Q\) なので KL は 0 です。

### 証明の概略

1. `klDiv_self` と上の等式。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure"></a>

## 定義 `binaryGoalMeasure`

### 式

$$\mu_G=\tfrac12\delta_{\text{true}}+\tfrac12\delta_{\text{false}}$$

### Lean のコメント（日本語訳）

> 等重みの 2 値のゴールの周辺。

### 定義の説明

公平なコイン投げの分布です。

### 証明の概略

1. 定義：`(1/2) • dirac true + (1/2) • dirac false`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_isProbabilityMeasure"></a>

## 補題 `binaryEncodedJoint_isProbabilityMeasure`

### 式

$$P\ \text{は確率測度}$$

### Lean のコメント（日本語訳）

> 符号化の同時法則は確率の法則である。

### 補題の説明

全質量 1/2+1/2=1。

### 証明の概略

1. 全質量の計算。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_isProbabilityMeasure"></a>

## 補題 `binaryGoalMeasure_isProbabilityMeasure`

### 式

$$\mu_G\ \text{は確率測度}$$

### Lean のコメント（日本語訳）

> 2 値のゴールの周辺は確率の法則である。

### 補題の説明

同上。

### 証明の概略

1. 全質量の計算。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryConstantJoint_eq_product"></a>

## 補題 `binaryConstantJoint_eq_product`

### 式

$$Q=\mu_G\otimes\delta_{\mathrm{encode}\,\text{false}}$$

### Lean のコメント（日本語訳）

> 定数の出力の側は、ゴールの周辺と出力の Dirac の、独立な積の法則である。

### 補題の説明

定数の出力は目標と独立です。

### 証明の概略

1. 積測度の外延性（長方形での値）。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_singleton"></a>

## 補題 `binaryGoalMeasure_singleton`

### 式

$$\mu_G(\{g\})=\tfrac12$$

### Lean のコメント（日本語訳）

> 2 値のゴールの両方の質量は 1/2 である。

### 補題の説明

各目標の確率が 1/2 です。

### 証明の概略

1. Dirac 測度の混合の 1 点集合での値。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalEntropy_eq_log_two"></a>

## 補題 `binaryGoalEntropy_eq_log_two`

### 式

$$H(G)=\log2$$

### Lean のコメント（日本語訳）

> 2 値のゴールのエントロピーは \(\log2\) である。

### 補題の説明

公平なコインのエントロピー（1 ビット）です。

### 証明の概略

1. \(-2\cdot\tfrac12\log\tfrac12=\log2\)。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalEntropy_pos"></a>

## 補題 `binaryGoalEntropy_pos`

### 式

$$H(G)>0$$

### Lean のコメント（日本語訳）

> この監査用のゴールのエントロピーは正である。

### 補題の説明

\(\log2>0\)。

### 証明の概略

1. `Real.log_pos`（\(1<2\)）。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_eq_marginal_product"></a>

## 補題 `binaryEncodedJoint_eq_marginal_product`

### 式

$$P=P_G\otimes P_Y$$

### Lean のコメント（日本語訳）

> 符号化の法則は、実際の両方の周辺の積に等しい。

### 補題の説明

目標と出力は（測度としては）独立です。

### 証明の概略

1. \(P=Q\)（定数出力）と、`binaryConstantJoint_eq_product`、周辺の計算。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_mutualInformation_eq_zero"></a>

## 補題 `binaryEncodedJoint_mutualInformation_eq_zero`

### 式

$$I(G;Y)=\mathrm{KL}(P\Vert P_G\otimes P_Y)=0$$

### Lean のコメント（日本語訳）

> 単射の符号化の相互情報量を、実際の周辺の積への KL で評価すると、零になる。出力の可測構造が、ゴールの差を観測できないため、正のゴールのエントロピーを達成しない。

### 補題の説明

**情報が伝わらない**：独立なので相互情報量は 0 です。

### 証明の概略

1. `binaryEncodedJoint_eq_marginal_product` と `klDiv_self`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryEncodedJoint_information_lt_goalEntropy"></a>

## 補題 `binaryEncodedJoint_information_lt_goalEntropy`

### 式

$$I(G;Y)=0<\log2=H(G)$$

### Lean のコメント（日本語訳）

> 一般の可測な出力の、集合論的な単射の符号化は、KL の情報量で、正のゴールのエントロピーを達成するとは限らない。文脈で条件づけた CMI への `Unit` の埋め込みは、別に確認する。

### 補題の説明

**反例の核心**：単射なのに、情報量が目標のエントロピーに達しません。

### 証明の概略

1. `binaryEncodedJoint_mutualInformation_eq_zero` と `binaryGoalEntropy_pos`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw"></a>

## 定義 `binaryContextLaw`

### 式

$$\text{Unit 文脈}\ +\ \text{2 値ゴール}\ +\ \text{定数の出力核}\ \to\ \text{ConditionalMutualInformationLaw}$$

### Lean のコメント（日本語訳）

> `Unit` の文脈と、2 値のゴール・定数の出力の核から、CMI の法則を明示的に構成する。後で、単射の符号化が生成する法則との同定に用いる、独立の法則。

### 定義の説明

文脈が 1 点（`Unit`）の条件付き相互情報量の法則 `ConditionalMutualInformationLaw` として、上の例を表現したものです。

### 証明の概略

1. `ConditionalMutualInformationLaw` の各フィールドを（入力は Dirac 測度、核は定数の出力）で与える。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_joint_eq_reference"></a>

## 補題 `binaryContextLaw_joint_eq_reference`

### 式

$$\text{joint}=\text{referenceMeasure}$$

### Lean のコメント（日本語訳）

> `Unit` の文脈の法則は、その条件付き独立の参照の法則に等しい。

### 補題の説明

同時法則が参照測度（条件付き独立の同時分布）そのものです。

### 証明の概略

1. 定義から、二値文脈法則の結合法則と参照測度が定義上一致する（`rfl`）。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_cmi_eq_zero"></a>

## 補題 `binaryContextLaw_cmi_eq_zero`

### 式

$$\mathrm{KL}(\text{joint}\Vert\text{ref})=0$$

### Lean のコメント（日本語訳）

> 明示的な CMI の法則で計算した、条件付き相互情報量は零である。

### 補題の説明

CMI が 0 です。

### 証明の概略

1. `binaryContextLaw_joint_eq_reference` と `klDiv_self`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_inputEntropy_eq_log_two"></a>

## 補題 `binaryContextLaw_inputEntropy_eq_log_two`

### 式

$$H(G\mid X)=\log2$$

### Lean のコメント（日本語訳）

> `Unit` の文脈の、条件付きのゴールのエントロピーは \(\log2\) である。

### 補題の説明

文脈が 1 点なので \(H(G|X)=H(G)=\log2\)。

### 証明の概略

1. `binaryGoalEntropy_eq_log_two`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryGoalMeasure_map_encode"></a>

## 補題 `binaryGoalMeasure_map_encode`

### 式

$$(\mu_G)\text{ を }g\mapsto(g,\mathrm{encode}\,g)\text{ で押し出すと}\ P$$

### Lean のコメント（日本語訳）

> 2 値のゴールの測度を、単射の `encode` で出力へ写すと、既存の符号化の法則になる。

### 補題の説明

単射の符号化が生成する同時法則が `binaryEncodedJoint` であることの確認です。

### 証明の概略

1. 像測度の定義と Dirac 測度の混合の像。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_joint_eq_encoded"></a>

## 補題 `binaryContextLaw_joint_eq_encoded`

### 式

$$\text{joint}=(P)\ \text{に}\ ()\ \text{を付けたもの}$$

### Lean のコメント（日本語訳）

> 文脈の法則の `joint` は、符号化の法則に `Unit` を付けたものと一致する。

### 補題の説明

`Unit` 文脈の同時法則は、符号化の同時法則に `()` を添えたものです。

### 証明の概略

1. `binaryEncodedJoint_eq_constant` と構成の展開。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_generated_by_encode"></a>

## 補題 `binaryContextLaw_generated_by_encode`

### 式

$$\text{joint}=\bigl(P_X\otimes P_{G|X}\bigr)\ \text{を}\ (x,g)\mapsto(x,g,\mathrm{encode}\,g)\ \text{で押し出したもの}$$

### Lean のコメント（日本語訳）

> 文脈の法則は、可測な単射の方策 `encode` が、\((X,G)\) の周辺から生成する法則である。非可測な決定論的な等値の事象を a.e. の仮定にせず、生成の測度の等式を、直接確認する。

### 補題の説明

この反例の法則が、「可測で単射な決定論的な行動」から**生成された**ものであることの確認です（反例が `MeasureCMI.lean` の定理の枠内にあることを保証）。

### 証明の概略

1. `binaryGoalMeasure_map_encode` と `binaryContextLaw_joint_eq_encoded`。

----

<a id="Tomabechi.Theorem19_22.DecoderRegularityWitness.binaryContextLaw_cmi_lt_inputEntropy"></a>

## 補題 `binaryContextLaw_cmi_lt_inputEntropy`

### 式

$$\mathrm{CMI}=0<\log2=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 可測な単射の生成方策でも、一般の可測な出力では、CMI の情報の達成は失敗する。標準 Borel の出力を含む、通常の正則な出力に対する反例ではない。

### 補題の説明

**この反例の主結論**：出力の可測構造が目標を区別できなければ、可測・単射な行動でも `I(G;Y|X)=H(G|X)` は成り立ちません。**出力空間の正則性の仮定が必要**です。

### 証明の概略

1. `binaryContextLaw_cmi_eq_zero`、`binaryContextLaw_inputEntropy_eq_log_two`、\(\log2>0\)。

----


## コメント修正記録

- ファイル冒頭のモジュールコメントが、別のファイル（`MeasureCMICapacity.lean`）の説明（「依存型 CMI 容量から定理22の段階容量への橋」）の写しになっていた。このファイルの実際の内容（出力の σ 代数の正則性が必要であることの反例）に合わせて書き直した（コメントのみ、宣言は不変）。
