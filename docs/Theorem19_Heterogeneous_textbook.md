# Theorem19_Heterogeneous.lean 解説

> 対象: [`Theorem19_Heterogeneous.lean`](../Theorem19_Heterogeneous.lean)（定理19の問題別アルファベット・直接CMI・二重上限）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
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

定理19の「**問題・方策の対ごとに、文脈・ゴール・出力の型がまったく違ってよい**」という設定（**異種の問題族**）での容量の結果をまとめたファイルです。`MeasureCMI.lean`・`MeasureCMICapacity.lean` の結果を、問題ごとの型を持つ構造体 `FiniteGoalCMIProblem`・`DirectGoalCMIProblem` に包んで再利用し、論文19の容量に関する結論（非負性・層の単調性・端点・物理層の零容量・正規化・二重上限と対上限の一致）を 1 つの入口にまとめます。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 有限容量から有限な法則を取り出す | `finiteMeasureCMILawOfFiniteCapacity` |
| 有限な問題の構造体（確率核つき） | `FiniteGoalCMIProblem` と `score`・`goalEntropy`・各補題 |
| 異種の容量の結果 | `heterogeneous_measure_cmi_*`（同定・単調性・零容量・二重上限・原文結論の一括） |
| 直接問題の構造体（出力の核なし） | `DirectGoalCMIProblem` と、`directCMI_*` |
| 異種の単射な方策による情報達成 | `directCMI_heterogeneous_injective_policy_attains_goalEntropy` |
| 反例の包み込み | `indiscreteBitDirectProblem*`（自明σ代数の出力：情報達成が破れる） |

### 0.3 このファイルが証明していないこと

- **層間の評価の保存**（埋め込みがスコアを保つ）と**有限容量**、**正の端点差**は、論文の**独立した条件**として保持します。異なる型の法則を点ごとの等号で比べることはしません。
- **単射な方策による情報達成**（`directCMI_heterogeneous_injective_policy_attains_goalEntropy`）は、出力型ごとの `MeasurableEq` を可測な復号器の構成に使う十分条件として仮定します。任意の可測な出力への一般化ではありません（その反例が `indiscreteBitDirectProblem`）。
- 反例（二値の自明σ代数）は、**任意の可測な \(Y\) への一般化に対する監査用の証人**であり、論文との適合性は別に判定されます。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理19の問題別アルファベットと、問題/方策の二重上限**
>
> 原文の各問題・方策の対には、独自の文脈型・有限離散のゴール型・出力型を許す。個別の法則の KL 型の CMI と、エントロピーの評価を再利用して、容量を構成する。問題族の全体で共通の有限のゴール集合や、一様なゴール数を要求しない。層の間の評価の保存と、有限の容量は、原文の独立の条件として保持する。

（コメント中の「原文」は、苫米地論文を指します。）名前空間は `Tomabechi.Theorem19_Heterogeneous`。`open MeasureTheory ProbabilityTheory Tomabechi.Theorem22`。

---

<a id="Tomabechi.Theorem19_Heterogeneous.finiteMeasureCMILawOfFiniteCapacity"></a>

## 定義 `finiteMeasureCMILawOfFiniteCapacity`

### 式

$$\sup\mathrm{KL}<\infty\ \Longrightarrow\ \text{各許容 law は有限 KL をもつ}$$

### Lean のコメント（日本語訳）

> 実数への変換の前の KL の容量が有限なら、各許容される法則も有限の KL をもつ。問題ごとに \(X/G/Y\) の型が異なってよい。原文の有限の容量から、有限な法則の証明を取り出す入口であり、\(\infty.\mathrm{toReal}=0\) を有限性の代用にせず、拡張非負実数の上限を先に評価する。

### 定義の説明

容量（KL の上限）が有限なら、どの問題の KL も有限です（上限以下）。`FiniteConditionalMutualInformationLaw`（有限 KL の証明書つき）を作ります。

### 証明の概略

1. 各許容 `law` について、KL \(\le\) 上限 \(<\infty\)（`le_sSup`）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.finiteMeasureCMILawOfFiniteCapacity_distribution"></a>

## 補題 `finiteMeasureCMILawOfFiniteCapacity_distribution`

### 式

$$(\text{取り出した law}).\text{distribution}=\text{law}$$

### Lean のコメント（日本語訳）

> 有限の容量から取り出した有限な法則は、元の分布・条件付きの周辺核を保持する。

### 補題の説明

取り出した有限 law の分布は、元の law そのものです（`rfl`）。

### 証明の概略

1. 定義の展開（`rfl`）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem"></a>

## 構造体 `FiniteGoalCMIProblem`

### 式

$$\text{Input},\text{Goal},\text{Output}:\ \text{型},\ \ \text{可測構造},\ \text{Goal は有限離散},\ \ \text{law}:\ \text{FiniteConditionalMutualInformationLaw}$$

### Lean のコメント（日本語訳）

> 1 つの許容される問題・方策の対の、有限ゴールの CMI のデータ。型と可測構造、有限ゴール性、条件付き周辺の法則と有限 KL の証明を、同じパッケージに置く。確率的な出力を許し、Input/Output の有限性・標準 Borel 性は要求しない。条件付き核は `law` に明示的に保持し、核の無条件の存在を主張する構造ではない。

### 定義の説明

**1 つの問題の全データ**を束ねた構造体です。文脈の型 `Input`、有限離散のゴール型 `Goal`、出力の型 `Output`、それぞれの可測構造、そして CMI の法則 `law`。問題ごとに型が違ってよいので、問題族は `FiniteGoalCMIProblem` の族として扱います。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score"></a>

## 定義 `FiniteGoalCMIProblem.score`

### 式

$$\mathrm{score}(p)=\mathrm{KL}(\text{joint}\Vert\text{ref}).\mathrm{toReal}$$

### Lean のコメント（日本語訳）

> 問題自身のアルファベットの上で計算した、有限 KL 型の CMI。

### 定義の説明

その問題の CMI（KL ダイバージェンスの実数値）です。

### 証明の概略

1. 定義：`finiteKLDivergenceScore p.law.toFiniteKLLaw`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.goalEntropy"></a>

## 定義 `FiniteGoalCMIProblem.goalEntropy`

### 式

$$H(G\mid X)\ \text{(その問題の条件付きゴール核から)}$$

### Lean のコメント（日本語訳）

> 問題自身の条件付きのゴール核から計算した \(H(G|X)\)。

### 定義の説明

その問題のゴールの不確かさです。

### 証明の概略

1. 定義：`inputGoalEntropy p.law.distribution`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_nonneg"></a>

## 補題 `FiniteGoalCMIProblem.score_nonneg`

### 式

$$\mathrm{score}(p)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

KL は非負です。

### 証明の概略

1. `ENNReal.toReal_nonneg`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_le_goalEntropy"></a>

## 補題 `FiniteGoalCMIProblem.score_le_goalEntropy`

### 式

$$I(G;Y\mid X)\le H(G\mid X)$$

### Lean のコメント（日本語訳）

> 問題ごとの有限ゴール性だけで CMI \(\le H(G|X)\)。全問題に共通のゴールの型を使わない。

### 補題の説明

`finite_measure_cmi_le_inputGoalEntropy`（MeasureCMI）の問題構造体版です。

### 証明の概略

1. `finite_measure_cmi_le_inputGoalEntropy` を適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_eq_zero_of_goalEntropy_zero"></a>

## 補題 `FiniteGoalCMIProblem.score_eq_zero_of_goalEntropy_zero`

### 式

$$H(G\mid X)=0\ \Longrightarrow\ \mathrm{score}(p)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゴールが決定的なら CMI は 0 です。

### 証明の概略

1. `score_nonneg` と `score_le_goalEntropy` で \(0\le\mathrm{score}\le0\)。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.ConditionallyIndependent"></a>

## 定義 `FiniteGoalCMIProblem.ConditionallyIndependent`

### 式

$$\text{joint}=\text{referenceMeasure}$$

### Lean のコメント（日本語訳）

> 問題固有の同時法則が、条件付き独立の参照の法則に一致するという、独立性。

### 定義の説明

出力が（文脈のもとで）目標と条件付き独立、という述語です。

### 証明の概略

1. 定義：`p.law.distribution.joint = p.law.distribution.referenceMeasure`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.FiniteGoalCMIProblem.score_eq_zero_of_independence"></a>

## 補題 `FiniteGoalCMIProblem.score_eq_zero_of_independence`

### 式

$$\text{条件付き独立}\ \Longrightarrow\ \mathrm{score}(p)=0$$

### Lean のコメント（日本語訳）

> 問題ごとに異なる可測アルファベットでも、条件付き独立なら CMI は零。

### 補題の説明

`klDiv_self`。

### 証明の概略

1. `klDiv_self`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_eq_pooledLayerCapacity"></a>

## 補題 `heterogeneous_measure_cmi_capacity_eq_pooledLayerCapacity`

### 式

$$\mathrm{cap}^{\text{Thm19}}(a)=\mathrm{cap}_{\text{pool}}(a)\quad(\text{異種})$$

### Lean のコメント（日本語訳）

> 問題別のアルファベットをもつ層の容量は、Σ 型で束ねた定理22の容量と一致する。同じ問題の型の要素に同じ CMI を割り当てる、表現の同定である。

### 補題の説明

`MeasureCMICapacity.lean` の同定の、異種の問題族への拡張です。

### 証明の概略

1. 両者の定義（`dependentLayerCapacity` と `layerCapacity`、pooled な許容集合）を展開する。
2. スコアの像の集合が一致することを、要素ごとに示す：層 \(a\) の問題 \(x\) は pooled な対 \((a,x)\) に対応し、逆に pooled な対の第 1 成分が \(a\) なら、その問題は層 \(a\) の許容問題（23 行）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_nondecreasing"></a>

## 補題 `heterogeneous_measure_cmi_capacity_nondecreasing`

### 式

$$\text{評価を保つ単射}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 原文 19 の、評価を保つ単射から、問題別アルファベットの CMI の容量の単調性。評価の保存は、原文に明示される条件であり、異なる型の法則を、点ごとの等号で比較しない。分布の保存の具体化は、共通の型の法則の橋や、可測同型による KL の保存を、別に使う。

### 補題の説明

異種の問題族でも、層間の埋め込みがスコアを保てば容量は単調です。

### 証明の概略

1. `dependentCapacity_nondecreasing_of_scorePreservingEmbedding`（Theorem19）を適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_monotone_along_lub_stages"></a>

## 補題 `heterogeneous_measure_cmi_capacity_monotone_along_lub_stages`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ \mathrm{cap}(u_n)\ \text{単調}$$

### Lean のコメント（日本語訳）

> 同じ層間の対応を、定理22の LUB の更新に沿って反復した、容量の単調性。

### 補題の説明

LUB の段階列に沿った単調性です。

### 証明の概略

1. 上の補題を各ステップに適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero"></a>

## 補題 `heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero`

### 式

$$\forall x\in\text{admissible}(a),\ H(G\mid X)=0\ \Longrightarrow\ \mathrm{cap}(a)=0$$

### Lean のコメント（日本語訳）

> 異なるゴールの型の問題を含む、指定した層でも、全問題の零のエントロピーから、容量は零。零のエントロピーから、スコアの集合の有界性も導くので、ここでは容量の有限性を追加の入力としない。

### 補題の説明

物理層（最下位）の容量が 0 であることの異種版です。

### 証明の概略

1. `zeroCapacity_of_zeroGoalEntropy`（Theorem19：ゴールのエントロピーが 0 なら容量 0）を適用する。
2. 必要な条件を、各問題の性質から与える：スコアの有界性（`score_le_goalEntropy`、エントロピー 0 なので上界 0）、スコアの非負性（`score_nonneg`）、スコア \(\le\) ゴールエントロピー（`score_le_goalEntropy`）、およびエントロピー 0（仮定 `hzero`）（18 行）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_doubleSup_eq_pairSup"></a>

## 補題 `heterogeneous_measure_cmi_doubleSup_eq_pairSup`

### 式

$$\sup_d\sup_\pi\mathrm{score}=\sup_{(d,\pi)}\mathrm{score}\quad(\text{異種})$$

### Lean のコメント（日本語訳）

> 問題/方策ごとに異なる CMI のアルファベットでも、原文 19 の二重の上限と、対の上限は一致する。各問題の方策の集合の非空性を要求せず、CMI の非負性を、パッケージから供給する。

### 補題の説明

`problemPolicy_doubleSup_eq_pairSup`（Theorem19）の異種版です。

### 証明の概略

1. スコアの非負性（`score_nonneg`）を渡して `problemPolicy_doubleSup_eq_pairSup` を適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.heterogeneous_measure_cmi_original_capacity_conclusions"></a>

## 定理 `heterogeneous_measure_cmi_original_capacity_conclusions`

### 式

$$\text{非負性・層の単調性・端点の比較・物理層の零容量・正規化（単調性/端点/一意性）}$$

### Lean のコメント（日本語訳）

> 原文 19 の容量に関する結論を、問題別アルファベットの 1 つの入口でまとめる。非負性・層の単調性・端点の比較・物理層の零容量・正規化の単調性/端点/一意性を返す。同じ許容される問題の族と、層間の評価の保存の写像を、すべての結論に使い、有限の容量と正の端点の差は、原文の条件として保持する。単射な方策の情報の達成は、`Theorem19_22` の個別の法則の定理で別に扱う。

### 補題の説明

**定理19の容量の結論の一括版**（異種の問題族）：容量が非負、層に沿って単調、\(\bot\) が最小・\(\top\) が最大、物理層で零、正規化が厳密増加で端点を 0/1 に写し一意、をまとめて述べます。

### 証明の概略

1. 容量の単調性：`heterogeneous_measure_cmi_capacity_nondecreasing`（同じファイルの前の定理）。
2. ゴールのエントロピーが 0 なら容量 0：`heterogeneous_measure_cmi_capacity_eq_zero_of_goalEntropy_zero`。
3. 端点の正規化 `endpointNormalization`・その厳密な単調性 `endpointNormalization_strictMono`・端点の値 `endpointNormalization_values`・正規化の一意性 `endpointAffine_unique`（Theorem19）をまとめて、原文の容量の結論を 1 つの定理にする（50 行）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem"></a>

## 構造体 `DirectGoalCMIProblem`

### 式

$$\text{Input},\text{Goal},\text{Output},\ \text{joint}\in\mathcal P(\text{Input}\times(\text{Goal}\times\text{Output}))$$

### Lean のコメント（日本語訳）

> 出力の条件付き核を持たない、直接の CMI の問題。\(X/Y\) は任意の可測空間。有限性は各問題に固定せず、許容される族の有限の容量から導く。

### 定義の説明

同時確率測度 `joint` だけを持つ問題の構造体です（条件付き核は持たない）。`MeasureCMI.lean` の「直接」版を使います。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.inputMarginal"></a>

## 定義 `DirectGoalCMIProblem.inputMarginal`

### 式

$$P_X=(\text{joint})_X$$

### Lean のコメント（日本語訳）

> 直接の問題の入力の周辺。明示的な可測空間のフィールドから定義する。

### 定義の説明

入力の周辺分布です。

### 証明の概略

1. 定義：`joint.map Prod.fst`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.information"></a>

## 定義 `DirectGoalCMIProblem.information`

### 式

$$\mathrm{KL}(P_{(XY)G}\Vert\text{ref})\in[0,\infty]$$

### Lean のコメント（日本語訳）

> 直接の問題の CMI。有限性を判定するため、拡張実数のまま保持する。

### 定義の説明

KL ダイバージェンス（拡張実数のまま）です。

### 証明の概略

1. 定義：`klDiv (directActionGoalJoint joint) (directCMIReference joint)`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score"></a>

## 定義 `DirectGoalCMIProblem.score`

### 式

$$\mathrm{score}=\mathrm{information}.\mathrm{toReal}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実数に直したスコアです。

### 証明の概略

1. 定義：`information.toReal`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.goalEntropy"></a>

## 定義 `DirectGoalCMIProblem.goalEntropy`

### 式

$$H(G\mid X)\ \text{(同時法則から構成した事前核で)}$$

### Lean のコメント（日本語訳）

> 直接の問題の、原文の \(H(G|X)\)。同時法則から、有限ゴールの事前核を構成する。

### 定義の説明

同時法則から作った事前核のエントロピーの積分です。

### 証明の概略

1. 定義：`∫ x, finiteKernelGoalEntropyAt (directPriorGoalKernel joint) x ∂inputMarginal`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_le_goalEntropy"></a>

## 補題 `DirectGoalCMIProblem.score_le_goalEntropy`

### 式

$$\mathrm{information}<\infty\ \Longrightarrow\ \mathrm{score}\le H(G\mid X)$$

### Lean のコメント（日本語訳）

> 有限の直接の CMI は、同時法則から構成した、条件付きのゴールのエントロピー以下である。

### 補題の説明

`directCMI_le_inputGoalEntropy_of_finite`（MeasureCMI）の問題構造体版です。

### 証明の概略

1. `directCMI_le_inputGoalEntropy_of_finite`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_information_ne_top_of_finite_capacity"></a>

## 補題 `directCMI_information_ne_top_of_finite_capacity`

### 式

$$\sup\mathrm{information}<\infty\ \Longrightarrow\ \forall q,\ \mathrm{information}(q)<\infty$$

### Lean のコメント（日本語訳）

> 許容される族の拡張容量が有限なら、各許容される問題の KL も有限である。

### 補題の説明

上限が有限なら、個々も有限です。

### 証明の概略

1. `le_sSup` と、上限が \(\ne\infty\)。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.ConditionallyIndependent"></a>

## 定義 `DirectGoalCMIProblem.ConditionallyIndependent`

### 式

$$\text{joint}=\text{directCMIReference}$$

### Lean のコメント（日本語訳）

> 直接の問題の条件付き独立：同時法則と、直接の独立な参照の法則が一致する。

### 定義の説明

直接版の条件付き独立です。

### 証明の概略

1. 定義：等式。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.information_eq_zero_of_independence"></a>

## 補題 `DirectGoalCMIProblem.information_eq_zero_of_independence`

### 式

$$\text{条件付き独立}\ \Longrightarrow\ \mathrm{information}=0$$

### Lean のコメント（日本語訳）

> 条件付き独立なら、拡張 CMI そのものが零。有限性の入力は不要。

### 補題の説明

`klDiv_self`。

### 証明の概略

1. `klDiv_self`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_eq_zero_of_independence"></a>

## 補題 `DirectGoalCMIProblem.score_eq_zero_of_independence`

### 式

$$\text{条件付き独立}\ \Longrightarrow\ \mathrm{score}=0$$

### Lean のコメント（日本語訳）

> 直接の問題の独立のときの、実数の評価は零。

### 補題の説明

上の補題の実数版です。

### 証明の概略

1. `information_eq_zero_of_independence` と `toReal`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_scores_bddAbove"></a>

## 補題 `directCMI_scores_bddAbove`

### 式

$$\sup\mathrm{information}<\infty\ \Longrightarrow\ \text{スコアは上に有界}$$

### Lean のコメント（日本語訳）

> 許容される問題の族の、拡張 CMI の上限が有限であることから、実数の容量に必要な有界性を導く。

### 補題の説明

拡張実数の上限が有限なら、実数のスコアも上に有界です。

### 証明の概略

1. `ENNReal.toReal` の単調性。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_nondecreasing"></a>

## 補題 `directCMI_capacity_nondecreasing`

### 式

$$\text{評価を保つ単射}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)\quad(\text{直接})$$

### Lean のコメント（日本語訳）

> 直接の同時法則からの、問題別の容量の単調性。有限の容量を、拡張 CMI で受け取り、実数の上限の有界性を、内部で導く。評価を保つ単射は、原文の独立の条件。

### 補題の説明

直接版の容量の単調性です。

### 証明の概略

1. `directCMI_scores_bddAbove` で有界性、`dependentCapacity_nondecreasing_of_scorePreservingEmbedding` を適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_eq_zero_of_goalEntropy_zero"></a>

## 補題 `directCMI_capacity_eq_zero_of_goalEntropy_zero`

### 式

$$H(G\mid X)=0\ (\text{許容族})\ \Longrightarrow\ \sup\mathrm{score}=0$$

### Lean のコメント（日本語訳）

> 直接の問題の型の零容量。\(H(G|X)=0\) は、指定した許容される族だけに要求する。

### 補題の説明

直接版の零容量です。

### 証明の概略

1. 各スコア \(\le H(G|X)=0\) と非負性。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_original_capacity_conclusions"></a>

## 定理 `directCMI_original_capacity_conclusions`

### 式

$$\text{直接問題族での原文19の容量結論の一括}$$

### Lean のコメント（日本語訳）

> 任意の可測な出力の、直接の問題族から、原文 19 の容量の結論をまとめる。有限の拡張容量・評価を保つ単射・物理層の零のエントロピー・正の端点の差を、明示的な入力に保つ。

### 補題の説明

`heterogeneous_measure_cmi_original_capacity_conclusions` の直接版です。

### 証明の概略

1. 同様にまとめる。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_doubleSup_eq_pairSup"></a>

## 補題 `directCMI_doubleSup_eq_pairSup`

### 式

$$\sup_d\sup_\pi=\sup_{(d,\pi)}\quad(\text{直接 CMI})$$

### Lean のコメント（日本語訳）

> 直接の CMI の、問題/方策の二重の上限は、許容される対の上限と一致する。各問題の方策の非空性は追加せず、許容される対の全体の非空性と、有限の拡張容量を用いる。

### 補題の説明

直接版の二重上限と対上限の一致です。

### 証明の概略

1. `problemPolicy_doubleSup_eq_pairSup`（Theorem19）を適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_capacity_monotone_along_lub_stages"></a>

## 補題 `directCMI_capacity_monotone_along_lub_stages`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ \mathrm{cap}(u_n)\ \text{単調}\quad(\text{直接})$$

### Lean のコメント（日本語訳）

> 直接の CMI の容量を、定理22の LUB の更新へ接続する。問題別の可測な型と、拡張容量の有限性を保持する。

### 補題の説明

LUB の段階列に沿った直接版の単調性です。

### 証明の概略

1. `directCMI_capacity_nondecreasing` を各ステップに適用。

----

<a id="Tomabechi.Theorem19_Heterogeneous.DirectGoalCMIProblem.score_eq_goalEntropy_of_recovery"></a>

## 補題 `DirectGoalCMIProblem.score_eq_goalEntropy_of_recovery`

### 式

$$\text{可測な復元}\ \Longrightarrow\ \mathrm{score}=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 直接の問題の型の、可測な復元による、情報の達成。任意の可測な出力を保ち、復号器の可測性と、同時法則の a.e. の復元を、実際の入力にする。

### 補題の説明

`directCMI_eq_inputGoalEntropy_of_recovery`（MeasureCMI）の問題構造体版です。

### 証明の概略

1. `directCMI_eq_inputGoalEntropy_of_recovery`。

----

<a id="Tomabechi.Theorem19_Heterogeneous.directCMI_heterogeneous_injective_policy_attains_goalEntropy"></a>

## 定理 `directCMI_heterogeneous_injective_policy_attains_goalEntropy`

### 式

$$\begin{aligned}
&\sup_{q\in\mathrm{adm}}I_q<\infty,\quad \text{各 }q:\ \text{joint は方策 }a_q\text{ から生成（決定論的・可測）},\ \ x\mapsto a_q(x,\cdot)\ \text{は入力 a.e. で単射},\ \ \text{出力空間は標準 Borel}\\
&\Longrightarrow\ \ \forall q\in\mathrm{adm},\ \ I_q=\mathrm{score}(q)=H(G\mid X)(q)
\end{aligned}$$
（**出力が標準 Borel であること**が必須の仮定。これを外すと情報達成が破れる＝`Theorem19_Counterexample`。）

### Lean のコメント（日本語訳）

> 異種の直接の問題族で、有限の容量から、各許容される法則の有限の KL を取り出し、各問題の、可測な決定論的な単射の方策による、情報の達成を、同じ `score` / `goalEntropy` に接続する。出力の型ごとの `MeasurableEq` は、可測な復号器の構成に使う十分条件であり、任意の可測な出力への一般化ではない。

### 補題の説明

**異種の問題族での、定理19の情報達成**：有限容量で各問題の KL が有限、方策が可測・a.e. 単射なら、各問題で CMI \(=H(G|X)\)。

### 証明の概略

1. 各許容 \(q\) について、問題 \(p=\)`problem q` の可測構造・有限ゴール・標準 Borel 性（`hstandardBorel`、そこから `MeasurableEq` を局所的に導く）を整える。
2. 有限容量の仮定から、この問題の KL 型 CMI が有限（`directCMI_information_ne_top_of_finite_capacity`）。
3. `directCMI_eq_inputGoalEntropy_of_injective_deterministic_joint`（Theorem19_22）を、方策の可測性・結合法則の生成・入力 a.e. 単射性と合わせて適用し、`score = goalEntropy` を得る（52 行）。

----

<a id="Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem"></a>

## 定義 `indiscreteBitDirectProblem`

### 式

$$\text{DecoderRegularity の 2 値の証人}\ \to\ \text{DirectGoalCMIProblem}$$

### Lean のコメント（日本語訳）

> P16 の 2 値の証人を、定理19で使う直接の KL 問題の型に包む。出力の自明な σ 代数を保持し、標準 Borel の条件は加えない。

### 定義の説明

`DecoderRegularity.lean` の反例を、`DirectGoalCMIProblem` として表したものです。

### 証明の概略

1. 定義：直接ゴール CMI 問題 `DirectGoalCMIProblem` を、入力 `Unit`、ゴール `Bool`、出力 `IndiscreteBit`（自明 σ 代数）、結合法則 `binaryContextLaw.joint`（既存の二値 CMI 法則）で与える。

----

<a id="Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_information_eq_zero"></a>

## 補題 `indiscreteBitDirectProblem_information_eq_zero`

### 式

$$\mathrm{information}=0$$

### Lean のコメント（日本語訳）

> 2 値の証人の直接の CMI は、既存の CMI の法則の KL そのものであり、有限かつ零である。

### 補題の説明

反例の CMI は 0 です。

### 証明の概略

1. `DecoderRegularity` の `binaryContextLaw_cmi_eq_zero` と同定。

----

<a id="Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_goalEntropy_eq_log_two"></a>

## 補題 `indiscreteBitDirectProblem_goalEntropy_eq_log_two`

### 式

$$H(G\mid X)=\log2$$

### Lean のコメント（日本語訳）

> 直接の問題の型が計算する、条件付きのゴールのエントロピーは、同じ 2 値の法則の \(H(G|X)=\log2\) と一致する。

### 補題の説明

反例のゴールのエントロピーは \(\log2\) です。

### 証明の概略

1. `binaryContextLaw_inputEntropy_eq_log_two` と同定。

----

<a id="Tomabechi.Theorem19_Heterogeneous.indiscreteBitDirectProblem_score_lt_goalEntropy"></a>

## 補題 `indiscreteBitDirectProblem_score_lt_goalEntropy`

### 式

$$\mathrm{score}=0<\log2=H(G\mid X)$$

### Lean のコメント（日本語訳）

> 直接の KL 型の、同一の `DirectGoalCMIProblem` の上で、情報の達成の等式が破れる。任意の可測な \(Y\) への一般化に対する C2 の証人であり、原文への適合性は、別に C1/C3 で判定する。

### 補題の説明

**直接問題の型の上での反例**：スコア \(<\) ゴールのエントロピー。出力空間の正則性の仮定が必要であることを、同じ構造体で示します。

### 証明の概略

1. 上の 2 つの補題と \(\log2>0\)。

----


## コメント修正記録

（なし）
