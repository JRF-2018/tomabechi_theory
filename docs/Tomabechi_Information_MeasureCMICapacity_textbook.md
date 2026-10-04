# Tomabechi/Information/MeasureCMICapacity.lean 解説

> 対象: [`Tomabechi/Information/MeasureCMICapacity.lean`](../Tomabechi/Information/MeasureCMICapacity.lean)（定理19の依存型容量と一般測度CMI・定理22の段階容量の橋）。
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

定理19の**依存型の容量**（`Theorem19.lean`）と、定理22の**共通の型での層の容量**（`Capacity.lean`, `Theorem22.lean`）を結ぶ**橋**です。問題の型が層ごとに違う（\(A_a\)）ものを、**Σ 型**（\(\Sigma a, A_a\)）に束ねて 1 つの「プール」にすると、定理19の容量が定理22の容量に一致します。さらに、`MeasureCMI.lean` の**一般測度の CMI** をスコアにした容量について、単調性・非負性・零容量の条件・端点の正規化・LUB の段階列に沿った単調性を示します。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| Σ 型のプール | `ProblemPool`, `pooledAdmissible`, `pooledFiniteGoalScore` |
| 有限版の橋 | `dependentCapacity_eq_pooledLayerCapacity`, `dependent_finite_goal_capacity_nondecreasing`, `..._monotone_along_lub_stages` |
| 一般測度版 | `pooledMeasureCMIScore`, `dependentMeasureCMICapacity_eq_pooledLayerCapacity`, `dependent_measure_cmi_capacity_nondecreasing` ほか |
| 零容量・正規化 | `..._eq_zero_of_independence`, `..._of_zero_entropy_bound`, `..._endpoint_normalization_values`, `..._eq_zero_of_inputGoalEntropy_zero` |
| 問題ごとに空間が違う直接版 | `heterogeneous_directCMI_capacity_eq_zero` |

### 0.3 このファイルが証明していないこと

- Σ 型への束ね直しは**表現の同定**であり、確率モデルの存在を仮定から導くものではありません。
- 容量の単調性は、層間の埋め込みが**同時法則（あるいは KL の対）を保存する**という仮定から導きます。条件付き核が一意である（可算生成などの）正則性も、同時法則だけの保存から参照法則の保存を導く版で仮定します。
- スコアと上限の有限性（空でない・上に有界）は仮定です。「スコア \(\le\) エントロピー」の不等式は、一部の補題では**入力**として与えます（`..._of_zero_entropy_bound`）。
- 零容量の結論は、物理層（最下位）のゴールのエントロピーが 0 であることを**仮定**します。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 一般測度の CMI の法則を、依存型の容量へ接続する API。

名前空間は `Tomabechi.Theorem19_22`。`open Tomabechi.Theorem22`、`open MeasureTheory ProbabilityTheory`。

---

<a id="Tomabechi.Theorem19_22.ProblemPool"></a>

## 定義 `ProblemPool`

### 式

$$\Sigma a,\ A_a$$

### Lean のコメント（日本語訳）

> 層ごとに異なる問題の型・方策の対を束ねる、共通の Σ 型。

### 定義の説明

層 \(a\) と、その層の問題・方策 \(x\in A_a\) の組全体です。

### 証明の概略

1. 定義：Σ 型の別名。

----

<a id="Tomabechi.Theorem19_22.pooledAdmissible"></a>

## 定義 `pooledAdmissible`

### 式

$$\{\langle b,x\rangle\mid x\in\text{admissible}(b),\ b=a\}$$

### Lean のコメント（日本語訳）

> 指定した層で許容される要素を、Σ 型の共通のプールの上に埋め込んだ集合。

### 定義の説明

層 \(a\) の許容問題を、プール（Σ 型）の部分集合として見たものです。

### 証明の概略

1. 定義：`{p | ∃ x ∈ admissible a, p = ⟨a, x⟩}`（Σ 型への埋め込み）。

----

<a id="Tomabechi.Theorem19_22.pooledFiniteGoalScore"></a>

## 定義 `pooledFiniteGoalScore`

### 式

$$\mathrm{score}(\langle b,x\rangle)=I(G;Y\mid X)\ (\text{有限ゴール})$$

### Lean のコメント（日本語訳）

> 問題が属する層に応じて、有限ゴールの CMI を採点する、Σ 型の上のスコア。

### 定義の説明

プールの各元（層 \(b\) の問題 \(x\)）に、その問題の有限ゴール CMI（`FiniteCMI` のもの）を対応させます。

### 証明の概略

1. 定義：`finiteConditionalMutualInformation (mass b x) (policy b x)`。

----

<a id="Tomabechi.Theorem19_22.dependentCapacity_eq_pooledLayerCapacity"></a>

## 補題 `dependentCapacity_eq_pooledLayerCapacity`

### 式

$$\mathrm{cap}^{\text{Thm19}}(a)=\mathrm{cap}^{\text{Thm22}}_{\text{pool}}(a)$$

### Lean のコメント（日本語訳）

> 定理19の依存型の容量は、Σ 型で束ねた、定理22の容量と一致する。これは、問題の型の束ね方による、表現の同定であり、確率モデルの存在を、仮定から導く主張ではない。

### 補題の説明

同じ上限を、依存型で書くか、Σ 型のプールで書くかの違いだけです。

### 証明の概略

1. スコア集合が一致する（Σ 型の埋め込みで集合が等しい）ので、`sSup` が等しい。

----

<a id="Tomabechi.Theorem19_22.dependent_finite_goal_capacity_nondecreasing"></a>

## 補題 `dependent_finite_goal_capacity_nondecreasing`

### 式

$$a\le b\ \Longrightarrow\ \mathrm{cap}_{\text{pool}}(a)\le\mathrm{cap}_{\text{pool}}(b)$$

### Lean のコメント（日本語訳）

> 定理19の層別の埋め込みが、許容性と、誘導される同時法則を保つとき、Σ 型のプールの上の、定理22の有限ゴールの容量は単調である。単射性も、原文の条件として保持する。

### 補題の説明

定理19の埋め込み（同時法則を保つ）から、定理22の容量の単調性が従います。

### 証明の概略

1. `dependentCapacity_eq_pooledLayerCapacity` で、問題の型が異なる層の容量を、全層をまとめた pooled な容量に書き換える。
2. `dependentCapacity_nondecreasing_of_scorePreservingEmbedding`（Theorem19）を適用する。必要なのは、埋め込みがスコアを保つこと。
3. スコアの保存：有限 CMI は結合法則だけの関数（`finiteConditionalMutualInformation_factors_through_jointLaw`）で、結合法則が埋め込みで保存される（仮定 `hlaw`）ので、両者のスコアが等しい（48 行）。

----

<a id="Tomabechi.Theorem19_22.dependent_finite_goal_capacity_monotone_along_lub_stages"></a>

## 補題 `dependent_finite_goal_capacity_monotone_along_lub_stages`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ n\mapsto\mathrm{cap}_{\text{pool}}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> 定理22の LUB の更新式 \(u(n+1)=u(n)\vee v(n+1)\) のもとで、前の定理の、定理19由来の容量の橋を、各隣り合う段階へ適用し、Σ 型で束ねた依存型の問題の族の、有限 CMI の容量が単調になることを示す。

### 補題の説明

LUB の段階列に沿った、依存型の容量の単調性です。

### 証明の概略

1. 各 \(n\) で上の補題を \(u_n\le u_n\vee v_{n+1}\) に適用し、`monotone_nat_of_le_succ`。

----

<a id="Tomabechi.Theorem19_22.pooledMeasureCMIScore"></a>

## 定義 `pooledMeasureCMIScore`

### 式

$$\mathrm{score}(\langle b,x\rangle)=\mathrm{KL}(\text{joint}\Vert\text{ref}).\mathrm{toReal}$$

### Lean のコメント（日本語訳）

> 依存型の問題のプールの上の、一般の可測空間の CMI のスコア。有限な法則は、その同時法則・条件付き核・参照法則・有限 KL の証明書を、明示的に保持する。ゴールの文字集合は有限であり、入力と出力の文字集合は無限でもよく、出力は確率的でもよい。

### 定義の説明

`MeasureCMI.lean` の測度論的な CMI（KL ダイバージェンス）を、プールの各元に対応させるスコアです。

### 証明の概略

1. 定義：`finiteKLDivergenceScore (law b x).toFiniteKLLaw`。

----

<a id="Tomabechi.Theorem19_22.dependentMeasureCMICapacity_eq_pooledLayerCapacity"></a>

## 補題 `dependentMeasureCMICapacity_eq_pooledLayerCapacity`

### 式

$$\mathrm{cap}^{\text{Thm19}}(a)=\mathrm{cap}_{\text{pool}}(a)\quad(\text{一般測度 CMI})$$

### Lean のコメント（日本語訳）

> 依存型の容量と、その Σ 型の、一般の可測空間の CMI の容量は、同じスコアの上限であり、文脈・行為の空間への有限性の制限はない。

### 補題の説明

一般測度版の表現の同定です。

### 証明の概略

1. 上の同定と同様。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_nondecreasing"></a>

## 補題 `dependent_measure_cmi_capacity_nondecreasing`

### 式

$$\text{同時法則を保つ埋め込み}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 条件付き核が、生成された関連する空間の上で一意であるとき、層をまたぐ同時法則を保つ埋め込みは、一般の CMI のスコアを保つ。これは、有限の \(X/Y\) や決定論的な方策なしに、定理19の依存型の容量の単調性を与える。有限のゴールの文字集合は、その可測空間で表される。

### 補題の説明

**定理19の容量の単調性の一般測度版**：同時法則さえ保てば、容量は減りません。

### 証明の概略

1. `dependentCapacity_nondecreasing_of_scorePreservingEmbedding`（Theorem19）を、スコア \(=\)`finiteKLDivergenceScore`（法則の KL）として適用する。
2. スコアの保存：結合法則の保存（`hjointPreserving`）から、`ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq`（Theorem22）で参照測度も等しい。結合法則と参照測度がともに等しいので、KL のスコアが等しい（48 行）。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_nondecreasing_of_pair_preserving"></a>

## 補題 `dependent_measure_cmi_capacity_nondecreasing_of_pair_preserving`

### 式

$$\text{KL の対（joint, ref）を保つ埋め込み}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 完全に一般の可測空間では、KL の完全な対（同時法則と、条件付き独立の参照法則）を保つことが、容量の単調性に十分である。この変種は、可算生成の仮定を除く。上の、同時法則だけの定理は、その正則性の仮定のもとで、参照の保存を導く。

### 補題の説明

可算生成性などの正則性を仮定せず、**KL の対そのものが保たれる**ことを仮定する版です。

### 証明の概略

1. `toFiniteKLLaw` の等式からスコアが保たれる。`dependentCapacity_nondecreasing_of_scorePreservingEmbedding` を適用。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_nonnegative"></a>

## 補題 `dependent_measure_cmi_capacity_nonnegative`

### 式

$$\mathrm{cap}(a)\ge0$$

### Lean のコメント（日本語訳）

> プールされた一般測度の CMI の容量は、そのスコアが実際の有限 KL の値なので、非負である。空でないことと有界性は、定理19の明示的な容量の仮定である。

### 補題の説明

KL は非負です。

### 証明の概略

1. 許容集合が非空（`hnonempty`）なので元 \(x\) を取る。
2. KL のスコアは非負（`ENNReal.toReal_nonneg`）で、スコアの集合は上に有界なので、上限 \(\ge\) その元のスコア \(\ge0\)（`le_csSup`）（23 行）。

----

<a id="Tomabechi.Theorem19_22.finite_measure_cmi_score_eq_zero_of_joint_eq_reference"></a>

## 補題 `finite_measure_cmi_score_eq_zero_of_joint_eq_reference`

### 式

$$\text{joint}=\text{ref}\ \Longrightarrow\ \mathrm{score}=0$$

### Lean のコメント（日本語訳）

> 条件付き独立は、同時法則を、その指定された参照の法則に等しくし、したがって、測度の CMI のスコアは零になる。この定理は、測度の水準の正確な条件を記録する。非形式的な独立性の述語からそれを導くことは、別の法則の構成の課題として残る。

### 補題の説明

同時法則が参照測度（独立な同時分布）に等しければ、CMI は 0（`klDiv_self`）。

### 証明の概略

1. `klDiv_self`。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_eq_zero_of_independence"></a>

## 補題 `dependent_measure_cmi_capacity_eq_zero_of_independence`

### 式

$$\forall x,\ \text{joint}=\text{ref}\ \Longrightarrow\ \mathrm{cap}(a)=0$$

### Lean のコメント（日本語訳）

> すべての許容される問題で、同時法則が、その条件付き独立の参照の法則に等しければ、依存型の測度 CMI の容量は零である。空でないことと有界性は、元の容量の API の仮定として保持する。

### 補題の説明

全問題で情報が伝わらない（条件付き独立）なら、容量は 0 です。

### 証明の概略

1. 各スコアが 0（上の補題）、上限も 0（`csSup`）。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_eq_zero_of_zero_entropy_bound"></a>

## 補題 `dependent_measure_cmi_capacity_eq_zero_of_zero_entropy_bound`

### 式

$$\text{score}\le H=0\ \Longrightarrow\ \mathrm{cap}(a)=0$$

### Lean のコメント（日本語訳）

> 測度 CMI のスコアが、与えられたエントロピーの汎関数で上から抑えられるなら、依存型の容量は、零の条件付きのエントロピーの結論をもつ。スコアからエントロピーへの不等式は、ここでは明示的な入力であり、このアダプタは、一般の測度論的な不等式が導かれたとは主張しない。

### 補題の説明

`zeroCapacity_of_zeroGoalEntropy`（Theorem19）の一般測度版のアダプタです。

### 証明の概略

1. 上限が 0 以下：各スコアは、仮定 `hscoreLeEntropy` で `goalEntropy` 以下、`hentropyZero` でそれが 0（`csSup_le`）。
2. 上限が 0 以上：許容集合の元 \(x_0\) のスコアは非負なので、上限もそれ以上（36 行）。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_endpoint_normalization_values"></a>

## 補題 `dependent_measure_cmi_endpoint_normalization_values`

### 式

$$\mathrm{cap}(\bot)=0,\ \mathrm{cap}(\top)>0\ \Longrightarrow\ \nu(\mathrm{cap}(\bot))=0,\ \nu(\mathrm{cap}(\top))=1$$

### Lean のコメント（日本語訳）

> 零のエントロピーの端点の容量が零で、最上位の端点の容量が正なら、既存のアフィンの正規化は、それらの端点を 0 と 1 に固定する。

### 補題の説明

端点の正規化の確認です（`endpointNormalization_values`）。

### 証明の概略

1. `endpointNormalization_values`（Theorem19）。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_monotone_along_lub_stages"></a>

## 補題 `dependent_measure_cmi_capacity_monotone_along_lub_stages`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ n\mapsto\mathrm{cap}(u_n)\ \text{は単調}\quad(\text{一般測度 CMI})$$

### Lean のコメント（日本語訳）

> 一般の可測空間の CMI の容量を、LUB の漸化式 \(u(n+1)=u(n)\vee v(n+1)\) に沿って反復する。各 `law` が与える、同時法則を保つ埋め込みと、有限 KL の証明書を条件とする。

### 補題の説明

LUB の段階列に沿った、一般測度の容量の単調性です。

### 証明の概略

1. `dependent_measure_cmi_capacity_nondecreasing` を各ステップに適用。

----

<a id="Tomabechi.Theorem19_22.dependent_measure_cmi_capacity_eq_zero_of_inputGoalEntropy_zero"></a>

## 補題 `dependent_measure_cmi_capacity_eq_zero_of_inputGoalEntropy_zero`

### 式

$$\forall x\in\text{admissible}(a),\ H(G\mid X)=0\ \Longrightarrow\ \mathrm{cap}(a)=0$$

### Lean のコメント（日本語訳）

> 指定した層 \(a\) のすべての許容される問題で \(H(G|X)=0\) なら、その層の容量は零である。他の層の零のエントロピーや、CMI の上界を入力せず、空でないことと法則だけから証明する。原文 19 の物理層への適用では \(a=\bot\) とする。

### 補題の説明

**物理層（最下位）の容量が 0 になる**ことの測度版：ゴールが決定的（\(H=0\)）なら CMI も 0。

### 証明の概略

1. `finite_measure_cmi_score_eq_zero_of_inputGoalEntropy_zero`（MeasureCMI）で各スコアが 0。上限も 0。

----

<a id="Tomabechi.Theorem19_22.heterogeneous_directCMI_capacity_eq_zero"></a>

## 補題 `heterogeneous_directCMI_capacity_eq_zero`

### 式

$$\text{問題ごとに}\ X_q,G_q,Y_q\ \text{が異なる}:\ H(G\mid X)=0\ (\forall q)\ \Longrightarrow\ \sup=0$$

### Lean のコメント（日本語訳）

> 問題ごとに \(X/G/Y\) が異なる、直接の CMI の容量の、零のエントロピーの結論。原文の、実数化の前の KL の上限が有限であることから、各許容される問題の有限性を取り出す。許容されない問題の有限性、各問題の \(Y|X\) の核、出力の標準 Borel 性は、要求しない。

### 補題の説明

問題ごとに空間が違っても（異種の問題族）、全問題で \(H(G|X)=0\) なら、直接の CMI の容量は 0 です。

### 証明の概略

1. 各許容問題で KL が有限（上限が有限から）。`directCMI_le_inputGoalEntropy_of_finite`（MeasureCMI）でスコア \(\le H(G|X)=0\)、非負性。

----


## コメント修正記録

（なし）
