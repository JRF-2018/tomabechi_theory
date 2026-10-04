# Tomabechi/Information/DeterministicOutput.lean 解説

> 対象: [`Tomabechi/Information/DeterministicOutput.lean`](../Tomabechi/Information/DeterministicOutput.lean)（定理21の有限ゴール・決定論的出力の情報結論）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の**情報容量の結論**（行動が目標を区別するなら、条件付き相互情報量はエントロピーに等しく、正）を、**一般の可測な入力空間**で述べます（目標空間は有限）。
さらに「**偏った枝**（branch）の制約」つきの形と、入力が有限の場合の特殊化も示します。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `residualGoalEntropyAt` / `residualGoalEntropy` | 決定論的な行動を観測した後の残余エントロピー（1 入力での値と、入力で積分したもの） |
| `conditionalGoalMutualInformation` | \(H(G|X)-H(G|X,Y)\)（測度版の条件付き相互情報量） |
| `residualGoalEntropyAt_eq_zero_of_injective_on_support` | 行動が目標を区別すれば残余エントロピーは 0 |
| `theorem21_general_input_information_capacity` | 一般入力版の情報容量 |
| `theorem21_branch_constrained_information_capacity` | 枝の制約つきの版 |
| `theorem21_finite_input_branch_capacity` | 入力が有限（Dirac 混合）の特殊ケース |

### 0.3 このファイルが証明していないこと

- ここでの条件付き相互情報量は、**出力の等値ファイバー**から計算するエントロピーの差です。\(Y\) の可測構造を使う **KL ダイバージェンス型の CMI** とは別の定義で、この宣言自体は両者の同一視を主張しません。確定 H-info（標準 Borel 出力）のもとで同じ生成法則に結びつける定理は、`Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL`（`Tomabechi/Information/MeanFieldDirectCMI.lean`）にあります。
- 行動が目標を区別すること（台の上で単射）と、正のエントロピーは**仮定**です。論文のモデルで確かめる作業はここにはありません。
- 枝の制約つきの定理は、「正の質量の目標が枝に入る」ことを**仮定**し、結論にそのまま添えるだけで、枝への所属を導くものではありません。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理21の、有限の目標・決定論的な出力についての情報の結論。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem21`。

---

<a id="Tomabechi.Theorem21.residualGoalEntropyAt"></a>

## 定義 `residualGoalEntropyAt`

### 式

$$\mathrm{res}(\text{mass},\text{action})=\sum_gh\Bigl(\text{mass}(g),\sum_{g':\,\text{action}(g')=\text{action}(g)}\text{mass}(g')\Bigr)$$

### Lean のコメント（日本語訳）

> 1 つの入力で、決定論的な行動を観測した後の、残余の条件付きエントロピー密度。

### 定義の説明

入力が 1 つに決まっているときの、行動の結果（出力）を見たあとの残りの不確かさです。出力が同じ目標をまとめたファイバーの質量を分母にします。

### 証明の概略

1. 定義：各ゴール \(g\) について、同じ出力を持つゴールの質量の和（ファイバーの質量）を求め、\(g\) の質量とそのファイバーの質量を `finiteConditionalEntropyTerm` に渡して、全ゴールで足し合わせる（出力を知った後に残るゴールの条件付きエントロピーの 1 入力版）。

----

<a id="Tomabechi.Theorem21.residualGoalEntropyAt_eq_zero_of_injective_on_support"></a>

## 補題 `residualGoalEntropyAt_eq_zero_of_injective_on_support`

### 式

$$\text{action が質量が正の目標を区別}\ \Longrightarrow\ \mathrm{res}(\text{mass},\text{action})=0$$

### Lean のコメント（日本語訳）

> 決定論的な行動が、質量が正のすべての目標を区別するなら、それを観測した後に残る条件付きエントロピーは、その入力で 0 である。

### 補題の説明

出力から目標が一意に決まる（質量が正の範囲で）なら、観測後の不確かさは残りません。

### 証明の概略

1. 各項について：質量が 0 なら項は 0。質量が正なら、単射性により、ファイバーの質量の和は自分自身の質量だけ（他は 0 質量または別ファイバー）。
2. \(h(p,p)=-p\log1=0\)（21 行）。

----

<a id="Tomabechi.Theorem21.residualGoalEntropy"></a>

## 定義 `residualGoalEntropy`

### 式

$$H(G\mid X,Y)=\int\mathrm{res}(\text{mass}(x,\cdot),\text{action}(x,\cdot))\,d\mu(x)$$

### Lean のコメント（日本語訳）

> 決定論的な行動の後に残る条件付きエントロピーを、一般の入力分布で積分したもの。

### 定義の説明

1 入力の残余エントロピーを入力で積分したものです。

### 証明の概略

1. 定義：`∫ x, residualGoalEntropyAt (mass x) (action x) ∂μ`。

----

<a id="Tomabechi.Theorem21.conditionalGoalMutualInformation"></a>

## 定義 `conditionalGoalMutualInformation`

### 式

$$I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)$$

### Lean のコメント（日本語訳）

> 有限の目標と決定論的な出力についての条件付き相互情報量。入力の測度に関する \(H(G|X)-H(G|X,Y)\) として定義する。
> 日本語の監査注：ここでの残余エントロピーは、出力の等値ファイバーから計算する。\(Y\) の可測構造を使う KL 型の CMI とは別の定義であり、この宣言自体は同一視を主張しない。確定 H-info（標準 Borel 出力）のもとでの同じ生成法則への接続は、`Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL`（`Tomabechi/Information/MeanFieldDirectCMI.lean`）を参照。

### 定義の説明

入力の分布で平均した、「出力を観測して得られる、目標についての情報量」です。定義は等値ファイバーのエントロピーの差で、KL 型の相互情報量とは別物である点に注意してください（上の監査注）。

### 証明の概略

1. 定義：`conditionalGoalEntropy μ mass - residualGoalEntropy μ mass action`。

----

<a id="Tomabechi.Theorem21.theorem21_general_input_information_capacity"></a>

## 定理 `theorem21_general_input_information_capacity`

### 式

$$\text{ほぼ確実に action が区別},\ H(G\mid X)>0\ \Longrightarrow\ I(G;Y\mid X)=H(G\mid X)\ \wedge\ I(G;Y\mid X)>0$$

### Lean のコメント（日本語訳）

> 一般の可測な入力空間での情報容量の結論。目標空間は有限で、行動の型には制限がない。入力のエントロピーの可積分性と条件付き確率の仮定は、入力のエントロピーを、本当に有限の条件付きエントロピーにする。残余のエントロピーは、ほとんど至るところ 0 であることが証明され、別個の可積分性の前提は要らない。

### 補題の説明

`theorem21_finite_information_capacity` の一般入力版です。残余エントロピーがほぼ確実に 0 なので、その積分も 0、よって \(I=H(G|X)\)、エントロピーが正なら \(I>0\)。

### 証明の概略

1. 入力のエントロピー密度が可測（`conditionalGoalEntropyAt_aestronglyMeasurable`）で可積分（`conditionalGoalEntropy_integrable_of_ae_probability`）。
2. ほぼ確実に残余エントロピー密度が 0（`residualGoalEntropyAt_eq_zero_of_injective_on_support`）。0 関数の積分は 0。
3. \(I=H-0=H>0\)（20 行）。

----

<a id="Tomabechi.Theorem21.theorem21_branch_constrained_information_capacity"></a>

## 定理 `theorem21_branch_constrained_information_capacity`

### 式

$$\text{目標が枝に入る(a.e.)}\ \wedge\ \text{情報容量の仮定}\ \Longrightarrow\ I=H(G\mid X)\ \wedge\ I>0\ \wedge\ (\forall^\mu x,\ \text{質量が正の目標は枝に入る})$$

### Lean のコメント（日本語訳）

> 公刊された定理21の情報の結論を、偏った枝の制約を明示して述べる。質量が正の目標は、順序論的な台のコンテキストが持つ枝の中にあり、決定論的な行動は、入力についてほとんど至るところ、それらの目標を分離する。

### 補題の説明

一般入力の情報容量に、「質量が正の目標は枝 `D.branch` に入る」という条件を**そのまま添えた**形です。枝への所属は仮定で、導かれるわけではありません（枝の構造は `MeanFieldReconstruction.lean` の `Theorem21BranchContext`）。

### 証明の概略

1. `theorem21_general_input_information_capacity` を適用して前半 2 つの結論を得る。
2. 枝への所属は仮定 `hgoals_in_branch` をそのまま 3 つ目の結論に添える（7 行）。

----

<a id="Tomabechi.Theorem21.theorem21_finite_input_branch_capacity"></a>

## 定理 `theorem21_finite_input_branch_capacity`

### 式

$$\mu=\mu_w\ (\text{Dirac 混合})\ \Longrightarrow\ \text{枝の制約つきの情報容量（上と同じ結論）}$$

### Lean のコメント（日本語訳）

> 入力が有限の場合の、枝の容量への特殊化。正規化された重みは、離散的な確率測度と順序論的な台のコンテキストの両方を作る。情報容量の結果は、その同じ測度を使う。

### 補題の説明

入力が有限個の原子（重み \(w_a\)）で、測度が `finiteReconstructionMeasure weight`（Dirac 混合）の場合です。同じ重みから、測度と枝のコンテキスト（`finiteWeightedBranchContext`）の両方を作ります。

### 証明の概略

1. `finite_reconstruction_measure_isProbabilityMeasure` で確率測度。`finiteWeightedBranchContext` で枝のコンテキスト \(D\)。
2. `theorem21_branch_constrained_information_capacity` に渡す（12 行）。

----


## コメント修正記録

- `conditionalGoalMutualInformation` の docstring が参照していた `Theorem21_P13.meanField_stage_theorem21_four_conclusions_directKL` は、現在は存在しない名前だった。正しい参照先 `Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL`（`Tomabechi/Information/MeanFieldDirectCMI.lean`）に修正した（コメントのみ、宣言は不変）。
