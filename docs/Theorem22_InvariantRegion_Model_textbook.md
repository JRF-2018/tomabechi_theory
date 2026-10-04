# Theorem22_InvariantRegion_Model.lean 解説

> 対象: [`Theorem22_InvariantRegion_Model.lean`](../Theorem22_InvariantRegion_Model.lean)（H-stage不変領域の範囲拡張を示す1次元モデル）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`InvariantRegion.lean` で「初期値の**全劣水準集合**ではなく、それより**小さい前向き不変な区間**を不変領域にしてよい」と緩めた意味を、**1 次元の玩具モデル**で確かめるファイルです。このモデルでは、初期値で定まる全劣水準集合は局所球の内部障壁を**満たさない**（境界に届く）のに、より小さい前向き不変区間は障壁を**満たす**、という入力範囲の差を解析的に確認します。

### 0.2 モデル

- 背景ポテンシャル \(V(x)=x/2\)、平均場 \(S(x)=-x^2/2\)、実効ポテンシャル \(V-S=\tfrac x2+\tfrac{x^2}{2}=\tfrac12(x+\tfrac12)^2-\tfrac18\)（谷は \(x^\*=-\tfrac12\)）。
- 局所球は中心 0・半径 1（\([-1,1]\)）、初期状態 \(x_0=\tfrac12\)。
- 閉ループ（恒等移動度）：\(\dot x=-(x+\tfrac12)\)。
- 初期点の全劣水準集合 \(\{V_{\text{eff}}\le V_{\text{eff}}(\tfrac12)=\tfrac38\}\) は、\(V_{\text{eff}}(-1)=0\le\tfrac38\) なので境界点 \(-1\) に届き、閉包が開球に入らない。
- 一方、前向き不変な区間 \([-\tfrac12,\tfrac12]\) は、閉包が開球に入り、谷 \(-\tfrac12\) と初期点 \(\tfrac12\) を含む。

### 0.3 このファイルが証明していないこと（重要）

- **このモデルは一般定理の代替ではありません**。「入力範囲の差」を解析的に確認するための**1 次元の玩具モデル**で、特殊ケースです。
- モデルが一般定理の仮定をすべて満たす（`InvariantRegionMeanFieldStageInput` を完全に構成する）ことは、23 の宣言で確認しています。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **H-stage の不変領域の範囲の拡張を示す、1 次元のモデル**
>
> このモデルは、一般の定理の代替ではない。初期値で定まる全部分準位の集合が、局所球の内部の障壁を満たさない一方、より小さい前向き不変な区間は障壁を満たす、という入力範囲の差を、解析的に確認する。

名前空間は `Tomabechi.Theorem22InvariantRegionModel`。`open RealInnerProductSpace`、`open MeasureTheory`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem22InvariantRegionModel.toyBackground"></a>

## 定義 `toyBackground`

### 式

$$V(x)=x/2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

背景のポテンシャル（線形）です。

### 証明の概略

1. 定義：`x / 2`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyMeanField"></a>

## 定義 `toyMeanField`

### 式

$$S(x)=-x^2/2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

平均場（臨場感）のポテンシャルです。

### 証明の概略

1. 定義：`-(x ^ 2) / 2`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyPotential"></a>

## 定義 `toyPotential`

### 式

$$V_{\text{eff}}(x)=V(x)-S(x)=\tfrac x2+\tfrac{x^2}{2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実効ポテンシャルです（ゲイン・臨場感ともに 1）。

### 証明の概略

1. 定義：`toyBackground x - toyMeanField x`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyInvariantRegion"></a>

## 定義 `toyInvariantRegion`

### 式

$$C=[-\tfrac12,\tfrac12]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

不変領域に選ぶ区間です。

### 証明の概略

1. 定義：`Set.Icc (-(1/2)) (1/2)`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyClosedLoopField"></a>

## 定義 `toyClosedLoopField`

### 式

$$f(x)=-(x+\tfrac12)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

閉ループの場 \(-\nabla V_{\text{eff}}\)（\(\nabla V_{\text{eff}}=\tfrac12+x\)）です。

### 証明の概略

1. 定義：`-(x + 1/2)`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_initial_mem"></a>

## 補題 `toy_initial_mem`

### 式

$$\tfrac12\in C$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期状態 \(\tfrac12\) は不変領域に属します。

### 証明の概略

1. `Set.mem_Icc` と数値計算（`norm_num`）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_valley_mem"></a>

## 補題 `toy_valley_mem`

### 式

$$-\tfrac12\in C$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

谷の底 \(-\tfrac12\) も不変領域に属します。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_threshold_strict"></a>

## 補題 `toy_threshold_strict`

### 式

$$\text{(閾値の厳密な不等式)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

このモデルが、ゲインの閾値 \(p>p_{\text{crit}}\) を厳密に満たすことの確認です。

### 証明の概略

1. 数値計算（`norm_num`）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_potential_square_completion"></a>

## 補題 `toy_potential_square_completion`

### 式

$$V_{\text{eff}}(x)=\tfrac12\bigl(x+\tfrac12\bigr)^2-\tfrac18$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平方完成です。谷の底が \(-\tfrac12\)、最小値が \(-\tfrac18\) だとわかります。

### 証明の概略

1. `ring`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_valley_unique_on_unit_ball"></a>

## 補題 `toy_valley_unique_on_unit_ball`

### 式

$$x^\*=-\tfrac12\ \text{は}\ [-1,1]\ \text{上の唯一の最小点}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平方完成から、谷の底が単位球の上の唯一の最小点です。

### 証明の概略

1. `toy_potential_square_completion` と \((y+\tfrac12)^2\ge0\)（`nlinarith`）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyAveragePresentation"></a>

## 定義 `toyAveragePresentation`

### 式

$$S(x)=\int K(x,a)\,d\mu(a)\quad(\text{原子 1 点})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

平均場 \(S\) を、**原子 1 点の確率測度での積分**として表す `MeanFieldAveragePresentation`（StageData）の構成です。

### 証明の概略

1. 各フィールド（原子の型・順序・測度・台・LUB・カーネル）を具体的に与える。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_mean_field_has_average_presentation"></a>

## 補題 `toy_mean_field_has_average_presentation`

### 式

$$S(x)=\text{integralValue}(x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平均場が、積分表示の値に等しいことの確認です。

### 証明の概略

1. 原子 1 点での積分は被積分関数の値（`integral_dirac`）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_closed_loop_interval_invariant"></a>

## 補題 `toy_closed_loop_interval_invariant`

### 式

$$x(a)\in C,\ x'=f(x)\ \Longrightarrow\ x(t)\in C\ (t\in[a,a+d])$$

### Lean のコメント（日本語訳）

> このスカラーの閉ループの方程式の、微分可能な解は、区間から出発すれば、任意の有限の前向きの時間区間で、その中に留まる。

### 補題の説明

区間 \([-\tfrac12,\tfrac12]\) は前向き不変です：端点で場が内向きだから。

### 証明の概略

1. 閉ループ場 \(f(x)=-(x+\frac12)\) は、区間 \([-\frac12,\frac12]\) の右端 \(\frac12\) で \(f=-1<0\)、左端 \(-\frac12\) で \(f=0\)（内向き）。
2. 軌道がこの区間から出ないことを、端点での符号から示す（`toyClosedLoopField`・`toyInvariantRegion` の定義を展開して計算。68 行）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_initial_sublevel_reaches_ball_boundary"></a>

## 補題 `toy_initial_sublevel_reaches_ball_boundary`

### 式

$$V_{\text{eff}}(-1)\le V_{\text{eff}}(\tfrac12)$$

### Lean のコメント（日本語訳）

> 初期点 \(1/2\) で、全エネルギーの部分準位は、単位球の境界点 \(-1\) に届くので、その閉包は、開球に含まれない。

### 補題の説明

初期点の全劣水準集合は、球の境界点 \(-1\) を含みます（\(0\le\tfrac38\)）。

### 証明の概略

1. 数値計算（\(V_{\text{eff}}(-1)=0\)、\(V_{\text{eff}}(\tfrac12)=\tfrac38\)）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_old_sublevel_barrier_fails"></a>

## 補題 `toy_old_sublevel_barrier_fails`

### 式

$$\neg\bigl(\overline{\{x\in\bar B\mid V_{\text{eff}}\le V_{\text{eff}}(\tfrac12)\}}\subset B\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**以前の入力（全劣水準集合を不変領域にする）の障壁条件は、このモデルでは成り立ちません**。

### 証明の概略

1. \(-1\) が閉包に入り、開球の外（`Metric.mem_ball` の否定）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_invariant_region_closure_inside_ball"></a>

## 補題 `toy_invariant_region_closure_inside_ball`

### 式

$$\overline C\subset B(0,1)$$

### Lean のコメント（日本語訳）

> 選んだ不変領域は、単位球の厳密に内側にある。

### 補題の説明

区間 \([-\tfrac12,\tfrac12]\) は閉集合なので閉包はそれ自身で、開球に含まれます。

### 証明の概略

1. `closure_Icc`（閉区間の閉包）と `Metric.mem_ball`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyNegativeIdentity"></a>

## 定義 `toyNegativeIdentity`

### 式

$$-\mathrm{id}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Hessian（平均場）の \(-1\) 倍の恒等写像です。

### 証明の概略

1. 定義：`-ContinuousLinearMap.id`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyIdentity"></a>

## 定義 `toyIdentity`

### 式

$$\mathrm{id}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

恒等写像（移動度）です。

### 証明の概略

1. 定義：`ContinuousLinearMap.id`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyInvariantRegionStage"></a>

## 定義 `toyInvariantRegionStage`

### 式

$$\text{完全な緩和 H-stage の記録}$$

### Lean のコメント（日本語訳）

> 1 次元のモデルの、完全な、緩和した H 段階の記録。

### 定義の説明

`InvariantRegionMeanFieldStageInput`（StageData）のすべてのフィールドを具体的に与えたものです（中心 0、半径 1、ゲイン 1、曲率 1、…）。

### 証明の概略

1. 各フィールドの条件（\(C^2\)・Riesz 表現・Hessian の下界/上界・閾値・障壁・不変性など）を、上の補題で確認する。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_invariant_region_is_strictly_smaller_than_initial_sublevel"></a>

## 補題 `toy_invariant_region_is_strictly_smaller_than_initial_sublevel`

### 式

$$C\neq\{x\in\bar B\mid V_{\text{eff}}(x)\le V_{\text{eff}}(x_0)\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**選んだ不変領域は、初期点の全エネルギー劣水準集合と等しくない**（より小さい）ことの確認です。つまり、緩和した入力が、以前の入力では扱えなかった範囲を扱えます。

### 証明の概略

1. もし不変領域 \(C\) と初期点の部分準位集合が等しいとすると、\(-1\) が部分準位集合に属す（`norm_num` でポテンシャルの値を計算：\(\tilde V(-1)\le\tilde V(\text{初期点})\)、かつ球の中）。
2. しかし \(-1\) は \(C\) に属さない（\(C\) は \([-\frac12,\frac12]\) 側）ので矛盾（28 行）。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_model_supplies_relaxed_mean_field_stage"></a>

## 補題 `toy_model_supplies_relaxed_mean_field_stage`

### 式

$$\text{Nonempty}\ (\text{InvariantRegionMeanFieldStageInput})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

緩和した段階の入力が**実際に構成できる**（空でない）ことの確認です。

### 証明の概略

1. `toyInvariantRegionStage` を証人にする。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toyModelWitness"></a>

## 定義 `toyModelWitness`

### 式

$$\text{toyInvariantRegionStage の InvariantRegionStageWitness}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

このモデルに、一般の選択関数 `chooseInvariantRegionStageWitness` を適用して得る証人です。

### 証明の概略

1. 定義：`chooseInvariantRegionStageWitness toyInvariantRegionStage`。

----

<a id="Tomabechi.Theorem22InvariantRegionModel.toy_model_has_general_quantitative_orbit"></a>

## 補題 `toy_model_has_general_quantitative_orbit`

### 式

$$\mathrm{rate}=1,\ \ \operatorname{dist}(x(t),x^\*)\le\mathrm{amp}\,e^{-(t-t_0)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

このモデルに一般の定理を適用して得た軌道が、初期条件を満たし、減衰の速さが 1（\(\gamma=1\)、曲率の余裕 \(1\)）で、距離が指数的に減る、という定量的な結論をもつことの確認です。

### 証明の概略

1. `toyModelWitness` の `distance_decay` と、`decayRate = 1` の計算。

----


## コメント修正記録

（なし）
