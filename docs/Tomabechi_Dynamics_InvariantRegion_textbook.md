# Tomabechi/Dynamics/InvariantRegion.lean 解説

> 対象: [`Tomabechi/Dynamics/InvariantRegion.lean`](../Tomabechi/Dynamics/InvariantRegion.lean)（定理22：初期部分準位等式を使わない不変領域入口）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22の**段階ごとの谷・大域軌道・指数減衰**を、`StageData.lean` では「初期エネルギーの**全劣水準集合**」を不変領域に使っていたのを、**任意の前向き不変な部分領域** \(C\) に**緩めた**版です。\(C\) は初期値の全エネルギー劣水準集合である必要はなく、(i) 閾値から得る谷と初期状態が \(C\) に属し、(ii) \(C\) の閉包が局所球の**内部**にあり、(iii) 閉ループ ODE が \(C\) を**前向き不変**にすること、だけが要ります。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `per_stage_valley_global_existence_and_decay_on_invariant_region` | 1 段階：閾値の一意谷を、任意の前向き不変領域上の大域軌道へ接続 |
| `meanField_invariant_region_stage_conclusions` | 平均場の段階入力（不変領域版）への適用 |
| `toInvariantRegionInput` | 以前の（正確な劣水準集合）入力が、緩和した入力へ埋め込まれること |
| `InvariantRegionStageWitness` ほか | 緩和した段階の証人とその補題・選択 |

### 0.3 このファイルが証明していないこと

- **不変性**と**谷の領域への所属**は**入力の条件**です。Hessian の閾値だけから導いたとは主張しません。
- 指数率は、曲率の余裕 \(\kappa pm-\beta\) と移動度の下界 \(\gamma\) による**原論文の定量的な率**です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理22：初期部分準位の等式を使わない不変領域の入口**
>
> この補助モジュールは、段階のポテンシャルの閾値の条件と、別に与えた前向き不変な領域を組み合わせる。領域は、初期値の全エネルギーの部分準位の集合である必要がない。谷・大域軌道・一意性および指数率は、定理21の既存の核から得る。

名前空間は `Tomabechi.Theorem22InvariantRegion`。`open Tomabechi.Theorem21 RealInnerProductSpace`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem22InvariantRegion.per_stage_valley_global_existence_and_decay_on_invariant_region"></a>

## 補題 `per_stage_valley_global_existence_and_decay_on_invariant_region`

### 式

$$C\ \text{前向き不変},\ \overline C\subset B(c,r),\ x^\*,x_0\in C\ \Longrightarrow\ \exists x:[a,\infty)\to C,\ \text{指数減衰（率 }\gamma(\kappa pm-\beta)\text{）,一意}$$

### Lean のコメント（日本語訳）

> 閾値で得る一意な谷を、任意の前向き不変な領域の上の、大域の凍結軌道へ接続する。\(C\) は、初期値の全エネルギーの部分準位と等しい必要はない。必要なのは、初期状態と閾値から得る谷が \(C\) に属し、\(C\) の閉包が局所球の内部にあり、閉ループの ODE が \(C\) を前向き不変にすることである。曲率の余裕 \(\kappa pm-\beta\) と、移動度の下界 \(\gamma\) による、原論文の定量的な指数率を返す。不変性と谷の所属は、入力の条件であり、Hessian の閾値のみから導いたとは主張しない。
> 日本語の要約：初期エネルギーの部分準位との等式を外し、任意の適切な不変領域から、同じ指数率の軌道を得る。

### 補題の説明

`per_stage_valley_global_existence_and_decay`（StageData）の、不変領域を任意にした版です。

### 証明の概略

1. `per_stage_unique_interior_minimum`（StageData）で内部の唯一の最小点、`per_stage_effective_strong_convexity` で強凸性を得る。
2. 部分準位集合を前向き不変集合 \(C\) として選び、`theorem21_state_dependent_mobility_global_existence_and_decay`（任意の前向き不変集合版）を適用して、軌道の大域存在と指数減衰を得る（132 行）。

----

<a id="Tomabechi.Theorem22InvariantRegion.meanField_invariant_region_stage_conclusions"></a>

## 定理 `meanField_invariant_region_stage_conclusions`

### 式

$$\text{平均場の段階入力（不変領域版）}\ \Longrightarrow\ \text{谷・変位・軌道・指数減衰}$$

### Lean のコメント（日本語訳）

> 緩和した谷と軌道の定理を、平均化した平均場の段階へ、直接適用する。積分の表現は、入力の記録が運び、同じ `meanField` が、ポテンシャル・勾配・Hessian を通して供給する。低水準の定理の \(C^1\) の閉ループの仮定は、ここでは、段階の \(C^2\) のポテンシャル・Riesz の勾配の表現・\(C^1\) の移動度から導く。
> 日本語の要約：平均場の積分表示を保持した不変領域の段階入力を、緩和済みの定量的な軌道の結論へ接続する。

### 補題の説明

`InvariantRegionMeanFieldStageInput`（StageData）の各フィールドから、`per_stage_valley_global_existence_and_decay_on_invariant_region` の仮定を整えて適用します。

### 証明の概略

1. 段階入力 `InvariantRegionMeanFieldStageInput` の \(C^2\) 性から、背景・平均場のポテンシャルの \(C^1\) 性と Fréchet 微分の表示（勾配の Riesz 表現）を導く（`contDiffAt_gradient_of_c2` など）。
2. 閉ループ場の \(C^1\) 性を整える。
3. 上の補題 `per_stage_valley_global_existence_and_decay_on_invariant_region` を適用して、段階の結論を得る（110 行）。

----

<a id="Tomabechi.Theorem22InvariantRegion.MeanFieldStageInput.toInvariantRegionInput"></a>

## 定義 `MeanFieldStageInput.toInvariantRegionInput`

### 式

$$\text{MeanFieldStageInput}\ \to\ \text{InvariantRegionMeanFieldStageInput}$$

### Lean のコメント（日本語訳）

> 以前の、正確な初期の部分準位の入力は、緩和した入力に埋め込まれる。谷の所属は、大域的な最小性と、初期の所属から従う。前向きの不変性は、既存の、厳密な内部の障壁と、勾配流の散逸の補題から従う。

### 定義の説明

以前の（初期エネルギーの劣水準集合を不変領域とする）入力は、新しい（任意の不変領域を許す）入力の特殊ケースです。

### 証明の概略

1. 不変領域として `sublevel` をとる。谷が `sublevel` に属すこと：谷は大域最小で、初期点より低いから。前向き不変性：`forward_invariant_sublevel_of_strict_interior_barrier`（GradientFlow）。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness"></a>

## 構造体 `InvariantRegionStageWitness`

### 式

$$\text{minimizer},\ \text{orbit}\ (\text{不変領域内}),\ \text{decay},\ \text{unique}$$

### Lean のコメント（日本語訳）

> 緩和した平均場の入力で添字づけられた、段階の証人。`StageValleyWitness` と異なり、その軌道は、与えられた不変領域に留まり、その領域が、正確なエネルギーの部分準位であることを要求しない。

### 定義の説明

`StageValleyWitness`（StageData）の不変領域版：谷と、不変領域 \(C\) にとどまる軌道、その指数減衰と一意性を束ねます。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.decayAmplitude"></a>

## 定義 `decayAmplitude`

### 式

$$\mathrm{amp}=\sqrt{2\varphi(t_0)/c}$$

### Lean のコメント（日本語訳）

> 距離の評価の、初期のエネルギー差の係数。

### 定義の説明

`StageValleyWitness.decayAmplitude` と同じ定義です。

### 証明の概略

1. 定義：`Real.sqrt (2 * (初期の差) / 曲率余裕)`。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.decayRate"></a>

## 定義 `decayRate`

### 式

$$\mathrm{rate}=\gamma c$$

### Lean のコメント（日本語訳）

> (22.4) に合う、定量的な指数率。

### 定義の説明

距離の減衰の速さ（移動度の下界 × 曲率の余裕）です。

### 証明の概略

1. 定義：`gamma * (gain * presenceGain * curvature - backgroundCurvature)`。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.decayAmplitude_nonneg"></a>

## 補題 `decayAmplitude_nonneg`

### 式

$$\mathrm{amp}\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平方根なので非負です。

### 証明の概略

1. `Real.sqrt_nonneg`。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.decayRate_pos"></a>

## 補題 `decayRate_pos`

### 式

$$\mathrm{rate}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\gamma>0\) と余裕 \(c>0\) の積なので正です。

### 証明の概略

1. `mul_pos`。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.distance_decay"></a>

## 補題 `distance_decay`

### 式

$$\operatorname{dist}(x(t),x^\*)\le\mathrm{amp}\cdot e^{-\mathrm{rate}(t-t_0)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`StageValleyWitness.distance_decay` の不変領域版です。

### 証明の概略

1. `orbit_decay` の第 3 成分を書き直す。

----

<a id="Tomabechi.Theorem22InvariantRegion.InvariantRegionStageWitness.orbit_ode_forward"></a>

## 補題 `InvariantRegionStageWitness.orbit_ode_forward`

### 式

$$\forall t\ge t_0:\ x'(t)=-A(x(t))\,g_{\text{eff}}(x(t))$$

### Lean のコメント（日本語訳）

> 選んだ緩和した凍結軌道は、局所の延長の区間が、段階の開始より厳密に前まで届くので、すべての前向きの時刻で、その ODE を満たす。

### 補題の説明

軌道は開始時刻より少し前から ODE を満たすので、開始時刻でも両側微分が成り立ちます。

### 証明の概略

1. `orbit_ode` の定義域に \(t\ge t_0\) が含まれる。

----

<a id="Tomabechi.Theorem22InvariantRegion.chooseInvariantRegionStageWitness"></a>

## 定義 `chooseInvariantRegionStageWitness`

### 式

$$s\ \mapsto\ \text{InvariantRegionStageWitness}\ s$$

### Lean のコメント（日本語訳）

> 別に証明した段階の定理から、各段階で 1 つの緩和した証人を選ぶ。その列は、各入力の段階と、その自身の領域を保つ。

### 定義の説明

`meanField_invariant_region_stage_conclusions` から証人を選びます（`Classical.choose`）。

### 証明の概略

1. `meanField_invariant_region_stage_conclusions` の存在から `Classical.choose`。

----

<a id="Tomabechi.Theorem22InvariantRegion.chooseAllInvariantRegionStageWitnesses"></a>

## 定義 `chooseAllInvariantRegionStageWitnesses`

### 式

$$\forall n,\ \text{InvariantRegionStageWitness}\ (\text{stages }n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

全段階の証人を選びます。

### 証明の概略

1. 各 \(n\) で `chooseInvariantRegionStageWitness`。

----


## コメント修正記録

（なし）
