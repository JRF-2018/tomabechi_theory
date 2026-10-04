# Tomabechi/Dynamics/StageData.lean 解説

> 対象: [`Tomabechi/Dynamics/StageData.lean`](../Tomabechi/Dynamics/StageData.lean)（定理22の段階ごとのデータ・谷・指数軌道）。
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
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22は、定理21の「局所谷」を**段階（stage）ごとに**繰り返す定理です。記号の台の最小上界（LUB）が段階とともに更新されると、そのたびに新しい中心・新しい谷が現れます。
このファイルは、**各段階を単独で見たとき**に、定理21の結論（谷の存在・唯一性・指数収束）が成り立つための**データ構造と補題**を整えます。段階の**切り替え**（段階 \(n\) から \(n+1\) への移行）は、ここでは扱いません。

### 0.2 構成

| 節 | 宣言 | 内容 |
| --- | --- | --- |
| 1. 段階ごとの解析補題 | `gain_threshold_implies_positive_margin` 〜 `per_stage_valley_global_existence_and_decay` | ゲイン閾値 (22.2)・強凸性・唯一の内部最小点・指数減衰 (22.4) を、1 段階／全段階について述べる |
| 2. 段階データ | `StageValleySpec`, `MeanFieldAveragePresentation`, `MeanFieldStageCore`, `MeanFieldStageInput`, `InvariantRegionMeanFieldStageInput`, `toStageValleySpec`, `meanFieldStageSequence` | 1 段階の入力データの構造体。平均場の積分表現を含むもの |
| 3. 段階の補題 | `stageEffectivePotential` 〜 `closedLoopC1` | 実効ポテンシャル・勾配・\(C^1\) 正則性 |
| 4. 谷の証人 | `StageValleyWitness` とその補題、`chooseStageValley` | 段階の入力から谷と大域軌道を**選ぶ** |
| 5. まとめ | `meanField_stage_theorem21_four_conclusions`, `all_*` | 定理21の 4 結論を段階ごと・全段階について |

### 0.3 用語の対応

- (22.2)：段階ごとの局所 Hessian 条件とゲイン閾値 \(p>\max(\beta,B/r)/(\kappa m)\)。
- (22.4)：段階ごとの指数減衰の評価。
- 「凍結軌道」：段階を固定（凍結）して、その段階の力学だけで進む軌道。

### 0.4 このファイルが証明していないこと

- **段階の切り替え**（ある段階の軌道の終わりが次の段階の初期状態になること、切り替え後の整合）は扱いません。その点は、後の `StageSwitching.lean` や定理23の側です。`all_stages_*` は、段階ごとに独立に構成した谷を一つの列に**選ぶ**だけで、段階間の整合性は仮定も結論もしません。
- 段階ごとの**厳密な内部障壁**（劣水準集合の閉包が開球に含まれること）と**移動度の一様な強制性**は、論文の局所 Hessian の閾値だけからは従わないので、**独立した仮定**として構造体に保持しています（`sublevel_barrier`, `mobility_coercive`）。
- 平均場の積分表現は、カーネルの導関数や微分と積分の交換を仮定しません（平均場とその勾配・Hessian を段階データとして直接与えます）。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理22の段階データと谷・指数軌道**
>
> 旧 `Theorem22.lean` の、段階ごとの強凸性、谷の証人、平均場の入力、および定量的な軌道の API。LUB 容量更新とは独立した段階力学の核として、既存の名前空間・宣言名・証明を保持する。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem22`。`open Tomabechi.Theorem21 RealInnerProductSpace Filter`、`open scoped Topology NNReal`。

---

<a id="Tomabechi.Theorem22.gain_threshold_implies_positive_margin"></a>

## 補題 `gain_threshold_implies_positive_margin`

### 式

$$p>\frac{\max(\beta,B/r)}{\kappa m}\ \Longrightarrow\ p>0,\ \ \kappa pm-\beta>0,\ \ 0\le B/r<\kappa pm$$

### Lean のコメント（日本語訳）

> 閾値 (22.2) から、実効ポテンシャルの強凸性の余裕が正であることを導く。指数減衰の評価に使う \(c_n>0\) へのスカラーな接続である。

> 利得の閾値 (22.2) は、実効ポテンシャルの強凸性の余裕を正にする。
> 日本語の要約：(22.2) の利得閾値から \(c=\kappa pm-\beta>0\) と境界方向の評価の余裕を導く。

### 補題の説明

ゲイン閾値から、強凸性の強さ \(c=\kappa pm-\beta\) が正であること、境界の外向き勾配の余裕 \(B/r<\kappa pm\) が成り立つことを、数だけの計算で示します（`critical_gain_estimates` と同種の補題）。

### 証明の概略

1. \(\max(\beta,B/r)<p\kappa m\)（分母を払う）から、\(\beta<p\kappa m\)、\(B/r<p\kappa m\)。
2. \(p>0\)（非負の閾値より大きい）。`nlinarith` で不等式を整理（17 行）。

----

<a id="Tomabechi.Theorem22.per_stage_unique_interior_minimum"></a>

## 補題 `per_stage_unique_interior_minimum`

### 式

$$(22.2)\ \Longrightarrow\ \exists x^\*\in\operatorname{int}\bar B(c,r),\ \text{唯一の最小点},\ \|x^\*-c\|\le\tfrac{B}{\kappa pm-\beta},\ \text{停留},\ \kappa pm-\beta>0$$

### Lean のコメント（日本語訳）

> 固定された LUB の段階で、論文の局所 Hessian・中心・勾配・ゲイン閾値の仮定は、定理21ですでに証明された、唯一の内部の最小点と変位の上界を与える。この段階の API は閉球の仮定を全部保持する。切り替えがそれらを与える、とは主張しない。
> 日本語の要約：定理22.2 の段階の条件から、閉球の内部の唯一の最小点、中心からの移動量の上界、停留条件、正の曲率の余裕を導く。

### 補題の説明

1 つの段階での谷の存在・唯一性・位置の評価です。中身は定理21の `exists_unique_interior_minimum_of_threshold`（GlobalFlow）を段階の記法で言い直したものです。

### 証明の概略

1. `exists_unique_interior_minimum_of_threshold` で最小点・唯一性・変位の評価。
2. 最小点が内部の局所最小なので勾配が 0（停留）。余裕の正値性は `gain_threshold_implies_positive_margin`（27 行）。

----

<a id="Tomabechi.Theorem22.all_stages_unique_interior_minima"></a>

## 補題 `all_stages_unique_interior_minima`

### 式

$$\forall n,\ (22.2)_n\ \Longrightarrow\ \exists (x^\*_n)_n:\ \text{各段階の唯一の内部最小点・変位・停留・余裕}$$

### Lean のコメント（日本語訳）

> 谷の定理の同時版：(22.2) の段階ごとの仮定のもとで、各層は、唯一の内部の最小点、元の変位の上界、停留性、正の曲率の余裕をもつ。古典的な選択により、段階ごとに個別に証明した最小点を 1 つの列にまとめる。これは、その列に切り替えの整合性を課すものではない。
> 日本語の要約：定理22.2 を全段階に適用し、各段階の唯一の最小点などを 1 つの列に選ぶ。段階間の切り替えの整合は、仮定にも結論にも入れない。

### 補題の説明

上の補題を、すべての段階 \(n\in\mathbb N\) に同時に適用して、最小点の列 \((x^\*_n)\) を選びます（選択公理）。

### 証明の概略

1. 各 \(n\) について `per_stage_unique_interior_minimum` で最小点の存在。
2. `Classical.choose` でそれらを列にまとめる（16 行）。

----

<a id="Tomabechi.Theorem22.per_stage_effective_strong_convexity"></a>

## 補題 `per_stage_effective_strong_convexity`

### 式

$$V-\kappa pS\ \text{は}\ \bar B(c,r)\ \text{で}\ (\kappa pm-\beta)\text{-強凸}$$

### Lean のコメント（日本語訳）

> (22.2) の Hessian の仮定とそのゲイン閾値は、段階ごとの指数評価が必要とする `StronglyConvexOn` の前提を与える。これにより、呼び出し側が実効ポテンシャルの Hessian から強凸性を再び証明する必要がなくなる。
> 日本語の要約：基礎・臨場感ポテンシャルの Hessian の境界とゲイン閾値から、実効ポテンシャルの強凸性を導く。

### 補題の説明

`effective_potential_strongly_convex`（StrongConvexity）の段階版です。閾値から強さが正であること（`gain_threshold_implies_positive_margin`）も使います。

### 証明の概略

1. `gain_threshold_implies_positive_margin` で \(\kappa p\ge0\)。
2. `effective_potential_strongly_convex` を適用（8 行）。

----

<a id="Tomabechi.Theorem22.all_stages_effective_strong_convexity"></a>

## 補題 `all_stages_effective_strong_convexity`

### 式

$$\forall n,\ V_n-\kappa_np_nS_n\ \text{は}\ \bar B(c_n,r_n)\ \text{で}\ c_n=\kappa_np_nm_n-\beta_n\ \text{-強凸}$$

### Lean のコメント（日本語訳）

> 各段階で、ゲイン閾値と、背景・臨場感の Hessian の境界を適用する。これは、定理23が使う添字つきの実効強凸性の前提を与え、段階の余裕 \(c_n=\kappa p_nm_n-\beta_n\) は、仮定されるのではなく導かれる。閉球の幾何、微分のデータ、Hessian の境界は、まさに段階ごとの解析的な入力であり、切り替えや到達可能性の主張はここには含まれない。
> 日本語の要約：各段階の解析的な条件から、曲率の余裕 \(c_n>0\) と強凸性を導く。切り替え・到達可能性は扱わない。

### 補題の説明

上の補題を全段階に適用します。

### 証明の概略

1. 各 \(n\) に `per_stage_effective_strong_convexity` を適用（11 行）。

----

<a id="Tomabechi.Theorem22.per_stage_exponential_decay"></a>

## 補題 `per_stage_exponential_decay`

### 式

$$\forall t\ge t_0:\ \varphi(t)\le\varphi(t_0)e^{-2\gamma c(t-t_0)},\ \ \|x(t)-x^\*\|\le\sqrt{2\varphi(t_0)/c}\,e^{-\gamma c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 固定された段階で、定理21の状態依存の移動度の評価は、ポテンシャル差と状態距離の定量的な速さを与える。もとの定理と同じく、大域的な軌道と前向き不変な劣水準集合は明示的な仮定であり、この結果は切り替えの到達可能性を確立しない。
> 日本語の要約：前向き不変な劣水準集合にとどまる 1 段階の軌道に、定理21のエネルギー差・状態距離の指数評価を適用する。

### 補題の説明

定理21の `theorem21_state_dependent_mobility_global_exponential_decay`（GlobalFlow）の段階での言い直しです。

### 証明の概略

1. 定理21の大域指数減衰の補題をそのまま適用（6 行）。

----

<a id="Tomabechi.Theorem22.per_stage_exponential_decay_of_local_extension"></a>

## 補題 `per_stage_exponential_decay_of_local_extension`

### 式

$$\text{ODE が開区間}\ (t_0-\epsilon,\infty)\ \text{で成立}\ \Longrightarrow\ \text{同じ指数減衰}\ (t\ge t_0)$$

### Lean のコメント（日本語訳）

> 開区間の連鎖律の定理を適用するのに必要な局所的な延長だけをもつ、前向きの軌道からの定量的な減衰。ODE は \([t_0,\infty)\) を含む開区間で要求され、その区間より前や、\(\mathbb R\) 全体での力学は課さない。`htrajectory_local` は、初期状態での局所 ODE 存在が普通に与える、局所領域の条件である。
> 日本語の要約：開始時刻の直前まで延長された局所 ODE の解について、強凸性と移動度の強制性から指数減衰を示す。

### 補題の説明

上の補題の、ODE が全時刻でなく**開始時刻の少し前から**成り立つ版です。局所存在定理（`GradientFlow`）の出力にそのまま使えます。

### 証明の概略

1. 定理21の `theorem21_state_dependent_mobility_exponential_decay`（一般の開区間版）を、開区間 \(I=(t_0-\epsilon,\infty)\) に対して適用する。
2. 局所延長した解の ODE（`hfield`）と、区間内の時刻 \(t_0\le s\le t\) が \(I\) に入ること（\(t_0-\epsilon<s\)）、軌道が部分準位集合に留まること、強凸性・停留点・\(C^1\) 性・係数の条件を渡す（48 行）。

----

<a id="Tomabechi.Theorem22.per_stage_valley_and_exponential_decay"></a>

## 補題 `per_stage_valley_and_exponential_decay`

### 式

$$(22.2)\ +\ \text{軌道・移動度・劣水準集合の仮定}\ \Longrightarrow\ \text{唯一の谷と指数減衰（22.4）}$$

### Lean のコメント（日本語訳）

> (22.2) と (22.4) の 1 段階での統合。Hessian とゲインの条件が、唯一の内部の谷とその停留する実効勾配を構成する。定理21の強凸性の結果が、明示的に前向き不変な劣水準集合上の定量的な減衰を与える。軌道・移動度・劣水準集合の条件は、もとの定理のとおり、仮定のままである。
> 日本語の要約：(22.2) の局所条件から唯一の内点の谷を作り、追加の軌道条件のもとで (22.4) の指数減衰を示す。

### 補題の説明

谷の存在（`per_stage_unique_interior_minimum`）と指数減衰（`per_stage_exponential_decay_of_local_extension`）を 1 つの定理にまとめたものです。軌道は**入力として与えます**（構成はしません）。

### 証明の概略

1. `per_stage_unique_interior_minimum` で最小点、`per_stage_effective_strong_convexity` で強凸性。
2. 最小点の停留性（局所最小で勾配が 0）。
3. `per_stage_exponential_decay_of_local_extension` を適用（48 行）。

----

<a id="Tomabechi.Theorem22.per_stage_valley_global_existence_and_decay"></a>

## 補題 `per_stage_valley_global_existence_and_decay`

### 式

$$\text{有限次元}:\ (22.2)\ +\ \text{初期エネルギーの劣水準集合の厳密な内部障壁}\ \Longrightarrow\ \text{軌道の構成・一意性・指数減衰}$$

### Lean のコメント（日本語訳）

> 軌道を入力として受け取らず、自分で前向きの軌道を構成する、有限次元の段階の定理。(22.2) が唯一の谷を作ったあとで、定理21の局所 ODE の存在、不変な劣水準集合での延長、一意性を適用する。不変領域は、閉球の中の初期エネルギーの劣水準集合であり、散逸がその前向き不変性を証明する。その閉包が厳密に内部にあることは、定理21の大域存在の議論のように、明示的な障壁の条件として残る。

### 補題の説明

**軌道の存在まで示す**段階の定理です。初期エネルギーの劣水準集合 \(C=\{x\in\bar B\mid V_{\text{eff}}(x)\le V_{\text{eff}}(x_0)\}\) を不変領域とし、散逸でその不変性を示します。閉包が開球に入る（障壁）ことは仮定です。

### 証明の概略

1. 谷（`per_stage_unique_interior_minimum`）と強凸性（`per_stage_effective_strong_convexity`）。
2. 定理21の大域存在・指数減衰の補題（`theorem21_state_dependent_mobility_global_existence_and_decay`）を適用（76 行）。

----

<a id="Tomabechi.Theorem22.StageValleySpec"></a>

## 構造体 `StageValleySpec`

### 式

$$\text{center},r,\kappa,p,m,\beta,B,\gamma,\text{startTime},V,S,\nabla V,\nabla S,\operatorname{Hess},A,\text{sublevel},x_0\ +\ \text{仮定の束}$$

### Lean のコメント（日本語訳）

> 谷と軌道を大域的に構成するための、1 つの段階の入力データ。
> 論文の対称な \(C^1\) の移動度と \(C^2\) のポテンシャルが、それらの勾配の Riesz 表現を通じて、閉ループ場の局所的な \(C^1\) 正則性を与える。厳密な内部障壁は、局所 Hessian の境界だけからは出ないので、追加の条件として残る。
> 日本語の注：厳密な内部障壁と、移動度の一様な強制性は、論文の局所 Hessian の閾値だけからは従わないので、独立な条件として保持する。論文に合わせて、移動度の場の \(C^1\) 性・対称性と、ポテンシャルの \(C^2\) 性を入力する。勾配がポテンシャルの Fréchet 微分を Riesz 表現するという条件から、勾配の場と閉ループ場の局所的な \(C^1\) 性を導く。

### 定義の説明

1 つの段階の「設定」を全部束ねた構造体です。主なフィールドは次のとおりです。

- 幾何：中心 `center`、半径 `radius`、初期状態 `initial`、開始時刻 `startTime`
- 定数：ゲイン `gain`（\(\kappa\)）、臨場感 `presenceGain`（\(p\)）、曲率 `curvature`（\(m\)）、背景の曲率 `backgroundCurvature`（\(\beta\)）、勾配の上界 `gradientBound`（\(B\)）、移動度の下界 `gamma`（\(\gamma\)）
- 場：背景ポテンシャル `background`、臨場感ポテンシャル `presence`、それぞれの勾配・Hessian、移動度 `mobility`
- 劣水準集合 `sublevel` とその性質：`initial_mem`（初期点を含む）、`sublevel_barrier`（閉包が開球に入る）、`sublevel_eq`（初期エネルギーの劣水準集合に等しい）
- 仮定：ゲイン閾値 `gain_threshold`、\(C^2\) 性、勾配の Riesz 表現、Hessian の下界・上界、中心での勾配ゼロ、勾配の上界、移動度の \(C^1\) 性・対称性・強制性

### 証明の概略

1. 構造体なので証明はない（フィールドを与えて構成する）。

----

<a id="Tomabechi.Theorem22.MeanFieldAveragePresentation"></a>

## 構造体 `MeanFieldAveragePresentation`

### 式

$$S_\mu(x)=\int K(x,a)\,d\mu(a),\quad \operatorname{supp}\mu\subset\text{sourceLayer},\ \ b=\sup\operatorname{supp}\mu\in\text{sourceLayer},\ \ \text{center}=x_b$$

### Lean のコメント（日本語訳）

> (21.1) の平均化された再構成場の表現。層の台、その最小上界、表される中心を含む。カーネルはスカラー場として積分され、カーネルの導関数や、微分と積分の交換は仮定しない。

### 定義の説明

平均場 \(S_\mu\) を「**原子（atom）の束**上の確率測度での積分」として書き表すデータです。原子は半順序集合をなし、最上位 `abstractTop`（論文の「空」）は層に入りません。測度の台の最小上界 `supportLub` が層に入り、その像が段階の中心 `centerRepresentation` になります。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.MeanFieldAveragePresentation.integralValue"></a>

## 定義 `integralValue`

### 式

$$\int K(x,a)\,d\mu(a)$$

### Lean のコメント（日本語訳）

> 平均化された場で使う、点ごとのスカラーの積分。

### 定義の説明

各点 \(x\) で、再構成カーネル \(K(x,\cdot)\) を原子の測度で積分した値です。

### 証明の概略

1. 定義：`∫ a, p.reconstructionKernel x a ∂p.atomMeasure`。

----

<a id="Tomabechi.Theorem22.MeanFieldStageCore"></a>

## 構造体 `MeanFieldStageCore`

### 式

$$\text{center}=x_{\sup\operatorname{supp}\mu},\ \ S(x)=\int K(x,a)\,d\mu(a),\ \ \text{平均場とその勾配・Hessian}\ +\ \text{閾値・障壁・移動度の仮定}$$

### Lean のコメント（日本語訳）

> 臨場感ポテンシャルがすでに定理21の平均場 \(S_\mu\) である、定理22の 1 つの段階。この記録は、平均場とその勾配と Hessian を段階データとして受け取り、カーネルの点ごとの導関数や、原子についての微分と積分の交換の証明は要求しない。層の台、その LUB \(b\)、表現 \(x_b\)、そして `meanField x = ∫ K(x,a) ∂μ` を示す積分の表現を記録する。残りの障壁・移動度・初期の劣水準集合の条件は、すべて明示的な H 段階の入力である。

### 定義の説明

`StageValleySpec` の臨場感ポテンシャルを、定理21の**平均場**に置き換えた構造体です。`StageValleySpec` との違いは、(i) 中心が台の LUB の像として決まる（`center_eq_supportLub_representation`）、(ii) 平均場が積分と等しい（`meanField_eq_integral`）、(iii) 劣水準集合の等式 `sublevel_eq` を**含まない**（次の 2 つの構造体が追加する）、の 3 点です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.MeanFieldStageInput"></a>

## 構造体 `MeanFieldStageInput`

### 式

$$\text{MeanFieldStageCore}\ +\ \text{sublevel}=\{x\in\bar B\mid V_{\text{eff}}(x)\le V_{\text{eff}}(x_0)\}$$

### Lean のコメント（日本語訳）

> もとの厳密な劣水準集合の段階の入力。共有された平均場の解析データの特殊化として残してある。

### 定義の説明

`MeanFieldStageCore` に「劣水準集合は初期エネルギー以下の集合に**等しい**」という等式を足したものです（正確な劣水準集合版）。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.InvariantRegionMeanFieldStageInput"></a>

## 構造体 `InvariantRegionMeanFieldStageInput`

### 式

$$\text{MeanFieldStageCore}\ +\ \text{(最小点}\in C\text{)}\ +\ \text{(}C\ \text{は前向き不変)}$$

### Lean のコメント（日本語訳）

> 任意の前向き不変な領域をもつ H 段階の平均場データ。共有の核は、積分の表現と、閾値のすべての解析的な条件を保持する。領域は、初期エネルギーの劣水準集合の全体である必要はない。閾値の最小点の所属と前向き不変性は、もとの定理の力学的な仮定と同じく、明示的な条件である。

### 定義の説明

劣水準集合の等式の代わりに、「最小点が領域に入る」（`minimizer_in_sublevel`）と「領域は前向き不変」（`forward_invariant`）を**仮定**する版です。不変領域を自由に選べます。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.MeanFieldStageInput.toStageValleySpec"></a>

## 定義 `MeanFieldStageInput.toStageValleySpec`

### 式

$$\text{MeanFieldStageInput}\to\text{StageValleySpec},\quad \text{presence}:=\text{meanField}$$

### Lean のコメント（日本語訳）

> 平均場の段階データを、共通の谷の仕様に変換する。これはフィールドごとの構成であり、`presence` は、ポテンシャルと劣水準集合の条件で使うのとまったく同じ平均場に設定する。

### 定義の説明

平均場の段階の入力を、共通の `StageValleySpec` の形に写します（臨場感ポテンシャルを平均場にする）。以降の谷の構成は `StageValleySpec` に対して行われます。

### 証明の概略

1. フィールドごとに対応づける（43 行）：`presence := meanField`, `presenceGradient := meanFieldGradient` など。

----

<a id="Tomabechi.Theorem22.meanFieldStageSequence"></a>

## 定義 `meanFieldStageSequence`

### 式

$$n\mapsto\text{(stages }n\text{).toStageValleySpec}$$

### Lean のコメント（日本語訳）

> LUB で添字づけられた段階の列を、どの平均場も変えずに変換する。

### 定義の説明

段階の入力の列（`ℕ → MeanFieldStageInput E`）を、`StageValleySpec` の列に写します。

### 証明の概略

1. 定義：各 \(n\) に `toStageValleySpec` を適用。

----

<a id="Tomabechi.Theorem22.stageEffectivePotential"></a>

## 定義 `stageEffectivePotential`

### 式

$$V_{\text{eff}}(x)=V(x)-\kappa p\,S(x)$$

### Lean のコメント（日本語訳）

> パッケージ化された段階の入力から、臨場感で重みづけされた段階のポテンシャル。
> 日本語の要約：背景ポテンシャルから、ゲインで重みづけされた臨場感ポテンシャルを引いた、段階の実効ポテンシャル。

### 定義の説明

段階 \(s\) の実効ポテンシャル：背景ポテンシャル − ゲイン × 臨場感 × 臨場感ポテンシャル。

### 証明の概略

1. 定義：`s.background x - s.gain * s.presenceGain * s.presence x`。

----

<a id="Tomabechi.Theorem22.stageEffectiveGradient"></a>

## 定義 `stageEffectiveGradient`

### 式

$$g_{\text{eff}}(x)=\nabla V(x)-\kappa p\,\nabla S(x)$$

### Lean のコメント（日本語訳）

> 臨場感で重みづけされた段階のポテンシャルの勾配。
> 日本語の要約：段階の実効ポテンシャルを構成する勾配場を定義する。

### 定義の説明

実効ポテンシャルの勾配場です。

### 証明の概略

1. 定義：`s.backgroundGradient x - (s.gain * s.presenceGain) • s.presenceGradient x`。

----

<a id="Tomabechi.Theorem22.StageValleySpec.backgroundContDiffOnOne"></a>

## 補題 `StageValleySpec.backgroundContDiffOnOne`

### 式

$$V\in C^2\ \text{at each point of}\ \bar B\ \Longrightarrow\ V\in C^1(\bar B)$$

### Lean のコメント（日本語訳）

> 段階の閉球上での \(C^1\) 正則性を、周りの空間での点ごとの \(C^2\) のデータから導く。
> 日本語の要約：閉球上の各点でのポテンシャルの \(C^2\) 性から、閉球上での \(C^1\) 性を導く。

### 補題の説明

各点で \(C^2\) なら、その点で \(C^1\)（`ContDiffAt.of_le`）、したがって球の上で \(C^1\) です。

### 証明の概略

1. 各点の \(C^2\) 性を \(C^1\) に弱めて、`ContDiffOn` にまとめる（4 行）。

----

<a id="Tomabechi.Theorem22.StageValleySpec.presenceContDiffOnOne"></a>

## 補題 `StageValleySpec.presenceContDiffOnOne`

### 式

$$S\in C^2\ \text{at each point of}\ \bar B\ \Longrightarrow\ S\in C^1(\bar B)$$

### Lean のコメント（日本語訳）

> 同じことを臨場感ポテンシャルに適用する。
> 日本語の要約：臨場感ポテンシャルの \(C^2\) 性から、閉球上の \(C^1\) 性を導く。

### 補題の説明

上と同じ議論を臨場感ポテンシャルに適用します。

### 証明の概略

1. 同様（4 行）。

----

<a id="Tomabechi.Theorem22.StageValleySpec.backgroundHasFDerivAt"></a>

## 補題 `StageValleySpec.backgroundHasFDerivAt`

### 式

$$DV(x)=\langle\nabla V(x),\cdot\rangle\ \ (x\in\bar B)$$

### Lean のコメント（日本語訳）

> Riesz の表現は、段階の球の上で、勾配を背景ポテンシャルの微分と同一視する。
> 日本語の要約：背景ポテンシャルの Riesz の勾配の表現から、微分可能性を得る。

### 補題の説明

勾配が Riesz 表現（`innerSL (gradient x) = fderiv`）で与えられているので、\(V\) は微分可能で、その微分は勾配との内積です。

### 証明の概略

1. \(C^2\)（したがって微分可能）の仮定から `HasFDerivAt`、導関数を勾配の表現で書き換える（6 行）。

----

<a id="Tomabechi.Theorem22.StageValleySpec.presenceHasFDerivAt"></a>

## 補題 `StageValleySpec.presenceHasFDerivAt`

### 式

$$DS(x)=\langle\nabla S(x),\cdot\rangle\ \ (x\in\bar B)$$

### Lean のコメント（日本語訳）

> 同じ議論を臨場感ポテンシャルに適用する。
> 日本語の要約：臨場感ポテンシャルの Riesz の勾配の表現から、微分可能性を得る。

### 補題の説明

上と同じ議論を臨場感ポテンシャルに適用します。

### 証明の概略

1. 同様（6 行）。

----

<a id="Tomabechi.Theorem22.contDiffAt_gradient_of_c2"></a>

## 補題 `contDiffAt_gradient_of_c2`

### 式

$$f\in C^2\ \text{at}\ x,\ \ \langle g(y),\cdot\rangle=Df(y)\ (\forall y)\ \Longrightarrow\ g\in C^1\ \text{at}\ x$$

### Lean のコメント（日本語訳）

> スカラーの \(C^2\) ポテンシャルは、その勾配が Hilbert 空間上の Riesz 写像を通じて Fréchet 微分で表されるとき、\(C^1\) の勾配をもつ。
> 日本語の要約：Riesz の表現で勾配を微分として定めると、ポテンシャルが \(C^2\) であることから、勾配が \(C^1\) であることが従う。

### 補題の説明

`GradientFlow.lean` の `rieszGradient_contDiffAt_of_contDiffAt_two` と同じ内容を、勾配が**与えられた**形（Riesz 表現の等式つき）で述べたものです。

### 証明の概略

1. \(Df\) が \(C^1\)（`ContDiffAt` の \(C^2\) から）。
2. Riesz 同型（連続線形等長同値）を合成して \(C^1\)。
3. 勾配 \(g\) は表現の等式から Riesz 同型と \(Df\) の合成と一致する（21 行）。

----

<a id="Tomabechi.Theorem22.StageValleySpec.closedLoopC1"></a>

## 補題 `StageValleySpec.closedLoopC1`

### 式

$$x\mapsto-A(x)\,g_{\text{eff}}(x)\ \text{は}\ \bar B\ \text{の各点で}\ C^1$$

### Lean のコメント（日本語訳）

> 論文の各因子の \(C^1\) 性から、段階の閉ループのベクトル場の局所的な \(C^1\) 性を導く。
> 日本語の要約：移動度の場と実効勾配の場の \(C^1\) 性を合成して、ODE の構成に必要な閉ループ場の正則性を得る。

### 補題の説明

移動度 \(A\)（\(C^1\)）と実効勾配（\(C^1\)、直前の補題）の合成は \(C^1\) です。ODE の局所存在に必要な正則性になります。

### 証明の概略

1. 実効勾配が \(C^1\)：`contDiffAt_gradient_of_c2` を背景・臨場感に適用して差と定数倍。
2. \(A\) の \(C^1\) 性との合成（`ContDiffAt.clm_apply`）と符号反転（13 行）。

----

<a id="Tomabechi.Theorem22.StageValleyWitness"></a>

## 構造体 `StageValleyWitness`

### 式

$$x^\*,\ x(\cdot):\ \text{minimizer},\ \text{唯一性},\ \text{変位},\ \text{停留},\ \text{余裕},\ \text{軌道},\ \text{初期条件},\ \text{ODE},\ \text{劣水準集合},\ \text{減衰},\ \text{一意性}$$

### Lean のコメント（日本語訳）

> 段階の解析データが与える、選ばれた最小点と大域的な凍結軌道。`orbit_decay` は、エネルギー差と状態距離の両方の速さを、正確な段階の定数とともに保持する。
> 日本語の要約：段階の唯一の最小点、初期状態からの凍結軌道、減衰と一意性の証明の情報をまとめる。

### 定義の説明

段階 \(s\) について、「谷（最小点）」と「その谷へ収束する大域軌道」の**証明の束**です。フィールド：最小点 `minimizer`（内部・最小・唯一・変位の評価・停留・正の余裕）と、軌道 `orbit`（局所延長 `local_extension`、初期条件、ODE、劣水準集合にとどまる、`orbit_decay`（エネルギー差と距離の指数減衰）、`orbit_unique`（一意性））です。

### 証明の概略

1. 構造体なので証明はない。フィールドは、最小点 `minimizer`・内点性・最小性・一意性・変位の評価・停留性・（軌道の）フィールドなど、一段階の谷についての証人データ（`chooseStageValley` が `StageValleySpec` から構成する）。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.decayAmplitude"></a>

## 定義 `decayAmplitude`

### 式

$$\mathrm{amp}=\sqrt{\frac{2\varphi(t_0)}{c}}\ \ \ (c=\kappa pm-\beta)$$

### Lean のコメント（日本語訳）

> 初期のエネルギー差が、(22.4) の距離の係数を与える。
> 日本語の要約：初期のポテンシャル差と曲率の余裕で定まる、距離の評価の係数を定義する。

### 定義の説明

距離の指数評価 \(\|x(t)-x^\*\|\le\mathrm{amp}\cdot e^{-\gamma c(t-t_0)}\) の前の係数です。

### 証明の概略

1. 定義：`Real.sqrt (2 * (初期の差) / (gain * presenceGain * curvature - backgroundCurvature))`。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.decayRate"></a>

## 定義 `decayRate`

### 式

$$\mathrm{rate}=\gamma c\ \ (c=\kappa pm-\beta)$$

### Lean のコメント（日本語訳）

> (22.4) の指数的な状態距離の速さ \(\gamma_nc_n\)。
> 日本語の要約：移動度の定数と曲率の余裕の積で、指数減衰の速さを定義する。

### 定義の説明

距離が減衰する速さ（移動度の下界 × 強凸の強さ）です。

### 証明の概略

1. 定義：`s.gamma * (s.gain * s.presenceGain * s.curvature - s.backgroundCurvature)`。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.decayAmplitude_nonneg"></a>

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

<a id="Tomabechi.Theorem22.StageValleyWitness.decayRate_pos"></a>

## 補題 `decayRate_pos`

### 式

$$\mathrm{rate}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\gamma>0\) と余裕 \(c>0\) の積なので正です。

### 証明の概略

1. `mul_pos s.gamma_pos w.positive_margin`。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.distance_decay"></a>

## 補題 `distance_decay`

### 式

$$\operatorname{dist}(x(t),x^\*)\le\mathrm{amp}\cdot e^{-\mathrm{rate}\,(t-t_0)}$$

### Lean のコメント（日本語訳）

> (22.4) の状態距離の部分を、定理23が消費する定数に書き直す。
> 日本語の要約：選ばれた軌道の状態距離についての、定量的な指数評価を取り出す。

### 補題の説明

`orbit_decay` の第 3 成分（ノルムの評価）を、`decayAmplitude`・`decayRate` を使った形に書き直します。

### 証明の概略

1. `orbit_decay` の第 3 成分を取り出し、`dist = ‖·‖` と指数部の符号の整理（11 行）。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.orbit_ode_forward"></a>

## 補題 `orbit_ode_forward`

### 式

$$\forall t\ge t_0:\ x'(t)=-A(x(t))\,g_{\text{eff}}(x(t))$$

### Lean のコメント（日本語訳）

> 選ばれた凍結軌道は、すべての前向きの時刻で、閉ループの ODE を解く。ODE の存在が与える局所的な延長が、初期の端点を覆う。
> 日本語の要約：構成した凍結軌道が、段階の開始後のすべての時刻で、閉ループの ODE を満たす。

### 補題の説明

軌道は開区間 \((t_0-\epsilon,\infty)\) で ODE を満たす（`orbit_ode`）ので、\(t\ge t_0\) でも成り立ちます。

### 証明の概略

1. `orbit_ode` の定義域に \(t\ge t_0\) が入ることを確認（5 行）。

----

<a id="Tomabechi.Theorem22.StageValleyWitness.orbit_in_closedBall"></a>

## 補題 `orbit_in_closedBall`

### 式

$$\forall t\ge t_0:\ x(t)\in\bar B(c,r)$$

### Lean のコメント（日本語訳）

> 大域存在の証明で使う不変な劣水準集合は、段階の閉球に含まれる。したがって、前向きの軌道の状態はすべて、Hessian と移動度の条件が仮定された局所領域にとどまる。
> 日本語の要約：劣水準集合の閉球への包含を使って、前向きの軌道がすべて段階の閉球にとどまることを示す。

### 補題の説明

軌道は劣水準集合にとどまり（`orbit_in_sublevel`）、劣水準集合は閉球に含まれます（`sublevel_eq`/`sublevel_barrier` から）。

### 証明の概略

1. `orbit_in_sublevel`、および劣水準集合 ⊆ 閉球（5 行）。

----

<a id="Tomabechi.Theorem22.chooseStageValley"></a>

## 定義 `chooseStageValley`

### 式

$$\text{StageValleySpec}\ s\ \Longrightarrow\ \text{StageValleyWitness}\ s$$

### Lean のコメント（日本語訳）

> 定理22の局所的な仮定と、述べられた大域存在の障壁を満たすすべての段階について、その唯一の谷と唯一の前向きの軌道を選ぶ。この構成は段階の添字について点ごとであり、したがって段階どうしで共通の半径・ゲイン・移動度を仮定しない。
> 日本語の要約：有限次元の段階の条件から、谷と全前向きの凍結軌道の証人を構成する。

### 定義の説明

段階の入力 `StageValleySpec`（有限次元）から、谷と軌道の証人 `StageValleyWitness` を**構成する**関数です（古典的な選択）。

### 証明の概略

1. 背景・臨場感の \(C^1\) 性と微分の表現（上の補題）。
2. `per_stage_valley_global_existence_and_decay` で、最小点・軌道・減衰・一意性の存在を得て、`Classical.choose` で取り出す。
3. 閉ループ場の \(C^1\) 性（`closedLoopC1`）、閾値（`gain_threshold_implies_positive_margin`）を使う（60 行）。

----

<a id="Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions"></a>

## 定理 `meanField_stage_theorem21_four_conclusions`

### 式

$$\begin{aligned}
&\text{平均場の段階入力 }s,\ \ \text{ゴールは枝の上},\ \ \sum_gm(x,g)=1,\ \ a(x,\cdot)\ \text{は a.e. 単射},\ \ H(G\mid X)>0,\ \ \text{枝表象は単射・単調}\\
&\Longrightarrow\ \exists\ \text{証人 }w:\ \ \text{(1) 内部の唯一の最小点 }x^\ast,\ \ \text{(2) }\|x^\ast-c\|\le\tfrac{B}{g\,p\,m-\beta},\\
&\qquad\text{(3) 不変な大域軌道と指数減衰（部分準位集合内、距離・ポテンシャル差）},\ \ \text{(4) 情報容量：枝の制約付き有限 CMI}=H(G\mid X)
\end{aligned}$$
（(4) は有限 CMI 版。KL 型 CMI への接続は `meanField_stage_theorem21_four_conclusions_directKL`。）

### Lean のコメント（日本語訳）

> 平均化された段階の場についての、定理21の 4 つの結論のグループ：唯一の内部の谷、変位/停留性、不変な大域軌道とその定量的な指数の速さ、そして独立な正の情報容量の結論。情報の法則は明示的な入力であり、谷の力学から推論されるものではない。

### 補題の説明

定理21の 4 結論（最小点・位置の評価・軌道と減衰・情報容量）を、平均場の段階（`MeanFieldStageInput`）について 1 つの定理にまとめます。**情報容量は谷の力学とは独立の入力**（入力分布 \(\mu\)、行動・目標の仮定）から得ます。

### 証明の概略

1. `toStageValleySpec` で `StageValleySpec` にして、`chooseStageValley` で証人 \(w\) を選ぶ。
2. 谷と軌道の結論は \(w\) のフィールドから（`minimizer_interior`, `displacement_bound`, `orbit_in_sublevel`, `distance_decay`, `orbit_ode_forward`）。
3. 情報容量は `theorem21_branch_constrained_information_capacity`（DeterministicOutput）から（35 行）。

----

<a id="Tomabechi.Theorem22.chooseAllStageValleys"></a>

## 定義 `chooseAllStageValleys`

### 式

$$\forall n,\ \text{StageValleyWitness}\ (\text{stages }n)$$

### Lean のコメント（日本語訳）

> 個別に検証された大域的な谷の構成から、段階ごとの最小点と凍結軌道を同時に選ぶ。
> 日本語の要約：段階ごとに構成した谷の証人を、全段階にわたって選ぶ。

### 定義の説明

各段階で `chooseStageValley` を使い、全段階の証人を（段階の添字についての依存関数として）選びます。

### 証明の概略

1. 定義：`fun n => chooseStageValley (stages n)`。

----

<a id="Tomabechi.Theorem22.all_stages_have_global_valley_orbits"></a>

## 補題 `all_stages_have_global_valley_orbits`

### 式

$$\exists\ \text{witnesses}:\ \forall n,\ \text{最小点・初期条件・減衰係数・ODE・閉球にとどまる}$$

### Lean のコメント（日本語訳）

> 独立に構成された段階の証人を、段階ごとの結果が使う前向きの軌道の形に正確にまとめる：選ばれた各軌道は、その段階の指定された初期状態から始まり、閉じた局所領域にとどまり、すべての前向きの時刻で閉ループの ODE を解き、明示的な指数の距離の評価をもつ。
> 日本語の要約：全段階の谷・軌道・指数減衰・ODE の成立・閉球内への滞在を、一括して結論する。

### 補題の説明

全段階の証人を選び、各段階の結論をまとめて述べた定理です。**段階間の接続**（段階 \(n\) の軌道の終わりと段階 \(n+1\) の初期状態の関係）は何も述べません。

### 証明の概略

1. `chooseAllStageValleys` で証人の族を選ぶ。
2. 各段階の結論は証人のフィールドと `distance_decay`, `orbit_ode_forward`, `orbit_in_closedBall` から（18 行）。

----

<a id="Tomabechi.Theorem22.chooseAllMeanFieldStageValleys"></a>

## 定義 `chooseAllMeanFieldStageValleys`

### 式

$$\forall n,\ \text{StageValleyWitness}\ ((\text{meanFieldStageSequence stages})\,n)$$

### Lean のコメント（日本語訳）

> LUB で添字づけられた平均場の段階の入力の族から、定理21/22のすべての最小点と凍結軌道を直接構成する。これは、各段階の平均場・移動度・局所の劣水準集合・軌道を、同じ添字つきのデータの中に保つ。

### 定義の説明

平均場の段階の族から、全段階の証人を構成します（`meanFieldStageSequence` と `chooseAllStageValleys`）。

### 証明の概略

1. 定義：`chooseAllStageValleys (meanFieldStageSequence stages)`。

----

<a id="Tomabechi.Theorem22.all_mean_field_stages_have_global_valley_orbits"></a>

## 補題 `all_mean_field_stages_have_global_valley_orbits`

### 式

$$\exists\text{witnesses}:\ \text{内部最小点},\ \text{変位},\ \text{軌道}\ (\text{劣水準集合・指数距離減衰・ODE})$$

### Lean のコメント（日本語訳）

> 段階ごとの谷の定理を、原子ごとの再構成カーネルではなく、平均化された場に適用する。選ばれた各証人は、定理21の唯一の最小点と停留点の証明も運ぶ。厳密な障壁と強制的な移動度は、明示的な H 段階の条件のままである。

### 補題の説明

平均場の段階の族について、全段階の谷・軌道を一括して述べます。各段階で最小点が内部にあること、中心からの変位の評価、軌道が劣水準集合にとどまり距離が指数減衰し ODE を満たすこと、を含みます。

### 証明の概略

1. `chooseAllMeanFieldStageValleys` で証人の族を選び、各フィールドから結論を取り出す（11 行）。

----


## コメント修正記録

（なし）
