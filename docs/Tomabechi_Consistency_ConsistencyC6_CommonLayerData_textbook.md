# Tomabechi/Consistency/ConsistencyC6_CommonLayerData.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_CommonLayerData.lean`](../Tomabechi/Consistency/ConsistencyC6_CommonLayerData.lean)（共通束上の定理24・26・27 のデータ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共通束 `WithTop ℕ` の上の**定理24・26・27 のデータ**を作るファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の、制御・費用の土台です。

* **有限層**：C1 の二主体の状態と、可測な有界ゲインの族。最大ゲイン 3 の制御と、**正の基準値**（baseline）を持つ。割引した費用の最適値は \(1+\tfrac{8d^2}{7}\)（\(d\) は初期の差の半分）で、これを実際に積分して求め、最大ゲインがすべてのゲインの中で最小であることを示す。
* **頂点**：C5 の上位のベクトル状態・方策・費用。定理26・27の解析条件は、既存の C5 の証人から移送する。
* 両方を、層ごとの型を持つ**一つのデータ** `c6LayeredNonnegativeTimeData` にまとめる（C1 の下位層を一点の型に潰さない）。
* 有限層の走行費は、箱の中で C1 の基礎評価 \(V_0\) に一致し、中心で再中心化した二次評価 \(1+16P\) にも一致する。
* 定理24（全有限層）、定理24→26、定理27 の結論を、このデータの上で得る。
* 補助として、C5 のデータを層の写像で**引き戻した**別の構成（`c6C5PullbackData`）も与える。

### 0.2 このファイルが証明していないこと

* 頂点の定理26・27の解析条件は、C5 の具体モデルからの移送です。
* 許容方策は、有限層は有界可測ゲイン、頂点は C5 の方策（有界可測ゲインのフィードバック）です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通束 `WithTop ℕ` の各有限層には C1 の二主体状態と全可測有界ゲイン族を置き、頂点には C5 の上位ベクトル状態・方策・費用を置く。有限層は最大ゲイン3の C1 制御と正 baseline を持ち、頂点の 26/27 解析条件は既存 C5 証人から移送する。両方を同じ層添字付きデータ `c6LayeredNonnegativeTimeData` にまとめる。

---

<a id="Tomabechi.Consistency.C6.c1ControlledOrbit_continuous"></a>

## 補題 `c1ControlledOrbit_continuous`

### 式

$$
s\mapsto\mathrm{orbit}(s)\ \text{は連続}
$$

### Lean のコメント（日本語訳）

> 全実数上のC1制御軌道は連続である。開始時刻より前は、その時刻からの再始動等式で開始を動かして有限前向き区間の絶対連続性を使う。

### 補題の説明

全実数の上で、C1 の制御軌道は連続です。開始時刻より前では、その時刻からの再始動の等式で開始時刻を動かして、有限の前向き区間での絶対連続性を使います。

### 証明の概略

1. \(s\le T\) の場合：区間 \([s-1,T+1]\) をとり、再始動の等式で、\(s-1\) から始めた軌道に直す。有限区間で絶対連続なので連続。
2. \(s>T\) の場合：開始時刻 \(T\) からの絶対連続性（有限区間）から連続。

----

<a id="Tomabechi.Consistency.C6.controlledConsensusState_continuous"></a>

## 補題 `controlledConsensusState_continuous`

### 式

$$
s\mapsto\text{二主体軌道}(s)\ \text{は連続}
$$

### Lean のコメント（日本語訳）

> C1二主体軌道も、任意の可測ゲイン方策に対して連続である。

### 補題の説明

C1 の二主体の軌道も、任意の可測ゲインに対して連続です。

### 証明の概略

1. 半差の積分軌道は連続（前の補題）。平均は一定。座標は平均と半差の和・差。

----

<a id="Tomabechi.Consistency.C6.controlledConsensusState_halfDifference_continuous"></a>

## 補題 `controlledConsensusState_halfDifference_continuous`

### 式

$$
s\mapsto\text{halfDiff}(\text{軌道}(s))\ \text{は連続}
$$

### Lean のコメント（日本語訳）

> 半差は連続な二主体軌道の座標線形写像なので連続である。

### 補題の説明

差の半分は、連続な二主体軌道の座標の線形な写像なので、連続です。

### 証明の概略

1. 前の補題で軌道は連続。座標の射影は連続。差を 2 で割る。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_discounted_cost_measurable"></a>

## 補題 `c1FiniteLayer_discounted_cost_measurable`

### 式

$$
s\mapsto\text{割引費用の被積分関数}\ \text{は可測}
$$

### Lean のコメント（日本語訳）

> 任意のC1ゲイン競合が作る割引評価被積分関数は可測である。

### 補題の説明

任意の C1 のゲインが作る、**割引した費用の被積分関数**は可測です。

### 証明の概略

1. 割引の重み \(e^{-(s-T)}\) と、\(1+8d(s)^2\) は連続（前の補題）なので、積は連続、したがって可測。`ofReal` との合成も可測。

----

<a id="Tomabechi.Consistency.C6.c6_future_exp_integrable"></a>

## 補題 `c6_future_exp_integrable`

### 式

$$
c>0\Rightarrow s\mapsto e^{-c(s-T)}\ \text{は将来半直線で可積分}
$$

### Lean のコメント（日本語訳）

> 将来半直線上の指数関数は積分可能。率 `c>0` を明示しておく。

### 補題の説明

将来の半直線 \([T,\infty)\) の上で、指数関数 \(e^{-c(s-T)}\)（\(c>0\)）は可積分です。

### 証明の概略

1. 半直線 \((T,\infty)\) 上の \(e^{-cs}\) の可積分性（`integrableOn_exp_mul_Ioi`）。
2. 閉半直線への移行（1 点は測度 0）。\(e^{cT}\) 倍の定数倍。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_optimalValue_integral"></a>

## 補題 `c1FiniteLayer_optimalValue_integral`

### 式

$$
\int_T^\infty e^{-(s-T)}\bigl(1+8d(s)^2\bigr)ds=1+\frac{8d^2}{7}
$$

### Lean のコメント（日本語訳）

> 最大ゲイン3の有限層C1割引評価は実際に積分でき、候補価値は `1 + 8 d²/7`（`d` は初期半差）となる。

### 補題の説明

最大ゲイン 3 の有限層の C1 の**割引した評価**は、実際に積分でき、その値（最適値の候補）は \(1+\tfrac{8d^2}{7}\) です（\(d\) は初期の差の半分）。

### 証明の概略

1. 被積分関数は \(e^{-(s-T)}+8d^2\,e^{-7(s-T)}\)（次の補題）。
2. \(\int_0^\infty e^{-u}du=1\)、\(\int_0^\infty e^{-7u}du=\tfrac17\)。\(1+8d^2/7\)。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_optimal_integrand_eq"></a>

## 補題 `c1FiniteLayer_optimal_integrand_eq`

### 式

$$
e^{-(s-T)}\bigl(1+8d(s)^2\bigr)=e^{-(s-T)}+8d_0^2e^{-7(s-T)}
$$

### Lean のコメント（日本語訳）

> 最大ゲインのC1有限層割引被積分関数を二つの指数核に分ける恒等式。

### 補題の説明

最大ゲインでの、割引した被積分関数を、二つの指数の項に分ける恒等式です。

### 証明の概略

1. 差の半分は \(d_0e^{-3(s-T)}\)（最大ゲインの累積量 \(3(s-T)\)）。二乗すると \(d_0^2e^{-6(s-T)}\)。割引の重み \(e^{-(s-T)}\) との積で \(e^{-7(s-T)}\)。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_optimalCost_integrable"></a>

## 補題 `c1FiniteLayer_optimalCost_integrable`

### 式

$$
\text{最大ゲインの割引費用は可積分}
$$

### Lean のコメント（日本語訳）

> C1有限層の最大ゲイン費用は、将来半直線上で可積分である。

### 補題の説明

最大ゲインの割引費用は、将来の半直線の上で可積分です。

### 証明の概略

1. 前の補題で二つの指数関数の和（率 1 と率 7）。それぞれ可積分（`c6_future_exp_integrable`）。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_optimalValue_minimal"></a>

## 補題 `c1FiniteLayer_optimalValue_minimal`

### 式

$$
1+\tfrac{8d^2}{7}\le\int\bigl(\text{任意のゲインの割引費用}\bigr)
$$

### Lean のコメント（日本語訳）

> 有限層の割引最適値は、全てのC1ゲイン競合の拡張実数費用以下。

### 補題の説明

有限層の割引した最適値は、**すべての C1 のゲイン**の（拡張実数の）費用以下です。

### 証明の概略

1. 最大ゲインの被積分関数は、各時刻で他のゲインの被積分関数以下（差の二乗の比較 `c1MaxGain_orbit_sq_le`）。
2. 最大ゲインの費用は積分値 \(1+8d^2/7\)（前の補題）。積分の単調性で結ぶ。

----

<a id="Tomabechi.Consistency.C6.C6LayeredState"></a>

## 定義 `C6LayeredState`

### 式

$$
\text{有限層}:\ \mathrm{AgentState},\quad\text{頂点}:\ \text{C5 のベクトル状態}
$$

### Lean のコメント（日本語訳）

> `WithTop ℕ` 上、有限層はC1二主体状態と全可測ゲイン族、頂点はC5ベクトル状態と元のC5 feedbackを持つ層別型。

### 定義の説明

共通束 `WithTop ℕ` の上の、**層ごとの状態の型**です。有限層は C1 の二主体の状態（と、可測な有界ゲインの族）、頂点は C5 のベクトル状態（と元の C5 のフィードバック）を持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6LayeredPolicy"></a>

## 定義 `C6LayeredPolicy`

### 式

$$
\text{有限層}:\ \text{C1 のゲイン信号},\quad\text{頂点}:\ \text{C5 の方策}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの**方策の型**です。有限層はゲイン信号、頂点は C5 のベクトル方策です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredTrajectory"></a>

## 定義 `c6LayeredTrajectory`

### 式

$$
\text{層ごとの軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの軌道です。頂点は C5 のデータの軌道、有限層は C1 の二主体の制御軌道（`controlledConsensusState`）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredRunningCost"></a>

## 定義 `c6LayeredRunningCost`

### 式

$$
\text{層ごとの走行費}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの走行費です。頂点は C5 の走行費、有限層は \(1+8\,(\text{差の半分})^2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredFiniteRunningCost_eq_C1V0"></a>

## 補題 `c6LayeredFiniteRunningCost_eq_C1V0`

### 式

$$
x\in\mathrm{box}\Rightarrow\text{有限層の走行費}=V_0(x)
$$

### Lean のコメント（日本語訳）

> 有限層Dの実走行費は、箱内C1モデルの基礎評価 `V₀` と一致する。正baselineと残差係数を同じ層上で保つS2の保存式。

### 補題の説明

有限層の実際の走行費は、箱の中の C1 モデルの基礎評価 \(V_0\) に一致します。正の基準値（baseline）と残差の係数を、同じ層の上で保つ保存式（S2）です。

### 証明の概略

1. \(V_0=1+\)（中心つき二次ポテンシャル）の式（`c1V0_eq_baseline_add_centeredPotential`）で書き換える。
2. 定義を展開して \(1+8d^2\) と比べる（`simp`）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredFiniteRunningCost_eq_layerPotential"></a>

## 補題 `c6LayeredFiniteRunningCost_eq_layerPotential`

### 式

$$
\text{走行費}=1+16\,P_{\mathrm{rep}(n)}
$$

### Lean のコメント（日本語訳）

> Dの有限添字nに対応する中心 `representation n` で測った再中心化済み二次評価として表す。C2正層kはDの添字k+1に入る。

### 補題の説明

D の有限の添字 \(n\) に対応する中心 \(\mathrm{rep}(n)\) で測った、**再中心化した二次の評価** \(1+16P\) として表します。C2 の正の層 \(k\) は、D の添字 \(k+1\) に入ります。

### 証明の概略

1. 走行費の式 \(1+8d^2\)。\(d=c-q\)（中心 \(c\) からの不一致）なので \(1+16\cdot\tfrac{(q-c)^2}{2}\)。

----

<a id="Tomabechi.Consistency.C6.c6LayeredTrajectory_runningCost_eq_layerPotential"></a>

## 補題 `c6LayeredTrajectory_runningCost_eq_layerPotential`

### 式

$$
\text{流れの上でも、走行費}=\text{同じ層の中心で再中心化した評価}
$$

### Lean のコメント（日本語訳）

> 有限層C1 flow上でも、走行費は同じ層中心で再中心化した評価そのもの。

### 補題の説明

有限層の C1 の流れの上でも、走行費は、同じ層の中心で再中心化した評価そのものです。

### 証明の概略

1. 流れの上の状態は箱に留まる。前の補題を、流れの状態に適用する。

----

<a id="Tomabechi.Consistency.C6.c6LayeredAdmissible"></a>

## 定義 `c6LayeredAdmissible`

### 式

$$
\text{層ごとの許容性}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの許容性です。頂点は C5 のもの、有限層は（全可測有界ゲインが許容）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredOptimalValue"></a>

## 定義 `c6LayeredOptimalValue`

### 式

$$
\text{層ごとの最適値}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適値です。頂点は C5 のもの、有限層は \(1+\tfrac{8d^2}{7}\)（割引した最適値）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredOptimalPolicy"></a>

## 定義 `c6LayeredOptimalPolicy`

### 式

$$
\text{層ごとの最適方策}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適方策です。頂点は C5 のもの、有限層は最大ゲインです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredNonnegativeTimeData"></a>

## 定義 `c6LayeredNonnegativeTimeData`

### 式

$$
\text{共通束上の定理24のデータ}
$$

### Lean のコメント（日本語訳）

> C1全制御族を全有限層へ、C5元データを頂点へ置いた共通束上の定理24データ。有限層と頂点のcontextを層型で保ち、C1下位層を単点Unitへ潰さない。

### 定義の説明

C1 の全制御族を**すべての有限層**へ、C5 の元のデータを**頂点**へ置いた、共通束の上の**定理24のデータ**です。有限層と頂点の文脈を層ごとの型で保ち、C1 の下位層を一点の型 `Unit` に潰しません。割引率は 1 です。

### 証明の概略

1. 各フィールド（軌道・走行費・許容性・最適値・最適方策）に、上の層ごとの定義を入れる。
2. 定理24の条件（正の費用、最適方策の最適性など）は、有限層は割引した最適値の補題（積分・最小性）から、頂点は C5 のデータから。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_rho"></a>

## 補題 `c6LayeredData_rho`

### 式

$$
\rho=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

割引率は 1 です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_all_finite_theorem24"></a>

## 定理 `c6LayeredData_all_finite_theorem24`

### 式

$$
\text{全有限層で、定理24の正費用の結論}
$$

### Lean のコメント（日本語訳）

> この実際の `WithTop ℕ` 層別データから定理24を全有限層で適用する。

### 補題の説明

この実際の `WithTop ℕ` の層ごとのデータから、定理24を、**すべての有限層**で適用して、その結論（正の費用）を得ます。

### 証明の概略

1. 定理24の一般の入口に、`c6LayeredNonnegativeTimeData` を渡す。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_trajectory"></a>

## 補題 `c6LayeredData_top_trajectory`

### 式

$$
\text{頂点の軌道}=\text{C5 の軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点では、層ごとのデータの軌道は C5 のデータの軌道です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_runningCost"></a>

## 補題 `c6LayeredData_top_runningCost`

### 式

$$
\text{頂点の走行費}=\text{C5 の走行費}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の走行費は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_optimalValue"></a>

## 補題 `c6LayeredData_top_optimalValue`

### 式

$$
\text{頂点の最適値}=\text{C5 の最適値}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の最適値は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_admissible"></a>

## 補題 `c6LayeredData_top_admissible`

### 式

$$
\text{頂点の許容性}=\text{C5 の許容性}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の許容性は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_optimalPolicy"></a>

## 補題 `c6LayeredData_top_optimalPolicy`

### 式

$$
\text{頂点の最適方策}=\text{C5 の最適方策}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の最適方策は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_admissible_fun"></a>

## 補題 `c6LayeredData_top_admissible_fun`

### 式

$$
\text{許容性（関数として）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の許容性は、関数として C5 のものに等しいです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredAdmissible_top"></a>

## 補題 `c6LayeredAdmissible_top`

### 式

$$
\text{許容性}(\top)=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`c6LayeredAdmissible` の頂点での値は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredOptimalValue_top"></a>

## 補題 `c6LayeredOptimalValue_top`

### 式

$$
\text{最適値}(\top)=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`c6LayeredOptimalValue` の頂点での値は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_trajectory_fun"></a>

## 補題 `c6LayeredData_top_trajectory_fun`

### 式

$$
\text{軌道（関数として）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の軌道は、関数として C5 のものに等しいです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_runningCost_fun"></a>

## 補題 `c6LayeredData_top_runningCost_fun`

### 式

$$
\text{走行費（関数として）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の走行費は、関数として C5 のものに等しいです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_top_optimalValue_fun"></a>

## 補題 `c6LayeredData_top_optimalValue_fun`

### 式

$$
\text{最適値（関数として）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の最適値は、関数として C5 のものに等しいです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredDynamics"></a>

## 定義 `c6LayeredDynamics`

### 式

$$
\text{定理26の力学（同じ層ごとのデータの上）}
$$

### Lean のコメント（日本語訳）

> 26 の力学は、C1 を豊富に含む同じ共通層の 24 のデータを使う。その頂点への射影は、定義として、既存の C5 の力学の証人である。

### 定義の説明

定理26の力学です。C1 を含む**同じ共通層の定理24のデータ**を使い、その頂点への射影は、定義として、既存の C5 の力学の証人と一致します。

### 証明の概略

1. 政策の同値・フィードバック・生きている集合は C5 のものを使う。
2. 最適性・Lyapunov などの解析的な条件は、層ごとのデータの頂点が C5 のデータに一致することを使って、C5 の証人から移す（`simpa`）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_jointConclusion"></a>

## 定義 `c6LayeredData_jointConclusion`

### 式

$$
\text{有限層の 24-A と頂点の 26 の条件を、同じ記録から取り出す}
$$

### Lean のコメント（日本語訳）

> 新しい共通Dの有限層24-Aと頂点Eの26条件を同じrecordから取り出す。

### 定義の説明

新しい共通データ D の**有限層の条件 24-A** と、**頂点の力学 E の定理26の条件**を、同じ記録から取り出します。

### 証明の概略

1. 定理24→26 の一般の入口（`theorem24_to26_from_nonnegativeTimeData`）を適用する。

----

<a id="Tomabechi.Consistency.C6.commonLayerToC5Abstraction"></a>

## 定義 `commonLayerToC5Abstraction`

### 式

$$
\top\mapsto\text{上位},\quad n\mapsto\text{下位}
$$

### Lean のコメント（日本語訳）

> 共通束の有限層は下位抽象、頂点は上位抽象を表す。

### 定義の説明

共通束の有限層を C5 の「下位の抽象」、頂点を「上位の抽象」に対応させます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonLayerToC5Abstraction_top"></a>

## 補題 `commonLayerToC5Abstraction_top`

### 式

$$
\mathrm{abs}(\top)=\text{上位}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点は上位です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.commonLayerToC5Abstraction_coe"></a>

## 補題 `commonLayerToC5Abstraction_coe`

### 式

$$
\mathrm{abs}(n)=\text{下位}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自然数の層は下位です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.commonLayerToC5Abstraction_eq_false_of_lt_top"></a>

## 補題 `commonLayerToC5Abstraction_eq_false_of_lt_top`

### 式

$$
a<\top\Rightarrow\mathrm{abs}(a)=\text{下位}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂より下の層は、下位です。

### 証明の概略

1. `a` が `none`（頂）か `some`（自然数）かの場合分け。頂だと \(a<\top\) に矛盾。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData"></a>

## 定義 `c6C5PullbackData`

### 式

$$
\text{C5 のデータを層の写像で引き戻した、共通束上の定理24のデータ}
$$

### Lean のコメント（日本語訳）

> C5のデータを層写像で引き戻した共通束上の24データ。全ての有限層で同じ下位費用を使い、頂点ではC5上位の実データを使う。

### 定義の説明

C5 のデータを、層の写像で**引き戻した**、共通束上の定理24のデータです。**すべての有限層で同じ下位の費用**を使い、頂点では C5 の上位の実データを使います（C1 の二主体の層別データとは別の構成）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_top_trajectory"></a>

## 補題 `c6C5PullbackData_top_trajectory`

### 式

$$
\text{頂点の軌道}=\text{C5}
$$

### Lean のコメント（日本語訳）

> 頂点で引き戻したデータはC5上位データそのもの。

### 補題の説明

頂点で引き戻したデータの軌道は、C5 の上位のデータそのものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_top_runningCost"></a>

## 補題 `c6C5PullbackData_top_runningCost`

### 式

$$
\text{頂点の走行費}=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の走行費は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_top_optimalValue"></a>

## 補題 `c6C5PullbackData_top_optimalValue`

### 式

$$
\text{頂点の最適値}=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の最適値は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_top_admissible"></a>

## 補題 `c6C5PullbackData_top_admissible`

### 式

$$
\text{頂点の許容性}=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の許容性は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_top_optimalPolicy"></a>

## 補題 `c6C5PullbackData_top_optimalPolicy`

### 式

$$
\text{頂点の最適方策}=\text{C5}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂点の最適方策は C5 のものです。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_all_finite_theorem24"></a>

## 定理 `c6C5PullbackData_all_finite_theorem24`

### 式

$$
\text{全有限層で、定理24の正費用の結論}
$$

### Lean のコメント（日本語訳）

> 同じ共通束データから、全有限層で定理24の正費用結論を得る。

### 補題の説明

同じ共通束のデータから、すべての有限層で、定理24の正費用の結論を得ます。

### 証明の概略

1. 定理24の一般の入口に、引き戻したデータを渡す。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackDynamics"></a>

## 定義 `c6C5PullbackDynamics`

### 式

$$
\text{引き戻したデータの上の定理26の力学}
$$

### Lean のコメント（日本語訳）

> 頂点の26力学も、上で定義した同じ層別Dの最上位射影を使う。解析条件は既存C5証人から輸送し、Dの費用・軌道・値との同定を明示する。

### 定義の説明

頂点の定理26の力学も、上で定義した**同じ層ごとのデータ D の最上位への射影**を使います。解析的な条件は、既存の C5 の証人から輸送し、D の費用・軌道・値との同定を明示します。

### 証明の概略

1. 政策の同値・フィードバック・生きている集合は C5 のもの。
2. 各条件は、頂点でのデータが C5 のものに一致する補題（`c6C5PullbackData_top_*`）で、C5 の証人から移す。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_jointConclusion"></a>

## 定義 `c6C5PullbackData_jointConclusion`

### 式

$$
\text{24→26 の実入口を、有限層の 24-A と頂点の E に適用}
$$

### Lean のコメント（日本語訳）

> 24→26の実入口を、有限層の条件24-Aと同じ層別Dの頂点Eへ適用する。

### 定義の説明

定理24→26 の実際の入口を、有限層の条件 24-A と、同じ層ごとのデータの頂点 E に適用します。

### 証明の概略

1. 定理24→26 の一般の入口に、引き戻したデータと力学を渡す。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackTheorem27Conclusion"></a>

## 定義 `c6C5PullbackTheorem27Conclusion`

### 式

$$
\text{定理27の結論の形}
$$

### Lean のコメント（日本語訳）

> 頂点のC6モデルが使う同じ状態・方策・費用を指定した27-A/27.6/27.7–27.10の出力形。参照入力は元のベクトル例の入力で、状態は共通D/Eのtrajectoryである。

### 定義の説明

頂点の C6 モデルが使う**同じ状態・方策・費用**を指定した、定理27の 27-A・27.6・27.7〜27.10 の**出力の形**です。基準入力は元のベクトルの例の入力で、状態は共通データ D・力学 E の軌道です。内容は、操作的な無明（PZS でないこと）と、残差の下降・作動量の下界の同値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C5PullbackData_theorem27_kernel"></a>

## 定理 `c6C5PullbackData_theorem27_kernel`

### 式

$$
\text{定理27の結論（引き戻したデータで）}
$$

### Lean のコメント（日本語訳）

> 既存の27-A実入力・基準入力証明を、共通束データの頂点projectionへ移す。sourceとC6のtrajectory/cost/value/admissibilityを同定して結論を移送する。

### 補題の説明

既存の 27-A の実入力・基準入力の証明を、共通束のデータの頂点への射影に移します。元の C5 と C6 の、軌道・費用・価値・許容性を同定して、結論を移送します。

### 証明の概略

1. 結論の形を展開し、頂点での各データが C5 のものに一致する補題で書き換える（`simpa`）。
2. C5 の既存の結論（`vectorSourceData_theorem27_kernel`）を適用する。

----

<a id="Tomabechi.Consistency.C6.c6LayeredTheorem27Conclusion"></a>

## 定義 `c6LayeredTheorem27Conclusion`

### 式

$$
\text{定理27の結論（層ごとの共通データの頂点で）}
$$

### Lean のコメント（日本語訳）

> 同一の27結論を、有限層C1状態を持つ新しい共通Dの頂点で記述する。

### 定義の説明

**同じ定理27の結論**を、有限層に C1 の状態を持つ、新しい共通データ D の頂点で述べたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayeredData_theorem27_kernel"></a>

## 定理 `c6LayeredData_theorem27_kernel`

### 式

$$
\text{定理27の結論（層ごとの共通データで）}
$$

### Lean のコメント（日本語訳）

> 27の運用出力を、同じ新L上24/26データの頂点projectionへ適用する。

### 補題の説明

定理27の運用の出力を、同じ新しい層ごとの 24・26 のデータの頂点への射影に適用します。

### 証明の概略

1. 結論の形を展開し、層ごとのデータの頂点での値が C5 のものに一致する補題で書き換える。
2. C5 の定理27の結論（前の定理）を適用する。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerData"></a>

## 定義 `c6CommonLayerData`

### 式

$$
=c6LayeredNonnegativeTimeData
$$

### Lean のコメント（日本語訳）

> 現行C6の標準共通D。有限層はC1状態を持つ層別データを指す。

### 定義の説明

現在の C6 の**標準の共通データ D** です。有限層は C1 の状態を持つ層ごとのデータを指します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerDynamics"></a>

## 定義 `c6CommonLayerDynamics`

### 式

$$
=c6LayeredDynamics
$$

### Lean のコメント（日本語訳）

> 標準共通Dの頂点力学。

### 定義の説明

標準の共通データの頂点の力学です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerData_all_finite_theorem24"></a>

## 定義 `c6CommonLayerData_all_finite_theorem24`

### 式

$$
=c6LayeredData_all_finite_theorem24
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

標準の共通データについての、全有限層の定理24の結論です（別名）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerData_jointConclusion"></a>

## 定義 `c6CommonLayerData_jointConclusion`

### 式

$$
=c6LayeredData_jointConclusion
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

標準の共通データについての、24-A と 26 の条件の取り出しです（別名）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonLayerData_theorem27_kernel"></a>

## 定理 `c6CommonLayerData_theorem27_kernel`

### 式

$$
=c6LayeredData_theorem27_kernel
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

標準の共通データについての、定理27の結論です。

### 証明の概略

1. 層ごとの共通データについての定理（前の定理）。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
