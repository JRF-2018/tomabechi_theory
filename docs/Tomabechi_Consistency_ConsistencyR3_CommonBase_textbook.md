# Tomabechi/Consistency/ConsistencyR3_CommonBase.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR3_CommonBase.lean`](../Tomabechi/Consistency/ConsistencyR3_CommonBase.lean)（定理1・4・20 で共有する基礎評価と、そこから作る定理4・20 の候補）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文は、定理1・4・20 で**同じ基礎評価 \(V_0\)** を使うように読めますが、以前の既存の入口は、定理ごとに別の評価を使っていました。このファイルは、既存の入口を勝手に同一視せず、**一つの共有基礎評価 \(V_0=1+\Phi_2\)** から、定理1・4・20 の候補を**別名で**作り直し、それらが整合することを式で証明します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通基礎評価」（R3）の出発点です。

| 定理 | 共有評価から作った量 |
| --- | --- |
| 定理1 | 箱の中で、既存の評価 \(1+\Phi_2\) と一致 |
| 定理4 | 実効評価 \(1+F-e^{-F}\)（\(F=\Phi_2\)）。\(F\le\cdot\le2F\)。零点は \(F=0\)。率 3 の流れで減衰。最大ゲインが最小化（argmin） |
| 定理20 | 実効評価 \(1+3D\)（\(D=(x_0-x_1)^2\)）。最小値からの差は Euclid 象徴距離のちょうど 12 倍。率 3 の流れで正確に率 6 で減衰。最大ゲインが最小化 |

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、既存の定理4・20 の入口へこの候補を接続する**最適性・微分条件は別途必要**です。
* 評価の同一性は**箱の中**での話です（箱の外では異なる）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> このファイルでは、既存入口を勝手に同一視せず、共通基礎評価を持つ再設計候補を別名で定義する。箱内では定理1の評価と一致し、定理4・20の実効評価がどのように得られるかを式として証明する。既存の定理4/20の入口へこの候補を接続する最適性・微分条件は別途必要である。

---

<a id="Tomabechi.Consistency.R3.commonBaseV0"></a>

## 定義 `commonBaseV0`

### 式

$$
V_0(x)=1+\Phi_2(x,0)
$$

### Lean のコメント（日本語訳）

> 1・4・20で共有する正の基礎評価。

### 定義の説明

定理1・4・20 で**共有する**、正の基礎評価関数です。基準値 1 に、定理2の共有残差を足したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBasePresenceP"></a>

## 定義 `commonBasePresenceP`

### 式

$$
P(x)=\exp\bigl(-\Phi_2(x,0)\bigr)
$$

### Lean のコメント（日本語訳）

> 定理4候補の非定数臨場感 `P=exp(-F)`。

### 定義の説明

定理4の候補となる臨場感です。\(P=e^{-F}\)（\(F=\Phi_2\)）。定数でなく、状態で変わります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBasePresenceQ"></a>

## 定義 `commonBasePresenceQ`

### 式

$$
Q\equiv1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

第二の臨場感 \(Q\) は定数 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4Effective"></a>

## 定義 `commonBaseTheorem4Effective`

### 式

$$
V_0-\kappa PQ=1+F-e^{-F}
$$

### Lean のコメント（日本語訳）

> 定理4候補の実効評価 `1+F-exp(-F)`。

### 定義の説明

定理4の実効評価（\(\kappa=1\)）です。共有の基礎評価から臨場感を引いたもの \(1+F-e^{-F}\) になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseD"></a>

## 定義 `commonBaseD`

### 式

$$
D(x)=(x_0-x_1)^2
$$

### Lean のコメント（日本語訳）

> 定理20の距離二乗 `D=(x₀-x₁)²`。

### 定義の説明

二人の食い違いの二乗です（定理20の距離の二乗）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseSlope"></a>

## 定義 `commonBaseSlope`

### 式

$$
s(D)=-D
$$

### Lean のコメント（日本語訳）

> 定理20候補の傾き `s(D)=-D`。

### 定義の説明

定理20の傾き関数 \(s(D)=-D\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20Effective"></a>

## 定義 `commonBaseTheorem20Effective`

### 式

$$
V_0-1\cdot1\cdot s(D)
$$

### Lean のコメント（日本語訳）

> 定理20候補の正baselineつき実効評価。

### 定義の説明

定理20の実効評価です。共有の基礎評価から、傾きを引いたものです。基準値が正（\(V_0\ge1\)）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseV0_eq_theorem1_on_box"></a>

## 補題 `commonBaseV0_eq_theorem1_on_box`

### 式

$$
x\in\mathrm{box}\Rightarrow V_0^{\text{共有}}=V_0^{\text{定理1}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、共有の基礎評価は、定理1の基礎評価と一致します。

### 証明の概略

1. どちらも \(1+\Phi_2(x,0)\)。定義を展開する。

----

<a id="Tomabechi.Consistency.R3.commonBaseV0_eq_theorem20_candidate_on_box"></a>

## 補題 `commonBaseV0_eq_theorem20_candidate_on_box`

### 式

$$
x\in\mathrm{box}\Rightarrow V_0(x)=1+2D(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、共有の基礎評価は \(1+2D\) です。

### 証明の概略

1. 箱の上の共有残差 \(2(x_0-x_1)^2\)（`sharedPotential_eq_coupling`）を代入する。

----

<a id="Tomabechi.Consistency.R3.commonBaseV0_positive"></a>

## 補題 `commonBaseV0_positive`

### 式

$$
V_0>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有の基礎評価は正です。

### 証明の概略

1. 共有残差は非負（`consensusPresence_potential_nonneg`）なので \(1+\Phi_2>0\)。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4Effective_formula"></a>

## 補題 `commonBaseTheorem4Effective_formula`

### 式

$$
V_{\text{eff}}=1+F-e^{-F}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の実効評価の具体形です。

### 証明の概略

1. 定義を展開し、\(Q=1\) で整理する（`simp`）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4Effective_monotone"></a>

## 補題 `commonBaseTheorem4Effective_monotone`

### 式

$$
a\le b\Rightarrow 1+a-e^{-a}\le1+b-e^{-b}
$$

### Lean のコメント（日本語訳）

> 共通基礎評価の定理4の実効値は、もとの非負の残差 `F` について増加する。argmin を移すのに必要なスカラーの比較である。

### 補題の説明

共有の基礎評価で作った定理4の実効評価は、もとの非負の残差 \(F\) について増加します。argmin（最小化）を移すために必要な、スカラーの比較です。

### 証明の概略

1. \(e^{-b}\le e^{-a}\)（\(a\le b\)、`exp_le_exp`）。一次不等式で結ぶ。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4_bounds"></a>

## 補題 `commonBaseTheorem4_bounds`

### 式

$$
F\le V_{\text{eff}}\le2F
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の実効評価は、\(F\) 以上 \(2F\) 以下です。

### 証明の概略

1. \(F\ge0\)。\(e^{-F}\le1\) から \(V_{\text{eff}}\ge F\)。\(1-F\le e^{-F}\)（`add_one_le_exp`）から上の評価。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4_zero_iff"></a>

## 補題 `commonBaseTheorem4_zero_iff`

### 式

$$
V_{\text{eff}}=0\iff F=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効評価が 0 であることと、共有残差 \(F\) が 0 であることは同値です。

### 証明の概略

1. （→）\(F\le V_{\text{eff}}=0\) と \(F\ge0\)。
2. （←）\(F=0\) なら \(1+0-e^{0}=0\)。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4_weightedTCZ_eq_shared"></a>

## 補題 `commonBaseTheorem4_weightedTCZ_eq_shared`

### 式

$$
\mathrm{weightedTCZ}_{\theta=0}=\mathrm{sharedTCZ}
$$

### Lean のコメント（日本語訳）

> 共有基礎評価の定理4の候補の、閾値 0 の TCZ は、共通の到達の箱の内側では、既存の共有の零残差の目標にちょうど等しい。

### 補題の説明

共有の基礎評価の定理4の候補の、閾値 0 の TCZ は、共通の到達の箱の中で、既存の共有 TCZ（共有残差が 0 の目標）にちょうど一致します。

### 証明の概略

1. 実効評価 \(\le0\) と、共有残差 \(=0\) が同値であることを示す（前の補題。非負性と合わせる）。
2. 箱の条件は同じ。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4_rate3_dissipation_rhs_bound"></a>

## 補題 `commonBaseTheorem4_rate3_dissipation_rhs_bound`

### 式

$$
-6F(1+e^{-F})\le-3V_{\text{eff}}
$$

### Lean のコメント（日本語訳）

> rate-3流に連鎖律を適用したときの候補散逸右辺を支える代数的不等式。

### 補題の説明

率 3 の流れに連鎖律を使ったときの、散逸の右辺を支える**代数的な不等式**です。

### 証明の概略

1. \(F\ge0\)。実効評価の上界 \(V_{\text{eff}}\le2F\)（前の補題）と、\(1+e^{-F}\ge1\) などから示す。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4Effective_rate3_decay"></a>

## 補題 `commonBaseTheorem4Effective_rate3_decay`

### 式

$$
V_{\text{eff}}(x(s),s)\le2\,V_{\text{eff}}(x_0,t_0)\,e^{-6(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 共通基礎評価から作った定理4候補は、C1 rate-3流上で定量的に減衰する。

### 補題の説明

共有の基礎評価から作った定理4の実効評価は、率 3 の流れの上で、定量的に（\(e^{-6(s-t_0)}\) で）減衰します。

### 証明の概略

1. 流れは箱に留まる。流れの上の共有残差は \(F(s)=F_0\,e^{-6(s-t_0)}\)。
2. 実効評価の評価 \(F\le V_{\text{eff}}\le2F\)（前の補題）を使って、\(V_{\text{eff}}(s)\le2F(s)\le2F_0e^{-6(s-t_0)}\le2V_{\text{eff}}(0)e^{-6(s-t_0)}\)。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4FiniteHorizonCost"></a>

## 定義 `commonBaseTheorem4FiniteHorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}V_{\text{eff}}(\text{state}(s))\,ds
$$

### Lean のコメント（日本語訳）

> 共有基礎評価の定理4の候補から作った有限地平の費用。

### 定義の説明

共有の基礎評価の定理4の候補から作った、有限地平の費用です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem4_maxGain_argmin"></a>

## 補題 `commonBaseTheorem4_maxGain_argmin`

### 式

$$
J_4(u_{\max})\le J_4(u)\quad(\forall u)
$$

### Lean のコメント（日本語訳）

> 最大ゲインは、新しい共有基礎評価の定理4の費用を、正のどの有限地平でも、可測な許容ゲインのすべてに対して最小にする。

### 補題の説明

最大ゲインは、この新しい定理4の費用を、すべての可測な許容ゲインに対して、正のすべての有限地平で最小にします。

### 証明の概略

1. 最大ゲインの差の二乗は他の制御以下（`c1MaxGain_orbit_sq_le`）。
2. 実効評価は共有残差 \(F\) の単調増加関数（`commonBaseTheorem4Effective_monotone`）で、箱の上では \(F\) が差の二乗の定数倍。
3. 点ごとの不等式を、積分に持ち上げる（`lintegral_mono_ae`）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20Effective_formula"></a>

## 補題 `commonBaseTheorem20Effective_formula`

### 式

$$
x\in\mathrm{box}\Rightarrow V_{\text{eff}}^{20}=1+3D
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、定理20の実効評価は \(1+3D\) です。

### 証明の概略

1. 共有の基礎評価 \(1+2D\)（前の補題）に、傾きの項 \(-s(D)=D\) を足す。

----

<a id="Tomabechi.Consistency.R3.commonBaseD_eq_halfDifference_sq"></a>

## 補題 `commonBaseD_eq_halfDifference_sq`

### 式

$$
D=4d^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

食い違いの二乗は、差の半分の二乗の 4 倍です。

### 証明の概略

1. 定義を展開して整理する（`ring`）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20FiniteHorizonCost"></a>

## 定義 `commonBaseTheorem20FiniteHorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}V_{\text{eff}}^{20}(\text{state}(s))\,ds
$$

### Lean のコメント（日本語訳）

> 共有基礎評価の定理20の候補の実効値を、任意の許容な二主体ゲイン信号に沿って積分して得る有限地平の費用。

### 定義の説明

共有の基礎評価の定理20の候補の実効評価を、二主体の任意の許容ゲインに沿って積分した、有限地平の費用です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20_maxGain_argmin"></a>

## 補題 `commonBaseTheorem20_maxGain_argmin`

### 式

$$
J_{20}(u_{\max})\le J_{20}(u)\quad(\forall u)
$$

### Lean のコメント（日本語訳）

> 同じ最大ゲインが、新しい定理20の候補の費用を、正のどの有限地平でも最小にする。候補は不一致の二乗の増加するアフィン関数で、率3のフィードバックが各点で最小にする。

### 補題の説明

同じ最大ゲインが、新しい定理20の費用も、正のすべての有限地平で最小にします。候補の実効評価は、食い違いの二乗の増加するアフィン関数で、率 3 のフィードバックが各時刻で最小にします。

### 証明の概略

1. 最大ゲインの差の二乗は他の制御以下。
2. 実効評価は \(1+3D\)（\(D\) の増加アフィン関数）なので、各時刻の大小は \(D\) の大小で決まる。
3. 積分に持ち上げる。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20_minimum_shift"></a>

## 補題 `commonBaseTheorem20_minimum_shift`

### 式

$$
V_{\text{eff}}^{20}-1=3D
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最小値（1）からの差は \(3D\) です。

### 証明の概略

1. 前の補題の式を移項する。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20_excess_eq_euclidean_distance"></a>

## 補題 `commonBaseTheorem20_excess_eq_euclidean_distance`

### 式

$$
V_{\text{eff}}^{20}-1=12\,D_{\text{Euclid}}
$$

### Lean のコメント（日本語訳）

> 定理20の共有候補の（最小値からの）超過は、移した Euclid 象徴距離のちょうど12倍である。これで、候補の零点集合と定量的な尺度が、既存の Euclid 入口で使う距離と同一視される。

### 補題の説明

定理20の共有候補の、最小値からの差は、Euclid 座標へ移した象徴の距離の**ちょうど 12 倍**です。これで、候補の零点集合と定量的な尺度が、既存の Euclid 入口で使う距離と同一視されます。

### 証明の概略

1. 差は \(3D=3\cdot(x_0-x_1)^2\)。象徴の距離は \(\tfrac14(x_0-x_1)^2\)（座標移送、`c1EuclideanSymbolDistance_eq_coordinates`）。比は 12。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20_minimum_sublevel_iff_symbol_target"></a>

## 補題 `commonBaseTheorem20_minimum_sublevel_iff_symbol_target`

### 式

$$
V_{\text{eff}}^{20}-1\le0\iff x\in\mathrm{Tgt}
$$

### Lean のコメント（日本語訳）

> 不変な箱の内側では、候補の最小値での部分準位集合は、定理20の、移した象徴の合意の目標にちょうど等しい。

### 補題の説明

不変な箱の中では、候補の最小値での部分準位集合は、定理20の（Euclid 座標へ移した）象徴の合意の目標集合にちょうど一致します。

### 証明の概略

1. 差は象徴の距離の 12 倍（前の補題）。距離は非負。
2. \(\le0\) は距離 \(=0\) と同値で、それは目標集合に入ること（`c1EuclideanSymbolDistance_zero_iff`）。

----

<a id="Tomabechi.Consistency.R3.commonBaseTheorem20Effective_excess_rate3_decay"></a>

## 補題 `commonBaseTheorem20Effective_excess_rate3_decay`

### 式

$$
V_{\text{eff}}^{20}(x(s))-1=\bigl(V_{\text{eff}}^{20}(x_0)-1\bigr)e^{-6(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 定理20候補の実効評価は、rate-3流上で最小値からの差が正確に率6で減衰する。

### 補題の説明

定理20の候補の実効評価は、率 3 の流れの上で、最小値からの差が**正確に**率 6 で減衰します（等式）。

### 証明の概略

1. 流れは箱に留まる。両側を \(1+3D\) の形に直す。
2. 流れの上で \(D(s)=D_0\,e^{-6(s-t_0)}\)。

----

<a id="Tomabechi.Consistency.R3.C1CommonBaseContract"></a>

## 構造体 `C1CommonBaseContract`

### 式

$$
V_0=V_0^{\text{共有}},\ \text{定理1・4・20 との整合}
$$

### Lean のコメント（日本語訳）

> 新しい共有評価の代数的契約。これは原文条件の追加証明ではなく、1/4/20入口へ接続する候補データの束である。

### 定義の説明

新しい共有評価の**代数的な契約**です。原文の条件を追加で証明するものではなく、定理1・4・20 の入口へつなぐ候補のデータを束ねたものです。フィールドは、`V0`（評価関数）、`V0_eq_shared`（共有評価に等しい）、`theorem1_matches`（箱の中で定理1の評価に一致）、`theorem4_effective`（実効評価が定理4の式に一致）、`theorem20_box_value`（箱の中で \(1+2D\)）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.commonBaseContract"></a>

## 定義 `commonBaseContract`

### 式

$$
\text{共有評価の契約}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有評価 `commonBaseV0` を使った契約の値です。各フィールドは前の補題で与えます。

### 証明の概略

1. `V0_eq_shared`・`theorem4_effective` は定義から（`rfl`）。`theorem1_matches`・`theorem20_box_value` は前の補題。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
