# Theorem4.lean 解説

> 対象: [`Theorem4.lean`](../Theorem4.lean)（定理4：苫米地臨場感加重）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理4（**苫米地臨場感加重**）：臨場感 \(P\in[0,1]\) と価値符号 \(Q\in[-1,1]\) による**実効ポテンシャル**

$$\tilde V=V_0-\kappa\,P\,Q$$

を定義し、その閾値 \(\theta_P\) を超える部分（**正部分** \([\tilde V-\theta_P]_+\)）を残差とする**臨場感加重 TCZ** への、**条件付きの指数収束**を示します。臨場感が高く（\(P\) 大）価値が正（\(Q>0\)）なら、実効ポテンシャルが下がり、そこが「谷」になります。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 実効ポテンシャルと残差 | `effectivePotential`, `residual4`, `effectivePotential_lower_bound` |
| 臨場感加重 TCZ | `weightedTCZ` |
| 収束 | `weighted_tcz_exponential_decay`, `weighted_tcz_distance_tendsto_zero`, `weighted_reachable_tcz_distance_tendsto_zero` |
| 臨場感の効果 | `effectivePotential_hasDerivAt_P`, `effectivePotential_P_monotonicity` |

### 0.3 このファイルが証明していないこと

- **下降条件（実効残差の指数散逸）と距離の誤差境界**は、制御系から導出せず、原文の**補題0の条件**として**入力**します。反復ホライズン最適性だけからこれらが出るとは主張しません。
- 収束先は**臨場感加重 TCZ**（実効ポテンシャル \(\tilde V\) の閾値集合）で、基礎ポテンシャル \(V_0\) の TCZ とは**異なります**。
- 臨場感 \(P\)・価値符号 \(Q\) の力学そのものは扱いません（状態・時刻の関数として与えられる）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理4：苫米地臨場感加重**
>
> 臨場感 `P` と価値符号 `Q` による実効ポテンシャル \(V_0-\kappa PQ\) を定義し、その正部分の残差をもつ、臨場感加重の TCZ のスライスへの、条件付きの指数収束を示す。下降条件・距離の誤差境界は、制御系から導出せず、原文の補題 0 の条件として入力する。

名前空間は `Tomabechi.Theorem4`。`open MeasureTheory`、`open Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem4.effectivePotential"></a>

## 定義 `effectivePotential`

### 式

$$\tilde V=V_0-\kappa PQ$$

### Lean のコメント（日本語訳）

> 原文の、臨場感で加重された実効ポテンシャル \(\tilde V=V_0-\kappa PQ\)。

### 定義の説明

基礎ポテンシャル \(V_0\) から、臨場感 \(P\)・価値符号 \(Q\) の積（強さ \(\kappa\)）を引いたものです。\(PQ>0\) の状態は実効ポテンシャルが低く、望ましい（谷）。

### 証明の概略

1. 定義：`V₀ - κ * P * Q`。

----

<a id="Tomabechi.Theorem4.residual4"></a>

## 定義 `residual4`

### 式

$$[\tilde V-\theta_P]_+=\max(\tilde V-\theta_P,0)$$

### Lean のコメント（日本語訳）

> 定理4の零の残差 \([\tilde V-\theta_P]_+\)。

### 定義の説明

実効ポテンシャルが閾値 \(\theta_P\) を超えた分（超えなければ 0）です。

### 証明の概略

1. 定義：`Tomabechi.Theorem1.residual1 (effectivePotential ..) θP`。

----

<a id="Tomabechi.Theorem4.effectivePotential_lower_bound"></a>

## 補題 `effectivePotential_lower_bound`

### 式

$$V_0\ge0,\ P\in[0,1],\ Q\in[-1,1],\ \kappa>0\ \Longrightarrow\ \tilde V\ge-\kappa$$

### Lean のコメント（日本語訳）

> \(V_0\ge0\)、\(P\in[0,1]\)、\(Q\in[-1,1]\)、\(\kappa>0\) なら、原文の下限 \(\tilde V\ge-\kappa\) が成り立つ。

### 補題の説明

実効ポテンシャルは \(-\kappa\) より下がりません（\(PQ\le1\)）。

### 証明の概略

1. \(\kappa PQ\le\kappa\)（\(0\le P\le1\)、\(Q\le1\)、`nlinarith`）。

----

<a id="Tomabechi.Theorem4.weightedTCZ"></a>

## 定義 `weightedTCZ`

### 式

$$\Omega_P(t)=\{x\in K\mid\tilde V(x,t)\le\theta_P\}$$

### Lean のコメント（日本語訳）

> 原文の \(\Omega_P(t)=\{x\in K\mid\tilde V(x,t)\le\theta_P\}\)。基礎の \(V_0\) の TCZ とは異なる。

### 定義の説明

臨場感加重の目標領域（実効ポテンシャルが閾値以下の点の集合）です。

### 証明の概略

1. 定義：`{x ∈ K | effectivePotential (V₀ x t) (P x t) (Q x t) κ ≤ θP}`。

----

<a id="Tomabechi.Theorem4.weighted_tcz_exponential_decay"></a>

## 定理 `weighted_tcz_exponential_decay`

### 式

$$\begin{aligned}
&r_4=\Phi_4(V_0,P,Q;\kappa,\theta_P):\ \text{AC},\ \ r_4'\le-2c\,r_4\ \text{a.e.},\ \ \mathrm{dist}(x(s),\Omega_P(s))^2\le C\,r_4,\ \ \Omega_P(s)\ne\emptyset\quad(s\in[t_0,t])\\
&\Longrightarrow\ \ \mathrm{dist}(x(t),\Omega_P(t))\le\sqrt{C\,r_4(t_0)}\,e^{-c(t-t_0)}
\end{aligned}$$
（\(\Omega_P=\)臨場感加重 TCZ `weightedTCZ`。条件付き結論。）

### Lean のコメント（日本語訳）

> 定理4の条件付きの定量的な結論。実効残差の絶対連続性、指数散逸、臨場感加重 TCZ のスライスへの誤差境界を仮定し、距離の指数の評価を得る。反復ホライズンの最適性だけから、これらの条件が出るとは主張しない。

### 補題の説明

**定理4の主結論**：実効残差が（絶対連続で）指数散逸し、距離の 2 乗が残差の定数倍で抑えられるなら、臨場感加重 TCZ への距離が指数的に減ります。

### 証明の概略

1. 定理1の `individual_tcz_distance_decay_of_ac_ae_derivative`（AC・a.e. 下降・誤差境界から距離の指数評価）を、残差 \(r_4=\)`residual4`（正部分の形）と臨場感加重 TCZ `weightedTCZ` に対して適用する（残差 \(\ge0\) は `residual1` の定義から）（34 行）。

----

<a id="Tomabechi.Theorem4.weighted_tcz_distance_tendsto_zero"></a>

## 定理 `weighted_tcz_distance_tendsto_zero`

### 式

$$\operatorname{dist}(x(t),\Omega_P(t))\to0$$

### Lean のコメント（日本語訳）

> 区間ごとの、定理4の指数の距離の評価を、全ての有限の終端時刻へ適用し、臨場感加重 TCZ への距離の極限も得る。各有限区間の、残差の正則性・下降・距離の誤差を要求し、定理4の定量的な結論から、そのまま極限へ進む。

### 補題の説明

`t → ∞` での収束版です。

### 証明の概略

1. 各終端時刻 \(T\) で `weighted_tcz_exponential_decay` を適用して、距離が \(\sqrt{Cr_4(t_0)}e^{-c(t-t_0)}\) で抑えられる。
2. 指数関数で抑えられた量は 0 に収束する（定理1の `tendsto_zero_of_exponential_majorant`）（44 行）。

----

<a id="Tomabechi.Theorem4.weighted_reachable_tcz_distance_tendsto_zero"></a>

## 定理 `weighted_reachable_tcz_distance_tendsto_zero`

### 式

$$\Omega_P\ \text{を閉到達集合}\ \overline{\bigcup\text{reachableAt}}\ \text{内で作る}\ \Longrightarrow\ \text{指数評価・極限}$$

### Lean のコメント（日本語訳）

> 選択された方策の、時刻ごとの到達の集合から構成した、閉の到達の閉包をもつ、定理4。方策の力学が、到達集合の証人を供給し、下降と、加重の誤差境界は、明示的な入力のままで、有限ホライズンの最適性から推論しない。
> 日本語の要約：閉到達集合の中の加重 TCZ の非空性から、指数の距離の評価と極限を得る。同じ時刻の実到達点が閾値以下になることは要求しない。

### 補題の説明

定理1の `closedLoopReachableSet` を領域 \(K\) にした版です。

### 証明の概略

1. `closedLoopReachableSet`（Theorem1）を \(K\) として、上の定理を適用。

----

<a id="Tomabechi.Theorem4.effectivePotential_hasDerivAt_P"></a>

## 補題 `effectivePotential_hasDerivAt_P`

### 式

$$\frac{\partial\tilde V}{\partial P}=-\kappa Q$$

### Lean のコメント（日本語訳）

> \(Q\) を固定した \(P\) の偏微分。\(P\) と \(Q\) が同時に変化する経路の全微分とは区別する。

### 補題の説明

臨場感 \(P\) を上げたときの実効ポテンシャルの変化率は \(-\kappa Q\)（\(Q>0\) なら下がる）。

### 証明の概略

1. `HasDerivAt.sub`、`hasDerivAt_const`、`hasDerivAt_id`（1 次式の微分）。

----

<a id="Tomabechi.Theorem4.effectivePotential_P_monotonicity"></a>

## 補題 `effectivePotential_P_monotonicity`

### 式

$$P_1\le P_2:\ \ Q\ge0\Rightarrow\tilde V(P_2)\le\tilde V(P_1),\ \ \ Q\le0\Rightarrow\tilde V(P_1)\le\tilde V(P_2)$$

### Lean のコメント（日本語訳）

> \(Q\) の符号ごとの臨場感の効果。

### 補題の説明

**臨場感の効果**：価値が正（\(Q\ge0\)）なら臨場感を上げると実効ポテンシャルが下がる（谷が深まる）、価値が負（\(Q\le0\)）なら上がる。

### 証明の概略

1. \(\kappa(P_2-P_1)Q\ge0\)（\(Q\ge0\)）または \(\le0\)（`nlinarith`）。

----


## コメント修正記録

（なし）
