# Tomabechi/Examples/Theorem2_SubgradientFlow.lean 解説

> 対象: [`Tomabechi/Examples/Theorem2_SubgradientFlow.lean`](../Tomabechi/Examples/Theorem2_SubgradientFlow.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
| Euler 法 | 微分方程式 \(\dot x=F(x)\) を、小さな刻み \(h\) で \(x_{k+1}=x_k+hF(x_k)\) と更新して近似する数値解法。このプロジェクトの Python 例が使う。Lean が証明するのは刻み 0 の極限（連続時間）の側。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理2（共有 TCZ への収束）の Python 例 `examples/theorem02_shared_tcz.py` のケース A は、共有残差 \(\Phi_2\) の**劣勾配（下り坂の向き）に沿って動く**更新則 \(\dot x\in-20\,\partial\Phi_2(x)\) を、小さな刻みで繰り返し適用する Euler 法で動かしています。このファイルは、その**連続時間版**（刻みを 0 に近づけた極限の流れ）を、Python と同じ初期値 \((2,-2)\)・ゲイン 20 のまま、**具体的な式**で書き下し、次を証明します。

1. その軌道は絶対連続で、\(\Phi_2\) の値は閾値の切替時刻 \(\tau\) を除いて \(\Phi'\le-2\Phi\) を満たす。
2. 軌道は、選んだ劣勾配 `residualGrad` に対する流れの方程式 \(\dot x_i=-20\,g_i(x)\) を、切替時刻を除いて満たす。
3. `residualGrad` は本当に \(\Phi_2\) の凸劣勾配である（支持不等式）。
4. 以上から、既存の一般定理 `theorem2_state_pair_conditional_conclusion`（`Theorem2.lean`）の全前提が満たされ、定理2の**速さつきの結論**（TCZ への距離の指数減衰、個人残差・不整合の指数減衰、到達点での表象の一致）が得られる。

軌道は 2 主体で対称（\(x_0=y,\ x_1=-y\)）です。

$$y(t)=2e^{-(160t+40\min(t,\tau))},\qquad \tau=\tfrac1{200}\log\tfrac{2}{r},\quad r=\sqrt\theta=\sqrt{1/10}.$$

- \(t\le\tau\)（\(|y|>r\)：hinge が働く間）：\(y=2e^{-200t}\)、減衰率 200。
- \(t\ge\tau\)（\(|y|\le r\)：hinge が 0 になった後）：\(y=r\,e^{-160(t-\tau)}\)、減衰率 160（不整合項だけが残る）。

共有残差は \(\Phi(t)=2\max(y^2-\theta,0)+8y^2\)（hinge が 2 本、不整合 \(\gamma(x_0-x_1)^2=2(2y)^2=8y^2\)）です。

依存する上流：`Tomabechi/Examples/Theorem2_SharedTCZ.lean`（系 `DA`、初期値 `x0`、`caseA_error_bound`、`sharedTCZ_nonempty`、`connectedA`、`potential_eq`）と `Theorem2.lean`。

### 0.2 このファイルが証明していないこと

- **Python の Euler 離散列そのもの**の挙動（刻み誤差、数値出力、図の近似値）は証明していません。証明したのは連続時間の流れです。
- 軌道は「**選んだ**劣勾配」に対する流れです。一般の劣微分包含 \(\dot x\in-20\,\partial\Phi_2(x)\) の解の存在・一意性は扱いません（具体解を書き下して、その性質を示しています）。
- 劣微分は切替時刻 \(\tau\) の 1 点で不連続なので、流れの方程式は \(\tau\) を除くほとんど至る所（a.e.）で示しています。
- ケース B（谷が遠い）と、定理2の一般の前提を満たさない場合は扱いません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理2の共有残差に対する実際の劣勾配流
>
> Python 例のケース A で使う初期値 \((2,-2)\) とゲイン 20 を保ち、共有残差 \(\Phi_2\) の選択劣勾配流を解析式で定義する。選んだ劣勾配との a.e. 流れ方程式、軌道上の指数減衰、既存の定理2の定量結論への接続を証明する。

### 0.4 その他の宣言

`set_option maxHeartbeats 2000000` は、重い `nlinarith`・`fun_prop` の計算予算を増やす設定です。名前空間は `Tomabechi.Examples.Theorem2SubgradientFlow`（`open Tomabechi.Examples.Theorem2`、`Tomabechi.Theorem2`、`MeasureTheory`、`Filter`）。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.r"></a>

## 定義 `r`

### 式

$$r=\sqrt\theta=\sqrt{1/10}$$

### Lean のコメント（日本語訳）

> hinge 項の閾値での正の平方根。

### 定義の説明

個人残差 \([x^2-\theta]_+\) が 0 になる境目の座標 \(|x|=r\)。軌道の切替時刻はこの値で決まります。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.τ"></a>

## 定義 `τ`

### 式

$$\tau=\frac{\log(2/r)}{200}$$

### Lean のコメント（日本語訳）

> 閾値を横切る時刻。

### 定義の説明

初期値 \(y(0)=2\) から率 200 で減衰する \(2e^{-200t}\) が、ちょうど \(r\) になる時刻 \(2e^{-200\tau}=r\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y"></a>

## 定義 `y`

### 式

$$y(t)=2\exp\bigl(-(160t+40\min(t,\tau))\bigr)$$

### Lean のコメント（日本語訳）

> 対称軌道の一成分。閾値の前は率 200、後は率 160 で指数減衰する。

### 定義の説明

\(t\le\tau\) では指数が \(-200t\)、\(t\ge\tau\) では \(-160t-40\tau\) になるよう、`min` 1 つで 2 本の指数をつないだ関数です。連続で、\(\tau\) だけで折れ曲がります。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.traj"></a>

## 定義 `traj`

### 式

$$x(t)=(y(t),\,-y(t))$$

### Lean のコメント（日本語訳）

> Python 例の連続時間劣勾配流の候補軌道。

### 定義の説明

2 主体の状態（座標 0 と座標 1）を並べた軌道。系 `DA` の状態型 `∀ i, State i` の元です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi"></a>

## 定義 `Phi`

### 式

$$\Phi(t)=2\max(y(t)^2-\theta,0)+8y(t)^2$$

### Lean のコメント（日本語訳）

> 軌道上の共有残差。

### 定義の説明

共有残差 \(\Phi_2=\sum_i[x_i^2-\theta]_++\gamma(x_0-x_1)^2\)（\(\gamma=2\)）に \(x=(y,-y)\) を代入した式です。後の `potential_traj` で、実際に `DA.potential` と一致することを示します。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.hingeGrad"></a>

## 定義 `hingeGrad`

### 式

$$g_h(x)=\begin{cases}2x&(x^2>\theta)\\0&(x^2\le\theta)\end{cases}$$

### Lean のコメント（日本語訳）

> hinge `max (x²-θ) 0` に対する、閾値上だけ勾配を取る選択劣勾配。

### 定義の説明

\([x^2-\theta]_+\) は \(x^2=\theta\) の点で折れ曲がり、微分できません。そこでは 0 を取る、という約束で一つの劣勾配を選びます。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.residualGrad"></a>

## 定義 `residualGrad`

### 式

$$g(x)=\bigl(g_h(x_0)+4(x_0-x_1),\ g_h(x_1)-4(x_0-x_1)\bigr)$$

### Lean のコメント（日本語訳）

> 共有残差の選択劣勾配。

### 定義の説明

\(\Phi_2\) の各座標方向の劣勾配：hinge 項の選択劣勾配と、不整合項 \(2(x_0-x_1)^2\) の偏微分 \(\pm4(x_0-x_1)\) の和です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.q"></a>

## 定義 `q`

### 式

$$q(t)=160t+40\min(t,\tau)$$

### Lean のコメント（日本語訳）

> `y` の指数部を表す、切替後に傾きが変わる関数。

### 定義の説明

\(y=2e^{-q}\) と書けるようにした指数部。傾きは \(\tau\) の前で 200、後で 160 です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.r_sq"></a>

## 補題 `r_sq`

### 式

$$r^2=\theta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(r\) は \(\theta\) の平方根として定義したので、2 乗すると \(\theta\) に戻る、という確認です。

### 証明の概略

1. `Real.sq_sqrt` に \(0\le\theta\)（\(\theta=1/10\)）を与える。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.r_pos"></a>

## 補題 `r_pos`

### 式

$$r>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(r\) が正であること。以後の割り算や不等式で使います。

### 証明の概略

1. `Real.sqrt_pos` に \(0<\theta\) を与える。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.tau_pos"></a>

## 補題 `tau_pos`

### 式

$$\tau>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替時刻が正であること。\(\log(2/r)>0\) すなわち \(2/r>1\) を示せばよく、\(r^2=1/10\) より \(r<1\) です。

### 証明の概略

1. \(2/r>1\) を `lt_div_iff₀` と \(r^2=1/10\)（`nlinarith`）で示す。
2. `Real.log_pos` から \(\log(2/r)>0\)、200 で割って正。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.min_eq_left_of_le"></a>

## 補題 `min_eq_left_of_le`

### 式

$$t\le\tau\ \Rightarrow\ \min(t,\tau)=t$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`min_eq_left` の言い換え。`y` の「切替前」の式を取り出すときに使います。

### 証明の概略

1. `min_eq_left` を適用。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.min_eq_right_of_le"></a>

## 補題 `min_eq_right_of_le`

### 式

$$\tau\le t\ \Rightarrow\ \min(t,\tau)=\tau$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替後の式を取り出すときに使う `min_eq_right` の言い換え。

### 証明の概略

1. `min_eq_right` を適用。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_before"></a>

## 補題 `y_before`

### 式

$$t\le\tau\ \Rightarrow\ y(t)=2e^{-200t}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替前は、\(y\) が単純な指数減衰（率 200）であること。

### 証明の概略

1. `min t τ = t` で書き換える。
2. 指数部 \(-(160t+40t)=-200t\) を `ring_nf` で整理。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_after"></a>

## 補題 `y_after`

### 式

$$\tau\le t\ \Rightarrow\ y(t)=r\,e^{-160(t-\tau)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替後は、切替時刻の値 \(y(\tau)=r\) から率 160 で減衰すること。

### 証明の概略

1. `min t τ = τ` で書き換え、指数部を \(-160(t-\tau)+(-200\tau)\) に分解して指数の積にする。
2. \(e^{-200\tau}=r/2\)（\(\tau\) の定義から \(\log(2/r)\) の指数が \(2/r\) になる）を示して代入し、整理。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_zero"></a>

## 補題 `y_zero`

### 式

$$y(0)=2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期値が Python 例と同じ 2 であること。

### 証明の概略

1. \(\min(0,\tau)=0\)（\(\tau>0\)）で書き換え、`simp`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.traj_zero"></a>

## 補題 `traj_zero`

### 式

$$x(0)=(2,-2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道の初期状態が、上流で定義した初期値 `x0`（\((2,-2)\)）と一致すること。Python 例の初期条件を保っている確認です。

### 証明の概略

1. 座標ごとに場合分け（`fin_cases`）し、`y_zero` で `simp`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_nonneg"></a>

## 補題 `y_nonneg`

### 式

$$y(t)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

指数関数の定数倍なので常に非負。\(\Phi\) の式変形で符号が必要になります。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_sq_le_four"></a>

## 補題 `y_sq_le_four`

### 式

$$t\ge0\ \Rightarrow\ y(t)^2\le4$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道が初期の大きさ以内に留まる（\(|y|\le2\)）こと。

### 証明の概略

1. 指数部 \(160t+40\min(t,\tau)\ge0\) を場合分け（\(t\le\tau\) か否か）で示す。
2. \(e^{-(\cdot)}\le1\) から \(0<y\le2\)、よって \(y^2\le4\)（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.q_lipschitz"></a>

## 補題 `q_lipschitz`

### 式

$$|q(s)-q(t)|\le200\,|s-t|$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(q\) が定数 200 のリプシッツ連続であること。\(y\) の絶対連続性の足場です。

### 証明の概略

1. \(q(s)-q(t)=160(s-t)+40(\min(s,\tau)-\min(t,\tau))\) と書く。
2. `min` が 1-リプシッツであることと三角不等式から \(160+40=200\) の係数を得る。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.exp_lipschitzOn_Iic"></a>

## 補題 `exp_lipschitzOn_Iic`

### 式

$$\exp\ \text{は}\ (-\infty,0]\ \text{上で 1-リプシッツ}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(x\le0\) では \(0<e^x\le1\) なので、傾き \(e^x\) が 1 以下。そこで指数関数が非拡大写像になります。

### 証明の概略

1. 凸集合上の平均値定理型の補題 `Convex.lipschitzOnWith_of_nnnorm_deriv_le` を使う。
2. 導関数が \(e^x\le1\)（\(x\le0\)）であることを示す。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.q_nonneg"></a>

## 補題 `q_nonneg`

### 式

$$t\ge0\ \Rightarrow\ q(t)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(y=2e^{-q}\) の指数が \(\le0\) の側に入ることの確認。

### 証明の概略

1. \(t\le\tau\) と \(t>\tau\) で場合分けして `positivity`／`nlinarith`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_ac"></a>

## 補題 `y_ac`

### 式

$$y\ \text{は}\ [0,T]\ \text{上で絶対連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理2の一般結論が要求する、軌道の絶対連続性（折れ曲がりを許す程度の滑らかさ）。

### 証明の概略

1. リプシッツ連続な関数は絶対連続（`LipschitzOnWith.absolutelyContinuousOnInterval`）。定数は 400。
2. \(q\) の 200-リプシッツ性と、指数の \(\le0\) 側での 1-リプシッツ性を合成し、係数 2 を掛けて 400。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_ac"></a>

## 補題 `Phi_ac`

### 式

$$\Phi\ \text{は}\ [0,T]\ \text{上で絶対連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差の軌道上の値が絶対連続であること。一般定理の前提の一つです。

### 証明の概略

1. \(y\) が絶対連続 → \(y^2\) も絶対連続（積）→ \(y^2-\theta\) も。
2. \(\max(\cdot,0)\) は 1-リプシッツなので合成しても絶対連続。
3. 定数倍と和を取って \(\Phi=2\max(y^2-\theta,0)+8y^2\) を得る。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_hasDeriv_before"></a>

## 補題 `y_hasDeriv_before`

### 式

$$t<\tau\ \Rightarrow\ \dot y(t)=-200\,y(t)$$

### Lean のコメント（日本語訳）

> 閾値の手前では、軌道の一成分は率 200 の微分方程式に従う。

### 補題の説明

切替前の流れの方程式。

### 証明の概略

1. \(t\) の近傍では \(u<\tau\) なので \(y=2e^{-200u}\)（`y_before`）。
2. 合成関数の微分で \(2\cdot e^{-200t}\cdot(-200)=-200\,y(t)\)。
3. 近傍で関数が一致するので微分も一致する（`congr_of_eventuallyEq`）。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_deriv_before"></a>

## 補題 `y_deriv_before`

### 式

$$t<\tau\ \Rightarrow\ y'(t)=-200\,y(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`y_hasDeriv_before` を `deriv` の形にしたもの。

### 証明の概略

1. `HasDerivAt.deriv`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_hasDeriv_after"></a>

## 補題 `y_hasDeriv_after`

### 式

$$t>\tau\ \Rightarrow\ \dot y(t)=-160\,y(t)$$

### Lean のコメント（日本語訳）

> 閾値の後では、軌道の一成分は率 160 の微分方程式に従う。

### 補題の説明

切替後の流れの方程式。

### 証明の概略

`y_hasDeriv_before` と同様。近傍で \(y=r\,e^{-160(u-\tau)}\) になることを使い、合成関数の微分で \(-160\,y\) を得る。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_deriv_after"></a>

## 補題 `y_deriv_after`

### 式

$$t>\tau\ \Rightarrow\ y'(t)=-160\,y(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`y_hasDeriv_after` の `deriv` 版。

### 証明の概略

1. `HasDerivAt.deriv`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.exp_neg200tau"></a>

## 補題 `exp_neg200tau`

### 式

$$e^{-200\tau}=\frac r2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替時刻の定義から \(2e^{-200\tau}=r\) となること。`y_after` と同じ事実を単独の補題にして、不等式の評価で再利用します。

### 証明の概略

1. \(-200\tau=-\log(2/r)\) と書き換え、`Real.exp_neg`、`Real.exp_log` で \(r/2\) に。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_gt_r_before"></a>

## 補題 `y_gt_r_before`

### 式

$$t<\tau\ \Rightarrow\ r<y(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替前は \(|y|>r\)、すなわち hinge が働いている（個人残差が正）ことを示します。

### 証明の概略

1. \(t<\tau\) より \(e^{-200\tau}<e^{-200t}\)（指数の単調性）。
2. `exp_neg200tau` で左辺を \(r/2\) に置き換え、\(y=2e^{-200t}\) と比べる。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_le_r_after"></a>

## 補題 `y_le_r_after`

### 式

$$\tau\le t\ \Rightarrow\ y(t)\le r$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替後は \(|y|\le r\)、hinge は 0 です。

### 証明の概略

1. \(y=r\,e^{-160(t-\tau)}\)、\(e^{-160(t-\tau)}\le1\) から。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.y_lt_r_after"></a>

## 補題 `y_lt_r_after`

### 式

$$\tau<t\ \Rightarrow\ y(t)<r$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替時刻より後は**厳密に** \(y<r\)。劣勾配が連続な範囲（活性でない側）に入るため、微分の評価が楽になります。

### 証明の概略

1. \(e^{-160(t-\tau)}<1\) と \(r>0\) から。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_eq_before"></a>

## 補題 `Phi_eq_before`

### 式

$$t<\tau\ \Rightarrow\ \Phi(t)=10\,y(t)^2-2\theta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替前は hinge が活性なので \(\max\) が外れ、\(\Phi=2(y^2-\theta)+8y^2\)。

### 証明の概略

1. `y_gt_r_before` から \(y^2-\theta\ge0\)（\(y^2-r^2=(y-r)(y+r)\ge0\)）。
2. `max_eq_left` で外し、`ring`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_eq_after"></a>

## 補題 `Phi_eq_after`

### 式

$$\tau\le t\ \Rightarrow\ \Phi(t)=8\,y(t)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替後は hinge が 0 で、不整合項だけが残る。

### 証明の概略

1. `y_le_r_after` から \(y^2-\theta\le0\)。
2. `max_eq_right` で外し、`ring`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_deriv_before"></a>

## 補題 `Phi_deriv_before`

### 式

$$t<\tau\ \Rightarrow\ \Phi'(t)=-4000\,y(t)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替前の \(\Phi\) の導関数。\(\Phi=10y^2-2\theta\) より \(\Phi'=20y\dot y=-4000y^2\)。

### 証明の概略

1. \(y^2-\theta>0\) は連続性により \(t\) の近傍でも成り立つので、近傍で \(\Phi=10y^2-2\theta\) と書ける。
2. 積の微分と `y_hasDeriv_before` から \(10\cdot2y\cdot(-200y)\)。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_deriv_after"></a>

## 補題 `Phi_deriv_after`

### 式

$$t>\tau\ \Rightarrow\ \Phi'(t)=-2560\,y(t)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替後の導関数。\(\Phi=8y^2\) より \(\Phi'=16y\dot y=-2560y^2\)。

### 証明の概略

1. `y_lt_r_after` から \(y^2-\theta<0\)、連続性により近傍でも成り立つので近傍で \(\Phi=8y^2\)。
2. 積の微分と `y_hasDeriv_after`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.Phi_deriv_decay_ae"></a>

## 補題 `Phi_deriv_decay_ae`

### 式

$$\Phi'(s)\le-2\,\Phi(s)\quad(\text{a.e. }s\in[0,T])$$

### Lean のコメント（日本語訳）

> 軌道上の残差は、切替時刻を除き \(\Phi'\le-2\Phi\) を満たす。

### 補題の説明

定理2の一般結論が要求する下降条件（\(c=1\)）。\(\tau\) は 1 点（測度 0）なので、それを除外します。

### 証明の概略

1. 1 点集合の測度は 0。\(s\ne\tau\) の点で、\(s<\tau\) と \(s>\tau\) に場合分け。
2. \(s<\tau\)：\(-4000y^2\le-2(10y^2-2\theta)\)、つまり \(-3980y^2\le4\theta\)（\(\theta\ge0\) を使って `nlinarith` が閉じる）。
3. \(s>\tau\)：\(-2560y^2\le-16y^2\)。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.potential_traj"></a>

## 補題 `potential_traj`

### 式

$$\text{DA.potential}(x(t),t)=\Phi(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上流の `StatePairResidualSystem.potential`（一般の共有残差）に軌道を代入した値が、ここで手で書いた `Phi` と一致すること。以後、`Phi` についての評価がそのまま一般定理の言葉になります。

### 証明の概略

1. 上流の `potential_eq`（具体的な式への展開）で書き換え、`simp` と `ring`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.hingeGrad_support"></a>

## 補題 `hingeGrad_support`

### 式

$$\max(z^2-\theta,0)\ \ge\ \max(x^2-\theta,0)+g_h(x)\,(z-x)$$

### Lean のコメント（日本語訳）

> hinge 項について、選んだ値は凸劣勾配の支持不等式を満たす。

### 補題の説明

劣勾配の定義（支持不等式）：関数のグラフは、選んだ傾きの接線より上にある。\(\theta<x^2\) か否かで 2 通りです。

### 証明の概略

1. 活性の場合：\(g_h=2x\)。\(z^2-\theta\le\max\) と \((z-x)^2\ge0\)（\(z^2\ge x^2+2x(z-x)\)）から。
2. 非活性の場合：\(g_h=0\)。\(\max(z^2-\theta,0)\ge0\ge\max(x^2-\theta,0)\)。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.residualGrad_support"></a>

## 補題 `residualGrad_support`

### 式

$$\Phi_2(z)\ \ge\ \Phi_2(x)+\sum_i g_i(x)(z_i-x_i)$$

### Lean のコメント（日本語訳）

> `residualGrad x` は具体共有残差の凸劣勾配である（支持不等式の形）。

### 補題の説明

\(\Phi_2=\sum[\cdot]_++\gamma(x_0-x_1)^2\) 全体について、`residualGrad` が劣勾配であることの具体的な不等式です。

### 証明の概略

1. 2 個の hinge 項は `hingeGrad_support` を各座標に適用。
2. 不整合項は 2 次式で、\((a-b)^2\ge0\) 型の評価（\(2(z_0-z_1)^2\ge2(x_0-x_1)^2+4(x_0-x_1)((z_0-z_1)-(x_0-x_1))\)）。
3. 和を `Fin.sum_univ_two` で展開し `nlinarith`。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.residualGrad_is_subgradient"></a>

## 補題 `residualGrad_is_subgradient`

### 式

$$\Phi_2(z)\ \ge\ \Phi_2(x)+\sum_i g_i(x)(z_i-x_i)$$

### Lean のコメント（日本語訳）

> 選択したベクトルは、定理2の共有ポテンシャルの凸劣勾配である。

### 補題の説明

上の具体式の不等式を、一般系 `DA.potential`（時刻 0）についての statement に言い換えたもの。`residualGrad` が「定理2の \(\Phi_2\) の」劣勾配だと言える根拠です。

### 証明の概略

1. `potential_eq` で `DA.potential` を具体式にし、`residualGrad_support` を適用。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.traj_flow_before"></a>

## 補題 `traj_flow_before`

### 式

$$t<\tau\ \Rightarrow\ \frac{d}{ds}x_i(s)\Big|_{s=t}=-20\,g_i(x(t))\quad(i=0,1)$$

### Lean のコメント（日本語訳）

> 切替前は、選択劣勾配流の両成分が活性ヒンジを含む勾配方程式に従う。

### 補題の説明

切替前は \(y^2>\theta\)（活性）なので \(g_0=2y+8y=10y\)、\(g_1=-10y\)。\(\dot x_0=-20\cdot10y=-200y\)、\(\dot x_1=+200y\) が成り立ちます。

### 証明の概略

1. `y_gt_r_before` から \(\theta<y^2\)（活性）。
2. 座標 0：`y_deriv_before` と `residualGrad` の定義を展開して `ring`。
3. 座標 1：\(-y\) の微分が \(+200y\)（符号反転）であることを示してから同様に。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.traj_flow_after"></a>

## 補題 `traj_flow_after`

### 式

$$t>\tau\ \Rightarrow\ \frac{d}{ds}x_i(s)\Big|_{s=t}=-20\,g_i(x(t))\quad(i=0,1)$$

### Lean のコメント（日本語訳）

> 切替後はヒンジが非活性となり、二次の不整合項だけが流れを決める。

### 補題の説明

切替後は \(y^2<\theta\)（非活性）。\(g_0=8y\)、\(g_1=-8y\) なので \(\dot x_0=-160y\)、\(\dot x_1=+160y\)。

### 証明の概略

`traj_flow_before` と同様。`y_lt_r_after` から非活性、`y_deriv_after`（率 160）を使う。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.traj_flow_ae"></a>

## 補題 `traj_flow_ae`

### 式

$$\dot x_i(t)=-20\,g_i(x(t))\quad(\text{a.e. }t\in[0,T])$$

### Lean のコメント（日本語訳）

> 閾値の一点を除けば、全区間で軌道は選択劣勾配方程式を満たす。

### 補題の説明

前後 2 つの補題をつなぎ、切替時刻 \(\tau\)（測度 0）を除いた a.e. の流れの方程式にします。これで、軌道が確かに「`residualGrad` に沿った劣勾配流」であるという主張が形式化されます。

### 証明の概略

1. \(\{\tau\}\) は測度 0。\(t\ne\tau\) の点で \(t<\tau\) か \(t>\tau\) かに場合分けし、前後の補題を適用。

----

<a id="Tomabechi.Examples.Theorem2SubgradientFlow.subgradient_flow_conclusion"></a>

## 補題 `subgradient_flow_conclusion`

### 式

$$\begin{aligned}&\mathrm{dist}(x(t),\Omega_2)\le\sqrt{2\Phi(0)}\,e^{-t}\\&\text{個人残差}_i(t)\le\tfrac{\Phi(0)}{w_i}e^{-2t},\quad\text{不整合}_e(t)\le\tfrac{\Phi(0)}{w_e}e^{-2t}\\&\text{共有 TCZ の点では全主体の表象が一致}\end{aligned}$$

### Lean のコメント（日本語訳）

> 実際の劣勾配流から定理2の条件付き定量結論を得る。

### 補題の説明

このファイルの主定理。Python 例のケース A の連続時間劣勾配流について、定理2の速さつきの結論（\(c=1\)）が得られます。`Theorem2.lean` の一般定理 `theorem2_state_pair_conditional_conclusion` の全前提——絶対連続性（`Phi_ac`）、a.e. 下降（`Phi_deriv_decay_ae`）、誤差境界（`caseA_error_bound`）、共有零集合の非空性（`sharedTCZ_nonempty`）、連結性（`connectedA`）——を満たすことで適用します。**これは連続時間の具体モデルでの結論で、Python の Euler 列・数値出力の証明ではありません。**

### 証明の概略

1. 一般定理に、全状態空間 `Set.univ`（\(K\)）、軌道 `traj`、連結性 `connectedA`、定数 \(c=1\)（下降率）、\(C=2\)（誤差境界 \(\mathrm{dist}^2\le C\Phi\)）、時間区間 \([0,t]\) を渡す。
2. AC の前提：`potential_traj` で \(\Phi\) に書き換えて `Phi_ac`。
3. a.e. 下降の前提：同様に `Phi_deriv_decay_ae`。
4. 誤差境界は上流の `caseA_error_bound`、共有零集合の非空性は `sharedTCZ_nonempty`。

----

## コメント修正記録

（なし。この `.lean` のコメントは、本書執筆時点の宣言と食い違っていないことを確認した。）
