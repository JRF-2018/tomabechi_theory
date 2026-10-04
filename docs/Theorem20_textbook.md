# Theorem20.lean 解説

> 対象: [`Theorem20.lean`](../Theorem20.lean)（定理20：象徴臨場感による指定LUB方向への条件付き核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| はさみうちの原理 | 0 以上で、0 に収束するものに抑えられた量は 0 に収束する。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理20（**象徴臨場感による、指定した LUB の方向への条件付きの収束**）の核です。実効ポテンシャル

$$\tilde V(x)=V_0(x)-\kappa q\,P(x)\,s\bigl(D(x)\bigr)$$

（\(D\) は指定した目標（LUB の表象）までの「距離型の関数」、\(s\) はその象徴的な臨場感の応答）の勾配流 \(\dot x=-M\nabla\tilde V\)（\(M\) は移動度の行列）に沿って、**\(D\) が厳密に減り**（(20.1)）、**PL 条件**（\(2\mu D\le\|\nabla D\|_M^2\)）のもとで**指数的に減る**（(20.2)、速さ \(2\mu c\)）ことを示します。

### 0.2 中心の計算

距離関数 \(D\) の軌道に沿った微分は、チェーンルールで \(\dot D=\langle\nabla D,\dot x\rangle\)、閉ループ \(\dot x=-M\nabla\tilde V\) を代入すると

$$\dot D=\underbrace{-\langle\nabla D,M\nabla V_0\rangle+\kappa qS\langle\nabla D,M\nabla P\rangle}_{(20.A)\ \text{の左辺（基礎地形・臨場感の交差項）}}+\underbrace{\kappa qP\,s'(D)\,\|\nabla D\|_M^2}_{(20.B)\ \text{の寄与（象徴項）}}.$$

条件 (20.A) \(\text{交差項}\le b\,g^2\)、(20.B) \(\kappa qP(-s')\ge b+c\)（\(g^2=\|\nabla D\|_M^2\)）から、\(\dot D\le-c\,g^2<0\)（**厳密下降**）。

### 0.3 構成

| 内容 | 宣言 |
| --- | --- |
| 距離の微分 | `distance_derivative_along_gradient_path`, `effective_potential_hasGradientAt`, `gradient_flow_distance_derivative`, `inverse_metric_direction_identity` |
| 方向結論 (20.1) | `theorem20_directional_conclusion`, `theorem20_directional_from_potential`, `strict_distance_descent`, `positive_direction_component` |
| PL と指数評価 (20.2) | `pl_yields_rate_differential`, `pl_strict_descent`, `exponential_distance_bound*`, `distance_error_exponential_bound`, `theorem20_exponential_conclusion`, `distance_tendsto_zero_of_exponential_bound` |
| 全軌道の接続 | `theorem20_full_trajectory_conclusion_everywhere_strict`, `gradient_eq_zero_of_nonnegative_at_zero`, `theorem20_full_trajectory_conclusion_of_original_conditions` |
| 方策の流れ版 | `theorem20_policy_flow_original_condition_conclusion` |

### 0.4 このファイルが証明していないこと

- 指定 LUB \(u_\sigma=\bigvee W_\sigma\) は、束の**最大元と同一視しません**。
- **ベクトル場から各仮定（(20.A)(20.B)・PL 条件・距離の誤差境界・勾配の非零性）を導く「モデルの構成」は別の課題**です。これらは**入力の仮定**として受け取ります（ファイル冒頭のコメント）。
- 一般の軌道に沿う指数評価 (20.2) は、PL 条件から**微分不等式**を作り、指数重みつきの関数の単調性を経て形式化します。
- 方策の流れ版は、微分可能な方策の流れ（始点でも両側微分をもつ）を**正則性の仮定**とし、ボレルなフィードバックや再始動の法則から導くことはしません。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理20：象徴臨場感による、指定 LUB の方向への条件付きの核**
>
> 指定 LUB \(u_\sigma=\bigsqcup W_\sigma\) は、束の最大元と同一視しない。ここでは、原文 (20.A/B) の微分の計算をスカラー化した核を置く。基礎の地形・臨場感の交差項を `a`、計量の勾配のノルム 2 乗を \(g^2\) とすると、(20.A) は \(a\le b\,g^2\)、(20.B) の寄与は `symbolTerm` \(\le-(b+c)g^2\) である。これらから (20.1) の厳密な下降を得る。PL 条件からの微分不等式も示すが、一般の軌道に沿う指数の評価 (20.2) は、別の微分不等式から、指数の重みつきの関数の単調性を経て、形式化する。距離の誤差境界から、距離の指数の評価も得る。ベクトル場から各仮定を導く、モデルの構成は別の課題。

名前空間は `Tomabechi.Theorem20`。`open Filter`、`open scoped Gradient Topology`。

---

<a id="Tomabechi.Theorem20.distance_derivative_along_gradient_path"></a>

## 補題 `distance_derivative_along_gradient_path`

### 式

$$\frac{d}{dt}D(x(t))=\langle\nabla D(x(t)),\dot x(t)\rangle$$

### Lean のコメント（日本語訳）

> 空間の上で勾配をもつ、スカラー関数を、微分可能な状態の軌道に沿って評価したときの、連鎖律。これにより、\(\dot D=\langle\nabla D,\dot x\rangle\) を、別の数理的な仮定にせず導ける。

### 補題の説明

距離型関数 \(D\) の軌道に沿った時間微分は、勾配と速度の内積です（多変数の連鎖律）。

### 証明の概略

1. 勾配の定義 `HasGradientAt`（Fréchet 微分を内積で表す）と軌道の `HasDerivAt` の合成（`HasFDerivAt.comp_hasDerivAt`）。

----

<a id="Tomabechi.Theorem20.effective_potential_hasGradientAt"></a>

## 補題 `effective_potential_hasGradientAt`

### 式

$$\nabla\bigl(V_0-\kappa q\,P\,s(D)\bigr)=\nabla V_0-\kappa q\bigl(s(D)\nabla P+P\,s'(D)\nabla D\bigr)$$

### Lean のコメント（日本語訳）

> 積と合成の微分則から、実効ポテンシャル \(V_0-\kappa qP\,s(D)\) の勾配を構成する。\(s'(D)\) は、指定した点での導関数である。

### 補題の説明

実効ポテンシャルの勾配を、積の微分則・合成関数の微分則で具体的に書き下します。

### 証明の概略

1. `HasGradientAt.mul`（積）、合成関数の微分則（合成）、`HasGradientAt.sub`、定数倍（`HasGradientAt.const_smul`）。

----

<a id="Tomabechi.Theorem20.gradient_flow_distance_derivative"></a>

## 補題 `gradient_flow_distance_derivative`

### 式

$$\langle\nabla D,\dot x\rangle=-\langle\nabla D,M\nabla V_0\rangle+\kappa qS\langle\nabla D,M\nabla P\rangle+\kappa qP\,s'\,\langle\nabla D,M\nabla D\rangle$$

### Lean のコメント（日本語訳）

> ベクトル場の上での、距離の微分の展開。`hEffectiveGradient` は、実効ポテンシャル \(V_0-\kappa qP\,s(D)\) の勾配に対する、積・合成則を表す。仮定された ODE `velocity=-M∇Ṽ` に代入すると、(20.A/B) に現れる項と、最後の \(\kappa qP\,s'\|\nabla D\|_M^2\) が、正確に得られる。

### 補題の説明

距離の微分を、(20.A) の交差項と、(20.B) の象徴項に**分解**する、代数的な計算です。

### 証明の概略

1. `hFlow : velocity = -M gradEffective` と `hEffectiveGradient` を代入し、内積の線形性（`inner_sub_right`, `inner_smul_right`, `inner_neg_right`）で展開（`ring`）。

----

<a id="Tomabechi.Theorem20.inverse_metric_direction_identity"></a>

## 補題 `inverse_metric_direction_identity`

### 式

$$\langle M^{-1}\dot x,\ d\rangle=-\langle\nabla D,\dot x\rangle\quad(d=-M\nabla D)$$

### Lean のコメント（日本語訳）

> 自己共役な移動度とその逆を用いると、実効勾配の流れの方向成分は、距離の減少率の負号に一致する。`inner (M⁻¹ velocity) direction` は、\(M^{-1}\) の計量の内積を表す。

### 補題の説明

指定した方向 \(d=-M\nabla D\)（\(D\) が最も速く減る方向）への、速度の成分が、\(-\dot D\) に等しい、という恒等式です。

### 証明の概略

1. \(M^{-1}\dot x\) と \(d=-M\nabla D\) の内積を、\(M\) の自己共役性 `hsymmetric` と左逆 `hleft` で移して \(-\langle\nabla D,\dot x\rangle\) を得る。

----

<a id="Tomabechi.Theorem20.theorem20_directional_conclusion"></a>

## 定理 `theorem20_directional_conclusion`

### 式

$$\langle\nabla D,\dot x\rangle\le-c\,g^2\ \ \wedge\ \ \langle M^{-1}\dot x,d\rangle>0$$

### Lean のコメント（日本語訳）

> 原文の、1 つの適用区間での、方向の結論 (20.1)。ここでは、`hEffectiveGradient` が、実効ポテンシャルの勾配の積・合成則、`hFlow` が閉ループの ODE を表す。`hA` と `hB` は、論文の一様な条件を、現在の状態で評価したもの、正の `g2` は、移動度の正定値性と、目標の外での勾配の非零性に対応する。

### 補題の説明

**(20.1)**：条件 (20.A)(20.B) から、距離型関数 \(D\) が厳密に減り（\(\dot D\le-cg^2<0\)）、速度が指定方向 \(d\) に正の成分をもつ（LUB の方向へ進む）。

### 証明の概略

1. `gradient_flow_distance_derivative` で \(\langle\nabla D,\dot x\rangle=-\langle\nabla D,M\nabla V\rangle+\kappa qS\langle\nabla D,M\nabla P\rangle+\kappa qP\,s'\langle\nabla D,M\nabla D\rangle\) と分解する。
2. (20.B) \(\kappa qP(-s')\ge b+c\) から第 3 項が \(\le-(b+c)\langle\nabla D,M\nabla D\rangle\)、(20.A) と足して \(\langle\nabla D,\dot x\rangle\le-c\langle\nabla D,M\nabla D\rangle\)（`nlinarith`）。
3. \(\nabla D\ne0\) なら右辺が負で \(\langle\nabla D,\dot x\rangle<0\)。`inverse_metric_direction_identity`（\(\langle M^{-1}\dot x,-M\nabla D\rangle=-\langle\nabla D,\dot x\rangle\)）で、方向成分が正（51 行）。

----

<a id="Tomabechi.Theorem20.theorem20_directional_from_potential"></a>

## 定理 `theorem20_directional_from_potential`

### 式

$$\text{ポテンシャルを関数として与えた}\ (20.1)$$

### Lean のコメント（日本語訳）

> 原文の実効ポテンシャルを、関数として与え、各項の勾配が存在するときの、方向の結論。積・合成則で、実効勾配を構成してから、閉ループの方程式と (20.A/B) を適用する。

### 補題の説明

上の定理の、実効勾配を `effective_potential_hasGradientAt` で**導いた**版です。

### 証明の概略

1. `effective_potential_hasGradientAt` で勾配を構成し、`theorem20_directional_conclusion` を適用。

----

<a id="Tomabechi.Theorem20.strict_distance_descent"></a>

## 補題 `strict_distance_descent`

### 式

$$\text{base}\le b\,g^2,\ \ \text{symbol}\le-(b+c)g^2\ \Longrightarrow\ \text{base}+\text{symbol}\le-c\,g^2$$

### Lean のコメント（日本語訳）

> (20.A/B) の代数の核。`g2` は \(\|\nabla D\|_M^2\)、`baseTerm` は (20.A) の左辺、`symbolTerm` は \(\kappa qP\,s'(D)\,g^2\) に当たる。

### 補題の説明

2 つの不等式を足すだけです（\(b\,g^2-(b+c)g^2=-cg^2\)）。

### 証明の概略

1. `linarith`。

----

<a id="Tomabechi.Theorem20.pl_yields_rate_differential"></a>

## 補題 `pl_yields_rate_differential`

### 式

$$\dot D\le-c\,g^2,\ \ 2\mu D\le g^2\ \Longrightarrow\ \dot D\le-2\mu c\,D$$

### Lean のコメント（日本語訳）

> PL 型の条件を追加すると、距離関数の軌道の微分は、指数の評価に必要な、微分不等式 \(\dot D\le-2\mu cD\) を満たす。

### 補題の説明

**PL 条件**（\(\|\nabla D\|_M^2\ge2\mu D\)）があれば、厳密下降が**指数下降**になります。

### 証明の概略

1. \(-cg^2\le-c\cdot2\mu D\)（\(c\ge0\)）。

----

<a id="Tomabechi.Theorem20.positive_direction_component"></a>

## 補題 `positive_direction_component`

### 式

$$d_u=-\dot D,\ \dot D<0\ \Longrightarrow\ d_u>0$$

### Lean のコメント（日本語訳）

> \(d_u=-M\nabla D\) と \(\dot x=-M\nabla\tilde V\) の定義から得る、方向成分の符号。原文の計量の内積の恒等式を、`distanceDeriv = Ḋ` として明示する。

### 補題の説明

距離が減っている（\(\dot D<0\)）なら、指定方向への成分は正です。

### 証明の概略

1. `hidentity` で書き換えて `linarith`。

----

<a id="Tomabechi.Theorem20.pl_strict_descent"></a>

## 補題 `pl_strict_descent`

### 式

$$\dot D\le-cg^2,\ 2\mu D\le g^2,\ D>0\ \Longrightarrow\ \dot D<0$$

### Lean のコメント（日本語訳）

> PL の境界を使ったとき、軌道の上の距離の微分が負となる。

### 補題の説明

目標の外（\(D>0\)）では、距離が**厳密に**減ります（\(g^2\ge2\mu D>0\)）。

### 証明の概略

1. \(-cg^2\le-2\mu cD<0\)（`nlinarith`）。

----

<a id="Tomabechi.Theorem20.exponential_distance_bound"></a>

## 補題 `exponential_distance_bound`

### 式

$$D\in C^1,\ D'\le-\text{rate}\cdot D\ \Longrightarrow\ D(t)\le D(t_0)e^{-\text{rate}(t-t_0)}$$

### Lean のコメント（日本語訳）

> \(C^1\) な非負の距離関数が、PL の微分不等式を満たすなら、指数の重みを掛けた関数は非増加となり、原文 (20.2) の、距離関数の定量的な評価を得る。原文の \(C^1\) の仮定に合わせ、a.e. の微分ではなく、各時刻での微分不等式を用いる。

### 補題の説明

**指数の比較**：\(e^{\text{rate}\,t}D(t)\) の微分が \(\le0\) なので単調非増加です（Grönwall 型）。

### 証明の概略

1. \(g(t)=e^{\text{rate}(t-t_0)}D(t)\) の微分は \(e^{\ldots}(D'+\text{rate}\,D)\le0\)。`antitoneOn_of_deriv_nonpos` で \(g(t)\le g(t_0)=D(t_0)\)。

----

<a id="Tomabechi.Theorem20.exponential_distance_bound_on_interval"></a>

## 補題 `exponential_distance_bound_on_interval`

### 式

$$\text{導関数の条件が}\ [t_0,t]\ \text{でだけ}\ \Longrightarrow\ D(t)\le D(t_0)e^{-\text{rate}(t-t_0)}$$

### Lean のコメント（日本語訳）

> 指数の比較の補題の区間版。導関数は \([t_0,t]\) の上でだけ要求するので、応用では、より前の時刻での正則性や減衰の仮定は要らない。

### 補題の説明

上の補題の、区間 \([t_0,t]\) だけで微分可能性・不等式を仮定する版です。

### 証明の概略

1. 区間での平均値の定理系の補題（`antitoneOn_of_deriv_nonpos` の区間版）。

----

<a id="Tomabechi.Theorem20.distance_error_exponential_bound"></a>

## 補題 `distance_error_exponential_bound`

### 式

$$\operatorname{dist}\le C\sqrt D,\ D(t)\le D(t_0)e^{-\text{rate}(t-t_0)}\ \Longrightarrow\ \operatorname{dist}(t)\le C\sqrt{D(t_0)}\,e^{-\text{rate}(t-t_0)/2}$$

### Lean のコメント（日本語訳）

> 距離の誤差境界 \(\mathrm{dist}\le C\sqrt D\) を加えると、状態の距離も、指数率 \(\text{rate}/2\) で減衰する。原文では \(\text{rate}=2\mu c\) を代入する。

### 補題の説明

\(D\) が速さ rate で減るなら、距離（\(\sqrt D\) 程度）は速さ rate/2 で減ります。

### 証明の概略

1. 平方根の単調性（`Real.sqrt_le_sqrt`）と \(\sqrt{xy}=\sqrt x\sqrt y\)、\(\sqrt{e^{-a}}=e^{-a/2}\)。

----

<a id="Tomabechi.Theorem20.theorem20_exponential_conclusion"></a>

## 定理 `theorem20_exponential_conclusion`

### 式

$$D(t)\le D(t_0)e^{-2\mu c(t-t_0)},\ \ \operatorname{dist}(t)\le C\sqrt{D(t_0)}\,e^{-\mu c(t-t_0)}$$

### Lean のコメント（日本語訳）

> 全適用時間で PL 型の条件が保たれる、1 つの軌道について、(20.1) と PL の境界・距離の誤差境界を合成し、原文 (20.2) の指数率 \(\mu c\) を得る。原文のコンパクトな前向き不変集合は、これらの一様な軌道の条件を保証する場として解釈される。

### 補題の説明

**(20.2)**：\(D\) の指数減衰（率 \(2\mu c\)）と、目標への距離の指数減衰（率 \(\mu c\)）。

### 証明の概略

1. `pl_yields_rate_differential` で \(D'\le-2\mu cD\)。`exponential_distance_bound` で \(D\) の評価、`distance_error_exponential_bound` で距離の評価。

----

<a id="Tomabechi.Theorem20.distance_tendsto_zero_of_exponential_bound"></a>

## 補題 `distance_tendsto_zero_of_exponential_bound`

### 式

$$0\le\operatorname{dist}\le Ae^{-\text{rate}(t-t_0)},\ \text{rate}>0\ \Longrightarrow\ \operatorname{dist}\to0$$

### Lean のコメント（日本語訳）

> 一様な指数の距離の評価と、距離の非負性から、\(t\to\infty\) の極限も得る。指数率は正であり、評価は、ある開始時刻以降に成立すれば十分。

### 補題の説明

はさみうちの原理で 0 に収束します。

### 証明の概略

1. `squeeze_zero'` と `Real.tendsto_exp_neg_atTop_nhds_zero`。

----

<a id="Tomabechi.Theorem20.theorem20_full_trajectory_conclusion_everywhere_strict"></a>

## 定理 `theorem20_full_trajectory_conclusion_everywhere_strict`

### 式

$$\text{(20.1)(20.2)\ と}\ \operatorname{dist}\to0\ (\text{全未来時刻で勾配が非零と仮定})$$

### Lean のコメント（日本語訳）

> 全未来時刻の勾配の非零性を置く、強い十分条件の版。原文の、目標の外の条件だけを要求する入口には、`theorem20_full_trajectory_conclusion_of_original_conditions` を使う。空間の上のポテンシャル・勾配・閉ループの軌道を、(20.1) と (20.2) に、一続きに接続する、条件付きの定理。距離の微分は、勾配の連鎖律から導出し、実効勾配は、積・合成則から構成する。仮定は初期時刻以後に限り、方向の評価・指数の評価・距離の極限を返す。

### 補題の説明

定理20の**全軌道の結論**（強い仮定版）：すべての時刻で \(g^2>0\)（勾配が 0 でない）と仮定します。

### 証明の概略

1. 軌道に沿った \(D\) の導関数 \(=\langle\nabla D,\dot x\rangle\)（`distance_derivative_along_gradient_path`）。
2. 各時刻で `theorem20_directional_from_potential` により、\(\frac d{dt}D\le-c\,g_2\)（\(g_2=\langle\nabla D,M\nabla D\rangle\)）と方向の結論を得る（(20.A)(20.B) と実効勾配の表示を仮定）。
3. PL 条件 \(g_2\ge2\mu D\) と合わせて \(D\) の指数減衰（`exponential_distance_bound_on_interval`）、距離の評価 `distance_error_exponential_bound`、極限 `distance_tendsto_zero_of_exponential_bound`（84 行）。

----

<a id="Tomabechi.Theorem20.gradient_eq_zero_of_nonnegative_at_zero"></a>

## 補題 `gradient_eq_zero_of_nonnegative_at_zero`

### 式

$$D\ge0,\ D(x)=0,\ \nabla D(x)=g\ \Longrightarrow\ g=0$$

### Lean のコメント（日本語訳）

> 非負関数の零点では、存在する勾配はゼロになる。定理20の目標の上では、方向の条件を仮定せず、この停留性から、収支の零の値を得る。

### 補題の説明

非負関数の最小点（零点）では勾配が 0 です（Fermat の定理）。

### 証明の概略

1. 零点は最小点なので、局所最小点での微分が 0（Fermat の定理）。

----

<a id="Tomabechi.Theorem20.theorem20_full_trajectory_conclusion_of_original_conditions"></a>

## 定理 `theorem20_full_trajectory_conclusion_of_original_conditions`

### 式

$$\begin{aligned}
&\dot x=-M\nabla(V_0-\kappa qP\,s(D))\ (\text{閉ループ}),\ M\ \text{対称・}\gamma\text{-強制的},\ D\ge0,\ D=0\iff x\in Z\ (Z\ne\emptyset\ \text{閉})\\
&\text{目標の外（}x\in K,\ x\notin Z\text{）でのみ：}\ \ \text{(20.A) }-\langle\nabla D,M\nabla V_0\rangle+\kappa q\,s(D)\langle\nabla D,M\nabla P\rangle\le b\langle\nabla D,M\nabla D\rangle,\\
&\qquad\text{(20.B) }\kappa qP\,(-s'(D))\ge b+c;\quad \text{PL: }2\mu D\le\langle\nabla D,M\nabla D\rangle;\quad \mathrm{dist}(x,Z)\le C\sqrt D\\
&\Longrightarrow\ \ D(x(t))\le D(x(t_0))\,e^{-2\mu c(t-t_0)},\ \ \mathrm{dist}(x(t),Z)\le C\sqrt{D(x(t_0))}\,e^{-\mu c(t-t_0)},\\
&\qquad \tfrac{d}{dt}D\le-c\langle\nabla D,M\nabla D\rangle,\ \ (x\notin Z\Rightarrow\tfrac d{dt}D<0),\ \ \langle M^{-1}\dot x,-M\nabla D\rangle=-\tfrac d{dt}D,\ \ \mathrm{dist}(x(t),Z)\to0
\end{aligned}$$
（\(b,c,\mu,\gamma>0\)、\(C\ge0\)。条件は全時刻 \(t\ge t_0\) の原文条件。）

### Lean のコメント（日本語訳）

> 定理20の、原文の条件による、全軌道の接続。方向の条件 A/B と勾配の非零性は、前向き不変集合 \(K\) の上の、目標の外にだけ課す。目標の上は、非負の距離型の関数の零点なので、勾配ゼロを導き、下降の微分もゼロとする。逆計量の恒等式は全時刻で、厳密な下降は目標の外で返す。PL の評価・距離の誤差から、指数率と極限を得る。

### 補題の説明

**定理20の主結論（原文の条件）**：条件は**目標の外でだけ**課します。目標の上では \(D=0\)（非負の関数の最小）なので勾配 0 で、そのまま微分も 0。目標の外では厳密に下降し、全体で指数収束・極限が成り立ちます。

### 証明の概略

1. 原文の条件は目標の外でだけ課されている。\(t\ge t_0\) の各時刻で、\(x(t)\in Z\)（\(D=0\)）か \(x(t)\notin Z\) かで場合分けする（目標の上では \(D\) が最小なので勾配が 0、`gradient_eq_zero_of_nonnegative_at_zero`）。
2. 目標の外では、条件 (20.A)(20.B)・PL から、定理 20 の方向の結論と \(\frac d{dt}D\le-c\,g_2\) を得る（`theorem20_directional_from_potential` を各時刻で使う）。
3. 全時刻で \(D\) の指数減衰（`exponential_distance_bound_on_interval`）、距離の指数評価（`distance_error_exponential_bound`）、極限（`distance_tendsto_zero_of_exponential_bound`）をまとめる（164 行）。

----

<a id="Tomabechi.Theorem20.theorem20_policy_flow_original_condition_conclusion"></a>

## 定理 `theorem20_policy_flow_original_condition_conclusion`

### 式

$$\text{方策の流れ }F\ \text{から軌道・速度・到達集合を生成した上の結論}$$

### Lean のコメント（日本語訳）

> 原文の条件の定理20の入口への、H-flow のアダプタ。`DifferentiableClosedLoopPolicyFlow` を要求する。その `solves` のフィールドは、始点での両側の微分を含む、すべての将来の時刻での、通常の導関数を与える。これは、前向きの AC＋a.e. の Carathéodory の解より強い、明示的な正則性の条件であり、このアダプタは、それを、ボレルなフィードバックや再始動の法則から導かない。軌道と速度は、無関係な関数ではなく、1 つの方策の流れから来る。

### 補題の説明

定理20の方策の流れ版：軌道 \(x=F.\text{flow}\)、速度 \(F.\text{vectorField}\) を同じ流れから取り、`theorem20_full_trajectory_conclusion_of_original_conditions` に渡します。

### 証明の概略

1. `hK`（軌道は到達可能集合内）、`hPath`（`F.solves` から `HasDerivAt`）、`hFlow`（閉ループの方程式）を用意して、原文の条件の定理を適用（`simpa`）。

----


## コメント修正記録

（なし）
