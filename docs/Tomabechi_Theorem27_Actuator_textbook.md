# Tomabechi/Theorem27/Actuator.lean 解説

> 対象: [`Tomabechi/Theorem27/Actuator.lean`](../Tomabechi/Theorem27/Actuator.lean)（条件27-Aの制御入力・Dini微分・定量散逸補題）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理27（**無明起行：無明があると、行（意図的な働きかけ）が起こる**）の核心を示すファイルです。**条件 27-A**（制御入力のモデル）：状態 \(x\in E\) の力学が**制御アファイン**

$$\dot x=\text{drift}(t)+G(t)\,u(t)$$

（\(G\) は入力 \(u\in U\) を状態の速度に変える**作用素（アクチュエータ）**）で、**参照ループ**（入力 \(u_{tr}\)）では Lyapunov 残差 \(W\) の変化がゼロ。このとき、

- 残差 \(W\)（無明の大きさ）が**下降している**（無明がある）ならば、実際の入力 \(u_0\) と参照入力 \(u_{tr}\) の**差（行）は 0 でない**（(27.7)）。
- 下降の速さは、作用素を通した**勾配との内積** \(-\langle\nabla W,G(u_0-u_{tr})\rangle\) で**帰属**される（アクチュエータへの帰属の恒等式）。
- 制御差の大きさは**下から評価**される（(27.8)）：\(\|u_0-u_{tr}\|\ge\text{decayRate}\cdot W/L\)。
- 不変な目標（寂静の集合）に入った後は、残差の下降率は 0、アクチュエータの寄与も 0（(27.9)）。
- (27.10)：「目標の外 ⇔ アクチュエータの寄与が正」。

### 0.2 構成

| 節 | 宣言 |
| --- | --- |
| 行の寄与の定義 | `sankhara27Contribution` |
| 上右 Dini 微分 | `upperRightDiniDerivative` と、局所 Lipschitz・絶対連続からの評価・a.e. 等式 |
| 連鎖律 | `hasDerivAt_timeState_composition`, `hasDerivAt_joint_time_state`, `timeState_fderiv_decomposition`, `ae_hasDerivAt_pi_*` |
| 目標到達後のゼロ下降 (27.9) | `residual_has_right_derivative_zero_after_target_entry`, `..._zero_*`, `residualDescentRate_zero_after_target_entry` |
| 帰属の恒等式 | `closedLoop_descent_formula_*`, `actuator_identity_from_reference_cancellation` |
| 無明 ⇒ 行 (27.7) | `ae_ignorance_implies_model_relative_action*`, `ignorance_implies_*`, `positive_actuator_contribution` |
| 制御差の下界 (27.8) | `control_difference_norm_lower_bound*`, `ae_control_difference_*`, `outside_target_implies_*` |
| (27.10) 同値 | `outside_target_iff_positive_actuator_contribution`, `ae_outside_target_iff_*` |
| Fréchet 微分から勾配 | `stateGradientFromFDeriv*`, `jointDerivativeOnPath*`, `adjoint_norm_bound_*` |

### 0.3 このファイルが証明していないこと

- **モデル相対**の結論です：「行」が 0 でないことは、条件 27-A のモデル（制御アファイン・参照ループの相殺・Lyapunov 関数の微分可能性・減衰の仮定）のもとでの結論で、思想的な「行」の解釈とは別です。
- 参照ループの打ち消し（27.A2）、状態勾配の表現、作用素のノルム評価（定数 \(L\)）、Lyapunov の（Dini の）減衰、局所 Lipschitz・連続性などは、すべて**明示的な仮定**で、条件 27-A だけから導いてはいません。
- 状態と入力は別の内積空間でもよく、有限次元の Euclid 空間の絶対連続な軌道を扱う箇所があります。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 条件 27-A の制御入力・Dini 微分・定量的な散逸の補題。

名前空間は `Tomabechi.Theorem27.Actuator`。`open RealInnerProductSpace Filter Topology`。

---

<a id="Tomabechi.Theorem27.Actuator.sankhara27Contribution"></a>

## 定義 `sankhara27Contribution`

### 式

$$0<-\langle\nabla W,\ G(u_0-u_{tr})\rangle$$

### Lean のコメント（日本語訳）

> (27.5) の、モデル相対の形成の作用：参照を引いた入力が、Lyapunov の残差の下降に、厳密に正の寄与をもつ。

### 定義の説明

**行（サンカーラ）の寄与**：入力の差 \(u_0-u_{tr}\) が、作用素 \(G\) を通して、残差 \(W\) を**下げる向きに働いている**（\(-\langle\nabla W,G\Delta u\rangle>0\)）。

### 証明の概略

1. 定義：`0 < -(inner ℝ gradW (actuator controlDifference))`。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative"></a>

## 定義 `upperRightDiniDerivative`

### 式

$$\overline D^+f(t)=\limsup_{h\downarrow0}\frac{f(t+h)-f(t)}{h}$$

### Lean のコメント（日本語訳）

> 上右の Dini 微分。前向きの差分商の limsup として定義する。

### 定義の説明

関数の「右側から見た微分の上限」です。微分可能でなくても定義でき、論文の条件 26-A はこれで述べられます。

### 証明の概略

1. 定義：`limsup` を前向きの差分商に対して。

----

<a id="Tomabechi.Theorem27.Actuator.slope_isBoundedUnder_of_locallyLipschitz"></a>

## 補題 `slope_isBoundedUnder_of_locallyLipschitz`

### 式

$$f\ \text{局所 Lipschitz}\ \Longrightarrow\ \text{前向きの差分商は基点の近くで下に有界}$$

### Lean のコメント（日本語訳）

> 局所的な Lipschitz の正則性は、基点の近くで、前向きの差分商を下から抑える。これは、「厳密に最終的な」右の傾きの定義を、実数値の limsup の境界に変えるときに必要な、有界性の側である。

### 補題の説明

差分商の絶対値が Lipschitz 定数で抑えられるので有界です。

### 証明の概略

1. Lipschitz 条件 \(|f(t+h)-f(t)|\le L\,h\) から差分商 \(\ge-L\)。

----

<a id="Tomabechi.Theorem27.Actuator.slope_isBoundedUnder_of_locallyLipschitzOn_Ici"></a>

## 補題 `slope_isBoundedUnder_of_locallyLipschitzOn_Ici`

### 式

$$f\ \text{は}\ [T,\infty)\ \text{で局所 Lipschitz}\ \Longrightarrow\ \text{ray の各点で前向きの差分商が下に有界}$$

### Lean のコメント（日本語訳）

> 将来の半直線での、局所的な Lipschitz の正則性は、その半直線の任意の点で、前向きの傾きを、下から抑えるのに十分である。

### 補題の説明

上の補題の、半直線版です。

### 証明の概略

1. 同様。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_le_of_rightSlopeBound_of_lowerBound"></a>

## 補題 `upperRightDiniDerivative_le_of_rightSlopeBound_of_lowerBound`

### 式

$$\text{右傾きの評価}\ +\ \text{差分商の下界}\ \Longrightarrow\ \overline D^+f(t)\le\text{bound}$$

### Lean のコメント（日本語訳）

> 前向きの商の下界は、最終的な右の傾きの評価を、実数値の limsup の境界に変えるのに必要な、下からの有界性を供給する。これは、正確な補助の入力を切り出す：局所 Lipschitz 連続性は、それを与える十分な方法の 1 つだが、この変換自身には要らない。

### 補題の説明

「右傾きが bound 以下」を「上右 Dini 微分が bound 以下」に直す補題です（実数値の limsup にするため下界が要る）。

### 証明の概略

1. `limsup` の比較と有界性（`Filter.limsup_le_of_le`）。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_le_of_rightSlopeBound"></a>

## 補題 `upperRightDiniDerivative_le_of_rightSlopeBound`

### 式

$$f\ \text{局所 Lipschitz},\ \text{右傾き}\le\text{bound}\ \Longrightarrow\ \overline D^+f\le\text{bound}$$

### Lean のコメント（日本語訳）

> 局所 Lipschitz の経路は、下からの傾きの境界を与え、したがって、実数値の上右 Dini の評価を与える。

### 補題の説明

上の補題に、局所 Lipschitz から下界を与えた版です。

### 証明の概略

1. `slope_isBoundedUnder_of_locallyLipschitz` と上の補題。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_eq_of_hasDerivAt"></a>

## 補題 `upperRightDiniDerivative_eq_of_hasDerivAt`

### 式

$$f'(t)=f'\ \Longrightarrow\ \overline D^+f(t)=f'$$

### Lean のコメント（日本語訳）

> 微分可能な点では、上右 Dini 微分は、通常の導関数に等しい。

### 補題の説明

微分可能なら Dini 微分は普通の微分です。

### 証明の概略

1. 微分の定義：差分商の極限が \(f'\)、limsup はその極限に一致。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_eq_zero_of_hasDerivWithinAt"></a>

## 補題 `upperRightDiniDerivative_eq_zero_of_hasDerivWithinAt`

### 式

$$f'_+(t)=0\ (\text{右微分})\ \Longrightarrow\ \overline D^+f(t)=0$$

### Lean のコメント（日本語訳）

> 前向きの半直線の上の、零の右の導関数は、上右 Dini 微分が消えることを強制する。

### 補題の説明

右微分が 0 なら Dini 微分も 0 です。

### 証明の概略

1. `hasDerivWithinAt` の差分商の極限から。

----

<a id="Tomabechi.Theorem27.Actuator.ae_upperRightDiniDerivative_eq_deriv_on_interval"></a>

## 補題 `ae_upperRightDiniDerivative_eq_deriv_on_interval`

### 式

$$f\ \text{局所 Lipschitz}\ \Longrightarrow\ \overline D^+f=f'\ \ (\text{a.e. on}\ [a,b])$$

### Lean のコメント（日本語訳）

> 局所 Lipschitz なスカラーの残差の経路は、各コンパクトな区間のほとんど至るところで、通常の導関数をもつ。したがって、その上右 Dini 微分は、そこで、その通常の導関数とほとんど至るところ一致する。

### 補題の説明

Lipschitz 関数は a.e. 微分可能（Rademacher/Lebesgue の定理）です。

### 証明の概略

1. Lipschitz ⇒ 絶対連続 ⇒ a.e. 微分可能。微分可能な点で Dini 微分 = 微分（上の補題）。

----

<a id="Tomabechi.Theorem27.Actuator.ae_upperRightDiniDerivative_eq_deriv"></a>

## 補題 `ae_upperRightDiniDerivative_eq_deriv`

### 式

$$f\ \text{局所 Lipschitz}\ \Longrightarrow\ \overline D^+f=f'\ \ (\text{a.e. on}\ \mathbb R)$$

### Lean のコメント（日本語訳）

> 局所 Lipschitz の残差の経路は、実数直線の全体のほとんど至るところで、上右 Dini 微分と通常の導関数が一致する。証明は、\(\mathbb R\) を可算個のコンパクトな区間で覆い、各区間で絶対連続性を適用する。

### 補題の説明

区間ごとの a.e. を、可算個の区間でまとめます。

### 証明の概略

1. `ℝ = ⋃ₙ [-n,n]` と 可算個の a.e. 条件の共通部分（`MeasureTheory.ae_all_iff`）。

----

<a id="Tomabechi.Theorem27.Actuator.ae_upperRightDiniDerivative_eq_deriv_on_future"></a>

## 補題 `ae_upperRightDiniDerivative_eq_deriv_on_future`

### 式

$$f\ \text{は}\ [T,\infty)\ \text{で局所 Lipschitz}\ \Longrightarrow\ \overline D^+f=f'\ \ (\mathrm{Leb}|_{[T,\infty)}\text{-a.e.})$$

### Lean のコメント（日本語訳）

> 将来の領域の版：局所 Lipschitz の正則性は、\([T,\infty)\) でだけ要り、初期時刻から先に指定される軌道に合う。

### 補題の説明

将来の半直線だけで成り立つ版です。

### 証明の概略

1. 上の補題を、区間 \([T,n]\) で適用。

----

<a id="Tomabechi.Theorem27.Actuator.lipschitzOn_Icc_of_absolutelyContinuousOnInterval_of_ae_deriv_bound"></a>

## 補題 `lipschitzOn_Icc_of_absolutelyContinuousOnInterval_of_ae_deriv_bound`

### 式

$$f\ \text{絶対連続},\ |f'|\le C\ \text{a.e.}\ \Longrightarrow\ f\ \text{は}\ [a,b]\ \text{で}\ C\text{-Lipschitz}$$

### Lean のコメント（日本語訳）

> 本質的に有界な導関数をもつ、絶対連続なスカラー関数は、その区間で Lipschitz である。これは、有界な 27-A のデータから、将来の局所 Lipschitz の正則性を得るのに使う、有限区間の橋である。

### 補題の説明

絶対連続関数は導関数の積分で書けるので、導関数が有界なら Lipschitz です。

### 証明の概略

1. \(f(t)-f(s)=\int_s^tf'\) と \(|f'|\le C\)。

----

<a id="Tomabechi.Theorem27.Actuator.locallyLipschitzOn_Ici_of_absolutelyContinuous_of_local_deriv_bound"></a>

## 補題 `locallyLipschitzOn_Ici_of_absolutelyContinuous_of_local_deriv_bound`

### 式

$$f\ \text{絶対連続},\ |f'|\le C_b\ \text{on every}\ [T,b]\ \Longrightarrow\ \text{LocallyLipschitzOn}\ [T,\infty)$$

### Lean のコメント（日本語訳）

> 絶対連続な将来の残差が、すべての有限の将来の区間で、本質的に有界な導関数をもつなら、将来の半直線の全体で、局所 Lipschitz である。

### 補題の説明

上の補題を各 \([T,b]\) で使います。

### 証明の概略

1. 各点の近傍をある \([T,b]\) に入れる。

----

<a id="Tomabechi.Theorem27.Actuator.ae_differentiableAt_pi_of_absolutelyContinuousOnInterval"></a>

## 補題 `ae_differentiableAt_pi_of_absolutelyContinuousOnInterval`

### 式

$$x:\mathbb R\to\mathbb R^n\ \text{絶対連続}\ \Longrightarrow\ x\ \text{は a.e. 微分可能}$$

### Lean のコメント（日本語訳）

> 有限次元の実座標の経路の絶対連続性は、ベクトルの経路の、ほとんど至るところの微分可能性を意味する。証明は、スカラーの絶対連続性の定理を、各座標の射影に適用し、`differentiableAt_pi` で微分可能性を組み立て直す。

### 補題の説明

各成分が a.e. 微分可能なら、ベクトル値関数も a.e. 微分可能です（有限個の成分の a.e. の共通部分）。

### 証明の概略

1. 各座標で絶対連続 ⇒ a.e. 微分可能、`differentiableAt_pi` でまとめる。

----

<a id="Tomabechi.Theorem27.Actuator.ae_hasDerivAt_pi_of_ac_and_ode"></a>

## 補題 `ae_hasDerivAt_pi_of_ac_and_ode`

### 式

$$x\ \text{絶対連続}\ +\ \dot x=v\ \text{a.e.}\ \Longrightarrow\ \text{HasDerivAt}\ x\ v\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 有限次元の状態の軌道が、各コンパクトな区間で絶対連続で、制御アファインの ODE をほとんど至るところ満たすなら、連鎖律が必要とする `HasDerivAt` の形が、ほとんど至るところ成り立つ。

### 補題の説明

a.e. で微分可能で、微分 `deriv x t = velocity t` なので `HasDerivAt x (velocity t) t` です。

### 証明の概略

1. `ae_differentiableAt_pi_of_absolutelyContinuousOnInterval` と ODE の a.e. 等式から `DifferentiableAt.hasDerivAt`。

----

<a id="Tomabechi.Theorem27.Actuator.ae_hasDerivAt_pi_on_future_of_ac_and_ode"></a>

## 補題 `ae_hasDerivAt_pi_on_future_of_ac_and_ode`

### 式

$$\text{将来の ray 版}$$

### Lean のコメント（日本語訳）

> 条件 27-A に合う、将来の半直線の版：コンパクトな区間での絶対連続性が、a.e. の微分可能性を供給し、ODE の等式は、\([T,\infty)\) の a.e. でだけ要る。

### 補題の説明

上の補題の将来の半直線の版です。

### 証明の概略

1. 同様。

----

<a id="Tomabechi.Theorem27.Actuator.hasDerivAt_timeState_composition"></a>

## 補題 `hasDerivAt_timeState_composition`

### 式

$$\frac d{dt}W(t,x(t))=dW(1,\dot x)$$

### Lean のコメント（日本語訳）

> 微分可能な状態の曲線に沿った、時間に依存する Lyapunov 関数の連鎖律。時間-状態の合成曲線の導関数は、明示的に供給されるので、この補題は、アクチュエータへの帰属の結果が使う、閉ループの導関数の公式を仮定しない。

### 補題の説明

時間と状態の両方に依存する \(W(t,x)\) の軌道に沿った微分は、全微分 \(dW\) に速度 \((1,\dot x)\) を代入したものです。

### 証明の概略

1. `HasFDerivAt.comp_hasDerivAt`（合成関数の微分）。

----

<a id="Tomabechi.Theorem27.Actuator.hasDerivAt_joint_time_state"></a>

## 補題 `hasDerivAt_joint_time_state`

### 式

$$\frac d{dt}(t,x(t))=(1,\dot x(t))$$

### Lean のコメント（日本語訳）

> 時間の導関数と状態の導関数を、連鎖律が必要とする、時間-状態の同時速度に組み立てる。

### 補題の説明

組 \((t,x(t))\) の微分は \((1,\dot x)\) です。

### 証明の概略

1. `hasDerivAt_id` と状態の微分を `HasDerivAt.prodMk`。

----

<a id="Tomabechi.Theorem27.Actuator.timeState_fderiv_decomposition"></a>

## 補題 `timeState_fderiv_decomposition`

### 式

$$dW(1,v)=dW(1,0)+\langle\nabla W,v\rangle$$

### Lean のコメント（日本語訳）

> 時空間の Fréchet 微分を、その時間成分と、状態の勾配の対に分解する。

### 補題の説明

全微分は線形なので、時間成分 \(dW(1,0)\) と状態成分 \(dW(0,v)=\langle\nabla W,v\rangle\) の和です。

### 証明の概略

1. \((1,v)=(1,0)+(0,v)\) と線形性、状態成分の勾配表現。

----

<a id="Tomabechi.Theorem27.Actuator.residual_has_right_derivative_zero_after_target_entry"></a>

## 補題 `residual_has_right_derivative_zero_after_target_entry`

### 式

$$\text{目標が前向き不変},\ W=0\ \text{on target},\ x(t)\in N(t)\ \Longrightarrow\ (W(s,x(s)))'_+=0$$

### Lean のコメント（日本語訳）

> 時間に依存する目標の前向きの不変性と、その目標の上での零の Lyapunov の残差は、目標への進入後の軌道に沿った残差が、零の右の導関数をもつことを強制する。これは、式 (27.9) の零下降の部分の、微積分の内容である。

### 補題の説明

目標に入ったら（不変なので）ずっと目標の中、目標の上では \(W=0\) なので、残差はずっと 0、右微分も 0 です。

### 証明の概略

1. \(s\ge t\) で \(W(s,x(s))=0\)（目標内）。定数の右微分は 0（`HasDerivWithinAt` の局所一致）。

----

<a id="Tomabechi.Theorem27.Actuator.upperRightDiniDerivative_zero_on_invariant_target"></a>

## 補題 `upperRightDiniDerivative_zero_on_invariant_target`

### 式

$$\overline D^+(W(s,x(s)))(t)=0\quad(t\ge\text{進入時刻})$$

### Lean のコメント（日本語訳）

> 目標の上での前向きの不変性と零の残差は、目標への進入の瞬間から先、上右 Dini 微分が消えることを強制する。

### 補題の説明

上の補題の Dini 版です。

### 証明の概略

1. `upperRightDiniDerivative_eq_zero_of_hasDerivWithinAt`。

----

<a id="Tomabechi.Theorem27.Actuator.residual_derivative_zero_after_target_entry"></a>

## 補題 `residual_derivative_zero_after_target_entry`

### 式

$$t>\text{進入時刻},\ \text{微分可能}\ \Longrightarrow\ \text{derivative}=0$$

### Lean のコメント（日本語訳）

> 目標への進入の厳密に後の時刻では、将来の消失が、残差の経路の、通常の導関数を零にする。

### 補題の説明

進入後は残差が定数 0 の区間にいるので、普通の微分も 0 です。

### 証明の概略

1. 残差が \(t\) の近傍（\(t>\)進入時刻）で 0 の定数。

----

<a id="Tomabechi.Theorem27.Actuator.closedLoop_descent_formula_of_chain_rule"></a>

## 補題 `closedLoop_descent_formula_of_chain_rule`

### 式

$$\text{descentRate}=-\langle\nabla W,G(u_0-u_{tr})\rangle$$

### Lean のコメント（日本語訳）

> 時間-状態の連鎖律と、制御アファインの速度から、閉ループの Lyapunov の導関数を導く。`hsplit` は、Fréchet 微分の、その明示的な時間の導関数と状態の勾配への、通常の分解である。

### 補題の説明

**アクチュエータへの帰属の恒等式**：残差の下降率は、入力の差 \(u_0-u_{tr}\) をアクチュエータ \(G\) に通したものと勾配の内積（の符号反転）に等しい。参照ループ（入力 \(u_{tr}\)）では \(W\) の変化が 0 であることを使い、引き算します。

### 証明の概略

1. 連鎖律：\(\dot W=dW(1,\text{drift}+Gu_0)\)。
2. 分解：\(=dW(1,0)+\langle\nabla W,\text{drift}+Gu_0\rangle\)。
3. 参照ループ（27.A2）：\(dW(1,0)+\langle\nabla W,\text{drift}+Gu_{tr}\rangle=0\)。差をとって \(\dot W=\langle\nabla W,G(u_0-u_{tr})\rangle\)、下降率はその符号反転。

----

<a id="Tomabechi.Theorem27.Actuator.ae_closedLoop_descent_formula_of_ode_under_measure"></a>

## 補題 `ae_closedLoop_descent_formula_of_ode_under_measure`

### 式

$$-\tfrac d{dt}W=-\langle\nabla W,G(u_0-u_{tr})\rangle\quad\mu\text{-a.e.}$$

### Lean のコメント（日本語訳）

> 時間に依存する制御とアクチュエータの写像についての、連鎖律の帰属の恒等式の、ほとんど至るところの版。ODE と参照ループの相殺は、条件 27-A に合わせて、ほとんど至るところで仮定される。Lyapunov 関数は、軌道の全体に沿って Fréchet 微分可能である。

### 補題の説明

上の恒等式の、a.e. 版（任意の測度）です。

### 証明の概略

1. 各時刻で上の補題を適用（a.e. の条件を `filter_upwards` で集める）。

----

<a id="Tomabechi.Theorem27.Actuator.future_residual_derivative_bound_of_attribution"></a>

## 補題 `future_residual_derivative_bound_of_attribution`

### 式

$$|\langle\nabla W,G\Delta u\rangle|\le C\ \Longrightarrow\ |(\text{residual})'|\le C$$

### Lean のコメント（日本語訳）

> 27-A の導関数の帰属は、アクチュエータの寄与の局所的な本質的な境界を、残差の導関数の局所的な本質的な境界に移す。

### 補題の説明

帰属の恒等式から、導関数の評価が内積の評価に移ります。

### 証明の概略

1. `-(deriv q t) = -(pairing t)` から絶対値が等しい。

----

<a id="Tomabechi.Theorem27.Actuator.future_pairing_ae_bound_of_continuousOn"></a>

## 補題 `future_pairing_ae_bound_of_continuousOn`

### 式

$$\text{pairing}\ \text{連続}\ \Longrightarrow\ \text{各コンパクトな将来区間で有界}$$

### Lean のコメント（日本語訳）

> 連続なアクチュエータ-残差の対は、各コンパクトな将来の区間で有界であり、将来の半直線の正則性のアダプタが使う、局所的な本質的な境界の入力を供給する。連続性は、モデルの正則性の条件であり、条件 27-A だけから推論されない。

### 補題の説明

コンパクト集合上の連続関数は有界です。

### 証明の概略

1. `IsCompact.exists_bound_of_continuousOn`。

----

<a id="Tomabechi.Theorem27.Actuator.future_inner_ae_bound_of_continuousOn"></a>

## 補題 `future_inner_ae_bound_of_continuousOn`

### 式

$$\nabla W,\ \text{actuated residual}\ \text{連続}\ \Longrightarrow\ \langle\nabla W,\cdot\rangle\ \text{有界}$$

### Lean のコメント（日本語訳）

> 勾配と作用した制御差の局所的な連続性は、それらの対の局所的な本質的な境界のための、成分ごとの十分条件である。

### 補題の説明

成分の連続性から内積の連続性、上の補題。

### 証明の概略

1. 内積の連続性（`Continuous.inner`）と上の補題。

----

<a id="Tomabechi.Theorem27.Actuator.ae_closedLoop_descent_formula_of_ode"></a>

## 補題 `ae_closedLoop_descent_formula_of_ode`

### 式

$$\text{帰属の恒等式}\ (\mathrm{Leb}\text{-a.e.})$$

### Lean のコメント（日本語訳）

> 測度に一般の恒等式の、Lebesgue の a.e. の互換ラッパー。

### 補題の説明

任意の測度版の Lebesgue 測度への特殊化です。

### 証明の概略

1. `ae_closedLoop_descent_formula_of_ode_under_measure` を `volume` で。

----

<a id="Tomabechi.Theorem27.Actuator.ae_closedLoop_descent_formula_of_ac_ode"></a>

## 補題 `ae_closedLoop_descent_formula_of_ac_ode`

### 式

$$x\ \text{絶対連続}\ +\ \text{制御アファインの ODE a.e.}\ \Longrightarrow\ \text{帰属の恒等式 a.e.}$$

### Lean のコメント（日本語訳）

> 条件 27-A の、絶対連続な有限次元の軌道と、ほとんど至るところの制御アファインの ODE は、連鎖律による帰属の定理で使う導関数の前提を与える。残りの仮定は、状態の勾配の表現と、参照ループの相殺 (27.A2) であり、どちらも a.e. である。

### 補題の説明

`HasDerivAt` の仮定を、**絶対連続性と ODE** から導いた版です。

### 証明の概略

1. `ae_hasDerivAt_pi_of_ac_and_ode` で微分を得て、上の補題を適用。

----

<a id="Tomabechi.Theorem27.Actuator.ae_actuator_contribution_zero_on_invariant_target"></a>

## 補題 `ae_actuator_contribution_zero_on_invariant_target`

### 式

$$\text{不変な目標の上では}\ \langle\nabla W,G(u_0-u_{tr})\rangle=0\ \ \text{a.e.}$$

### Lean のコメント（日本語訳）

> ほとんど至るところ、アクチュエータの寄与は、前向きに不変な零残差の目標の上で消える。主張は、点ごとの Dini の議論に目標への進入の瞬間を含み、a.e. の結論が、そのとき、通常の連鎖律に接続する。

### 補題の説明

目標の上では残差が定数 0 なので下降率が 0、帰属の恒等式から寄与も 0 です。

### 証明の概略

1. `upperRightDiniDerivative_zero_on_invariant_target` と a.e. 一致（`ae_upperRightDiniDerivative_eq_deriv`）、帰属の恒等式。

----

<a id="Tomabechi.Theorem27.Actuator.residualDescentRate_zero_after_target_entry"></a>

## 定理 `residualDescentRate_zero_after_target_entry`

### 式

$$t\ge\text{進入時刻}\ \Longrightarrow\ -\overline D^+(W(s,x(s)))(t)=0$$

### Lean のコメント（日本語訳）

> 式 (27.9)、第 1 の結論：軌道が、前向きに不変な零残差の目標に入ったあとは、その残差の下降率は、進入の時刻を含む、すべての後の時刻で零である。

### 補題の説明

**(27.9) 第 1**：寂静の集合に入ったら、残差はもう下がりません（すでに 0）。

### 証明の概略

1. `upperRightDiniDerivative_zero_on_invariant_target` の符号反転。

----

<a id="Tomabechi.Theorem27.Actuator.ae_actuator_contribution_zero_after_target_entry"></a>

## 定理 `ae_actuator_contribution_zero_after_target_entry`

### 式

$$\text{進入後}\ (t\ge T):\ \langle\nabla W,G(u_0-u_{tr})\rangle=0\ \ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 式 (27.9)、第 2 の結論：目標への進入のあとの、前向きの半直線の上で、アクチュエータの残差への寄与は、ほとんど至るところ消える。

### 補題の説明

**(27.9) 第 2**：寂静に入ったら、**行（アクチュエータの寄与）も消える**。

### 証明の概略

1. Dini 微分が a.e. で通常の導関数に一致する（局所 Lipschitz、`ae_upperRightDiniDerivative_eq_deriv`）。
2. 連鎖律の公式 `ae_closedLoop_descent_formula_of_ode`（導関数 = 行の寄与の符号反転）を a.e. で得る。
3. 目標に入った後の時刻 \(t\ge T\) では、前向き不変性で軌道が目標上にあり、残差が 0 なので Dini 微分が 0（`upperRightDiniDerivative_zero_on_invariant_target`）。これらから行の寄与 \(=0\)（30 行）。

----

<a id="Tomabechi.Theorem27.Actuator.ae_actuator_contribution_zero_after_target_entry_on_future"></a>

## 定理 `ae_actuator_contribution_zero_after_target_entry_on_future`

### 式

$$(\mathrm{Leb}|_{[T,\infty)}\text{-a.e.})\ \langle\nabla W,G(u_0-u_{tr})\rangle=0$$

### Lean のコメント（日本語訳）

> アクチュエータの静止の含意の、将来の測度の版。正則性と 27-A の連鎖律のデータは、進入で始まる半直線の上でだけ要る。

### 補題の説明

将来の半直線だけの仮定で成り立つ版です。

### 証明の概略

1. 上の定理の将来版。

----

<a id="Tomabechi.Theorem27.Actuator.ae_ignorance_implies_model_relative_action"></a>

## 定理 `ae_ignorance_implies_model_relative_action`

### 式

$$\text{a.e.}:\ 0<-\langle\nabla W,G\Delta u\rangle\ \wedge\ \Delta u\neq0\ \wedge\ G\Delta u\neq0$$

### Lean のコメント（日本語訳）

> 式 (27.7) のほとんど至るところの版：条件 26-A が、ほとんど至るところ、正の残差と、厳密な減衰を供給し、条件 27-A の ODE と参照ループの仮定が、ほとんど至るところ、アクチュエータへの帰属の恒等式を与える。

### 補題の説明

**(27.7)**：無明（残差が正で下降している）なら、**行**（入力の差 \(\Delta u=u_0-u_{tr}\)）は 0 でなく、その作用も 0 でない。

### 証明の概略

1. 帰属の恒等式 \(\text{descentRate}=-\langle\nabla W,G\Delta u\rangle\)、厳密減衰 \(\text{decayRate}\cdot W\le\text{descentRate}\)、\(W>0\) から寄与が正。
2. 寄与が正なら \(G\Delta u\neq0\)、したがって \(\Delta u\neq0\)（線形性）。

----

<a id="Tomabechi.Theorem27.Actuator.ae_ignorance_implies_model_relative_action_of_dini"></a>

## 定理 `ae_ignorance_implies_model_relative_action_of_dini`

### 式

$$\text{減衰の仮定が上右 Dini 微分}\ \Longrightarrow\ (27.7)\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 減衰の前提に、論文の上右 Dini 微分を使う、a.e. の形の (27.7)。残差の経路の局所 Lipschitz の正則性が、その Dini 微分と通常の導関数のほとんど至るところの等式を供給する。

### 補題の説明

論文の Dini 版の減衰条件を使います。

### 証明の概略

1. `ae_upperRightDiniDerivative_eq_deriv` で Dini 微分を通常の微分に置き換え、上の定理を適用。

----

<a id="Tomabechi.Theorem27.Actuator.ae_ignorance_implies_model_relative_action_of_ac_ode"></a>

## 定理 `ae_ignorance_implies_model_relative_action_of_ac_ode`

### 式

$$x\ \text{絶対連続}\ +\ \text{ODE a.e.}\ \Longrightarrow\ (27.7)$$

### Lean のコメント（日本語訳）

> 論文の有限次元の Euclid 状態空間について、条件 27-A の絶対連続な軌道と a.e. の ODE から、直接得られる式 (27.7)。これは、残差の作用の結論から、別の a.e. の `HasDerivAt` の前提を除く。

### 補題の説明

`HasDerivAt` の仮定を絶対連続性と ODE から導いた版です。

### 証明の概略

1. `ae_hasDerivAt_pi_of_ac_and_ode` と上の定理。

----

<a id="Tomabechi.Theorem27.Actuator.ae_control_difference_norm_lower_bound_of_dini"></a>

## 定理 `ae_control_difference_norm_lower_bound_of_dini`

### 式

$$\|G^\dagger\nabla W\|\le L\ \Longrightarrow\ \|u_0-u_{tr}\|\ge\frac{\text{decayRate}\cdot W}{L}\ \ \text{a.e.}$$

### Lean のコメント（日本語訳）

> Dini の下降と随伴の勾配の境界からの、ほとんど至るところのノルムの評価 (27.8)。随伴の対の恒等式は、すでに証明された a.e. の連鎖律が与え、Dini から通常の導関数への段階は、局所 Lipschitz の正則性が与える。

### 補題の説明

**(27.8)**：制御差の大きさは、残差と減衰率に比例して下から評価されます（\(L\) は作用素 \(G^\dagger\nabla W\) のノルムの上界）。

### 証明の概略

1. Cauchy–Schwarz：\(\text{descentRate}=-\langle G^\dagger\nabla W,\Delta u\rangle\le\|G^\dagger\nabla W\|\|\Delta u\|\le L\|\Delta u\|\)。
2. \(\text{descentRate}\ge\text{decayRate}\cdot W\)。

----

<a id="Tomabechi.Theorem27.Actuator.ae_control_difference_norm_lower_bound_of_dini_of_ac_ode"></a>

## 定理 `ae_control_difference_norm_lower_bound_of_dini_of_ac_ode`

### 式

$$\text{絶対連続・ODE a.e.}\ \Longrightarrow\ (27.8)$$

### Lean のコメント（日本語訳）

> 条件 27-A の絶対連続な有限次元の軌道と a.e. の制御アファインの ODE からの、式 (27.8) の残差に基づく制御の境界。随伴の勾配の境界は、述べられた定数 \(L\) の前提である。

### 補題の説明

(27.8) を絶対連続性と ODE から直接導く版です。

### 証明の概略

1. 上の定理に `ae_hasDerivAt_pi_of_ac_and_ode` を使う。

----

<a id="Tomabechi.Theorem27.Actuator.ae_control_difference_distance_lower_bound_of_dini_of_ac_ode"></a>

## 定理 `ae_control_difference_distance_lower_bound_of_dini_of_ac_ode`

### 式

$$\|u_0-u_{tr}\|\ge\frac{\text{decayRate}\cdot c_1\cdot d(x,N)^2}{L}\ \wedge\ (x\notin N\Rightarrow\|u_0-u_{tr}\|>0)$$

### Lean のコメント（日本語訳）

> (26.A) からの距離の項をもつ式 (27.8)：ノルムの評価は、絶対連続な ODE の軌道から、ほとんど至るところ得られ、状態が閉の零残差の目標の外にあるときはいつでも、厳密に正である。

### 補題の説明

制御差の下界を、**目標までの距離の 2 乗**で書き直した版です（\(W\ge c_1d^2\)）。目標の外では必ず正（行が必要）。

### 証明の概略

1. 上の定理と \(W\ge c_1d(x,N)^2\)（26-A）。

----

<a id="Tomabechi.Theorem27.Actuator.actuator_identity_from_reference_cancellation"></a>

## 補題 `actuator_identity_from_reference_cancellation`

### 式

$$\text{descentRate}=-\langle\nabla W,G(u_0-u_{tr})\rangle$$

### Lean のコメント（日本語訳）

> 参照ループの相殺と、閉ループの導関数の連鎖律の表現は、アクチュエータへの帰属の恒等式を意味する。状態と入力は、別の実内積空間でもよい。

### 補題の説明

`closedLoop_descent_formula_of_chain_rule` の純代数版（連鎖律の結論を `hchain` として受け取る）です。

### 証明の概略

1. 代数計算（`linarith`、`inner_sub_right`、`map_sub`）。

----

<a id="Tomabechi.Theorem27.Actuator.actuator_contribution_zero_after_target_entry"></a>

## 補題 `actuator_contribution_zero_after_target_entry`

### 式

$$\text{進入後の各微分可能な時刻で}\ \langle\nabla W,G(u_0-u_{tr})\rangle=0$$

### Lean のコメント（日本語訳）

> 前向きに不変な零残差の目標に入ったあと、残差の経路は、将来で消える。制御アファインの軌道が微分可能な、すべての後の時刻で、連鎖律と参照ループの相殺が、アクチュエータの残差への寄与を、したがって零にする。これは、(27.9) の a.e. の結論の基礎にある、進入後の点ごとの形である。

### 補題の説明

進入後の点ごとの形です。

### 証明の概略

1. 進入後は残差が 0 の定数なので導関数が 0、帰属の恒等式から寄与も 0。

----

<a id="Tomabechi.Theorem27.Actuator.positive_actuator_contribution"></a>

## 補題 `positive_actuator_contribution`

### 式

$$\text{descentRate}>0\ \Longrightarrow\ 0<-\langle\nabla W,G\Delta u\rangle\ \wedge\ \Delta u\neq0\ \wedge\ G\Delta u\neq0$$

### Lean のコメント（日本語訳）

> 条件 27-A のアクチュエータの帰属の部分の、代数的な帰結。恒等式 \(\text{descentRate}=-\langle\nabla W,G\eta\rangle\) は、参照の閉ループの Lyapunov の導関数が零のあとの、連鎖律の結論である。

### 補題の説明

下降率が正なら、寄与が正で、したがって \(\Delta u\ne0\)、\(G\Delta u\ne0\) です（0 のベクトルの内積は 0）。

### 証明の概略

1. 恒等式と下降率 > 0。\(\Delta u=0\) なら寄与 0 で矛盾、\(G\Delta u=0\) でも同様。

----

<a id="Tomabechi.Theorem27.Actuator.outside_target_iff_positive_actuator_contribution"></a>

## 定理 `outside_target_iff_positive_actuator_contribution`

### 式

$$x\notin N\ \Longleftrightarrow\ 0<-\langle\nabla W,G\Delta u\rangle$$

### Lean のコメント（日本語訳）

> (27.10) の、操作的な無明と、正のアクチュエータの寄与との、点ごとの同値。参照ループの恒等式が帰属を与え、不変な目標の上での零下降の性質が、逆の向きを与える。

### 補題の説明

**(27.10)**：目標の外（無明）⇔ 行の寄与が正。

### 証明の概略

1. （→）目標の外なら下降率が正（`residual_descent_of_outside_closed_target`）。帰属の恒等式 `hactuator` で、下降率 \(=-\langle\nabla W,G\Delta u\rangle\) なので行の寄与が正。
2. （←）寄与が正なら、目標の上（\(x\in N\)）では下降率が 0（`hzero`）なので寄与が 0 となり矛盾。よって目標の外（24 行）。

----

<a id="Tomabechi.Theorem27.Actuator.ae_outside_target_iff_positive_actuator_contribution_of_dini"></a>

## 定理 `ae_outside_target_iff_positive_actuator_contribution_of_dini`

### 式

$$\text{a.e.}\ t:\ x(t)\notin N(t)\ \Longleftrightarrow\ \text{sankhara27Contribution}$$

### Lean のコメント（日本語訳）

> 時間に依存する目標と、ほとんどすべての時刻についての、(27.10) の 2 番目の同値。厳密な残差の減衰が、目標の外での正のアクチュエータの寄与を与え、前向きの不変性と零の残差が、逆を与える。

### 補題の説明

(27.10) の a.e. の時間依存版です。

### 証明の概略

1. Dini 微分が a.e. で通常の導関数に一致（`ae_upperRightDiniDerivative_eq_deriv`）し、連鎖律の公式（`ae_closedLoop_descent_formula_of_ode`）で下降率が行の寄与（`sankhara27Contribution`）に等しい（a.e.）。
2. 目標の外では下降率が正、目標の上では不変性から Dini 微分が 0（`upperRightDiniDerivative_zero_on_invariant_target`）。これらから a.e. で「目標の外 ⇔ 行の寄与が正」（60 行）。

----

<a id="Tomabechi.Theorem27.Actuator.ignorance_implies_model_relative_action"></a>

## 定理 `ignorance_implies_model_relative_action`

### 式

$$\text{strict descent}\ +\ \text{零変動の参照ループ}\ \Longrightarrow\ 0<-\langle\nabla W,G\Delta u\rangle\ \wedge\ \Delta u\neq0\ \wedge\ G\Delta u\neq0$$

### Lean のコメント（日本語訳）

> 式 (27.7) の 2 段階の含意の統合した形：厳密な Lyapunov の下降と、零変動の参照ループが、非零のアクチュエータの寄与と、非零の入力/状態の作用を強制する。

### 補題の説明

(27.7) の点ごとの形です。

### 証明の概略

1. `actuator_identity_from_reference_cancellation` と `positive_actuator_contribution`。

----

<a id="Tomabechi.Theorem27.Actuator.ignorance_implies_action_of_control_affine_chain_rule"></a>

## 定理 `ignorance_implies_action_of_control_affine_chain_rule`

### 式

$$\text{制御アファインの軌道の連鎖律}\ \Longrightarrow\ \Delta u\neq0\ \wedge\ G\Delta u\neq0$$

### Lean のコメント（日本語訳）

> 微分可能な制御アファインの軌道からの、エンドツーエンドのアクチュエータの帰属。厳密な Lyapunov の減衰と、零の Lyapunov の変動をもつ参照ループが与えられると、連鎖律が入力の差の恒等式を導き、そして、入力の差と、その有効な状態への作用が、どちらも非零であることを証明する。これは、示した軌道・導関数の分解・Lyapunov の減衰の仮定を条件とする。

### 補題の説明

連鎖律を使って恒等式まで導く、(27.7) のエンドツーエンド版です。

### 証明の概略

1. `closedLoop_descent_formula_of_chain_rule` で恒等式、`positive_actuator_contribution`。

----

<a id="Tomabechi.Theorem27.Actuator.outside_target_implies_quantitative_descent_and_action"></a>

## 定理 `outside_target_implies_quantitative_descent_and_action`

### 式

$$x_0\notin N\ \Longrightarrow\ \text{decayRate}\,c_1d(x_0,N)^2\le\text{descentRate}\ \wedge\ 0<-\langle\nabla W,G\Delta u\rangle\ \wedge\ \Delta u\neq0\ \wedge\ G\Delta u\neq0$$

### Lean のコメント（日本語訳）

> 閉の零残差の目標の外の状態での、含意 (27.6)--(27.7) の統合。Lyapunov の下側の評価と減衰の不等式が、定量的な距離の下降と、その厳密な正値性を与え、制御アファインの連鎖律と参照ループの相殺が、その下降を、非零のアクチュエータの入力の差と、非零の有効な状態への作用に帰属させる。

### 補題の説明

**(27.6)+(27.7)**：目標の外にいるなら、定量的に下降し、その下降は非零の行に帰属される。

### 証明の概略

1. `residual_descent_of_outside_closed_target`（Abstract）で、目標の外なら下降率 \(\ge\)`decayRate`\(\cdot c_1d^2>0\)。
2. \(d=\mathrm{dist}(x_0,N)>0\)（閉・非空な目標の外）なので残差 \(W>0\)。
3. `ignorance_implies_action_of_control_affine_chain_rule` に、制御アファインの連鎖律と上の評価を渡して、行の寄与が正、\(u_0-u_{\rm tr}\ne0\)、\(G(u_0-u_{\rm tr})\ne0\) を得る（41 行）。

----

<a id="Tomabechi.Theorem27.Actuator.control_difference_norm_lower_bound"></a>

## 補題 `control_difference_norm_lower_bound`

### 式

$$\|G^\dagger\nabla W\|\le L\ \Longrightarrow\ \frac{\text{decayRate}\cdot W}{L}\le\|\Delta u\|$$

### Lean のコメント（日本語訳）

> 式 (27.8) の境界 \(\|G^\dagger\nabla W\|\le L\) を仮定した、制御差の定量的な下界。随伴の対の恒等式は、仮定として明示的に述べられ、したがって、この補題は、ノルムの評価を切り出す。

### 補題の説明

Cauchy–Schwarz です。

### 証明の概略

1. \(\text{decayRate}\,W\le-\langle G^\dagger\nabla W,\Delta u\rangle\le\|G^\dagger\nabla W\|\|\Delta u\|\le L\|\Delta u\|\)。

----

<a id="Tomabechi.Theorem27.Actuator.control_difference_norm_lower_bound_of_actuator_identity"></a>

## 補題 `control_difference_norm_lower_bound_of_actuator_identity`

### 式

$$\text{帰属の恒等式}\ \Longrightarrow\ \text{(27.8) のノルムの評価}$$

### Lean のコメント（日本語訳）

> アクチュエータの帰属の恒等式からの、式 (27.8) のノルムの評価。Cauchy–Schwarz が要る随伴の対は、追加の仮定ではなく、Mathlib の連続線形写像の随伴の恒等式から導かれる。

### 補題の説明

上の補題の、随伴の対の恒等式を自動的に導く版です。

### 証明の概略

1. `ContinuousLinearMap.adjoint_inner_left` と上の補題。

----

<a id="Tomabechi.Theorem27.Actuator.outside_target_implies_descent_action_and_control_bound"></a>

## 定理 `outside_target_implies_descent_action_and_control_bound`

### 式

$$\text{(27.6)--(27.8)}\ \text{の統合}$$

### Lean のコメント（日本語訳）

> 閉の零残差の目標の外の状態での、定量的な結論 (27.6)--(27.8) の統合。最後の制御の大きさの評価は、随伴のアクチュエータ-勾配の対の、作用素ノルムの境界を使う。

### 補題の説明

目標の外：定量的な下降・行は非零・制御差のノルムの下界、をまとめます。

### 証明の概略

1. `outside_target_implies_quantitative_descent_and_action` と `control_difference_norm_lower_bound_of_actuator_identity`。

----

<a id="Tomabechi.Theorem27.Actuator.stateGradientFromFDeriv"></a>

## 定義 `stateGradientFromFDeriv`

### 式

$$\nabla_xW\ :\ \langle\nabla_xW,z\rangle=dW(0,z)$$

### Lean のコメント（日本語訳）

> \(W\) の状態座標の導関数の、Riesz の代表元。

### 定義の説明

全微分の状態成分を、内積で表すベクトルとして取り出します。

### 証明の概略

1. 定義：Riesz 表現（`InnerProductSpace.toDual.symm`）。

----

<a id="Tomabechi.Theorem27.Actuator.jointDerivativeOnPath"></a>

## 定義 `jointDerivativeOnPath`

### 式

$$dW\ \text{(軌道}\ (t,x(t))\ \text{での全 Fréchet 微分)}$$

### Lean のコメント（日本語訳）

> 指定した軌道に沿った、時間に依存するポテンシャルの、標準的な同時 Fréchet 微分。

### 定義の説明

軌道上の各点での \(W\) の全微分です（連鎖律に使う）。

### 証明の概略

1. 定義：`fderiv ℝ (fun p => W p.2 p.1) (t, x t)`。

----

<a id="Tomabechi.Theorem27.Actuator.jointDerivativeOnPath_hasFDerivAt_of_contDiffAt"></a>

## 補題 `jointDerivativeOnPath_hasFDerivAt_of_contDiffAt`

### 式

$$W\ \text{が}\ C^1\ \text{near the path}\ \Longrightarrow\ \text{HasFDerivAt}\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 将来の軌道についての、条件 27-A の局所的な \(C^1\) の仮定は、連鎖律のアダプタが必要とする Fréchet 導関数の場を供給する。

### 補題の説明

\(C^1\) 級なら Fréchet 微分可能で、微分は `fderiv` です。

### 証明の概略

1. `ContDiffAt.differentiableAt` と `hasFDerivAt`。

----

<a id="Tomabechi.Theorem27.Actuator.stateGradientFromFDeriv_inner"></a>

## 補題 `stateGradientFromFDeriv_inner`

### 式

$$dW(0,z)=\langle\nabla_xW,z\rangle$$

### Lean のコメント（日本語訳）

> 状態座標の導関数の Riesz の代表元は、同時 Fréchet 微分から直接、条件 27-A の状態勾配の恒等式を供給する。

### 補題の説明

勾配の定義そのもの（Riesz 表現）です。

### 証明の概略

1. `InnerProductSpace.toDual_symm_apply`。

----

<a id="Tomabechi.Theorem27.Actuator.adjoint_norm_bound_implies_inner_action_bound"></a>

## 補題 `adjoint_norm_bound_implies_inner_action_bound`

### 式

$$\|G^\dagger g\|\le L\ \Longrightarrow\ |\langle g,Gv\rangle|\le L\|v\|$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

随伴の勾配のノルムの上界から、方向ごとの内積の上界が出ます（Cauchy–Schwarz と随伴の定義）。

### 証明の概略

1. `adjoint_inner_left` と Cauchy–Schwarz。

----

<a id="Tomabechi.Theorem27.Actuator.ae_inner_action_bound_of_adjoint_norm_bound"></a>

## 補題 `ae_inner_action_bound_of_adjoint_norm_bound`

### 式

$$\|G^\dagger\nabla W\|\le L\ \ \text{a.e.}\ \Longrightarrow\ \forall v,\ |\langle\nabla W,Gv\rangle|\le L\|v\|\ \ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 条件 27-A の随伴の評価の、ほとんど至るところの形。\(G^\dagger\nabla W\) の作用素の境界は、定量的な入力の差の結論 (27.8) が使う、方向ごとの対の境界を供給する。

### 補題の説明

上の補題の a.e. 版です。

### 証明の概略

1. 各時刻で上の補題。

----

<a id="Tomabechi.Theorem27.Actuator.ae_inner_action_bound_of_adjoint_norm_bound_on"></a>

## 補題 `ae_inner_action_bound_of_adjoint_norm_bound_on`

### 式

$$(\text{無明の時刻のみ})\ \|G^\dagger\nabla W\|\le L\ \Longrightarrow\ \text{方向ごとの評価 a.e.}$$

### Lean のコメント（日本語訳）

> 式 (27.8) に合う、条件つきの形：随伴の評価は、与えられた無明の述語を満たす時刻でだけ要求される。

### 補題の説明

目標の外（無明）の時刻だけでの評価で十分、という版です。

### 証明の概略

1. 上の補題を条件つきで。

----

<a id="Tomabechi.Theorem27.Actuator.ae_control_difference_distance_lower_bound_of_dini_on_future"></a>

## 定理 `ae_control_difference_distance_lower_bound_of_dini_on_future`

### 式

$$\text{将来の ray 版の (27.8)（距離の項つき）}$$

### Lean のコメント（日本語訳）

> 定量的な制御の境界 (27.8) の、将来の半直線の形。作用素の境界は \(|\langle\nabla W,Gv\rangle|\le L\|v\|\) として述べられ、操作的な無明の条項に合わせて、零残差の目標の外でだけ要求される。

### 補題の説明

(27.8) を将来の半直線だけの仮定で述べた、最終形です。

### 証明の概略

1. Dini 微分が将来の半直線上で a.e. 通常の導関数に一致（`ae_upperRightDiniDerivative_eq_deriv_on_future`）、連鎖律の公式（`ae_closedLoop_descent_formula_of_ode_under_measure`）で下降率が行の寄与に等しい。
2. 無明時の随伴評価 \(|\langle\nabla W,Gv\rangle|\le L\|v\|\) と下降率の下界から、入力差のノルムの下界 \(\|u_0-u_{\rm tr}\|\ge\lambda c_1d^2/L\) を、将来の半直線上の a.e. の仮定だけで導く（97 行）。

----


## コメント修正記録

（なし）
