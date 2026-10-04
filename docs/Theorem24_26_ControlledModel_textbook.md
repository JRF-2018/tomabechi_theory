# Theorem24_26_ControlledModel.lean 解説

> 対象: [`Theorem24_26_ControlledModel.lean`](../Theorem24_26_ControlledModel.lean)（定理24→26のインターフェースのための、2 つの作用を持つ制御モデル）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem24_26_Model`（制御の選択肢が 1 つ）の次の段階として、**制御が 2 つある**モデルです。許容されるフィードバックは 2 つの定数政策だけで、作用 `true` は \(\dot x=-x\)、作用 `false` は \(\dot x=0\)（動かない）です。走る費用は共通で \(3x^2\)、割引率は 1 です。このとき価値は、`true` の政策が \(x_0^2\)、`false` の政策が \(3x_0^2\) なので、`true` が最適で、最適な零価値目標は \(\{0\}\) になります。

つまり「2 つの政策を**実際に比較して**最適を選ぶ」モデルで、定理24→26のインターフェースを確かめます。最後の節では、下位の「零費用軌道なし」の層と上位の制御層を 2 要素の抽象の順序に入れ、一般の (26.3) の分類を適用します。

### 0.2 このファイルが証明していないこと

- 任意のフィードバック制御についての原文の仮定を導いたものではありません。許容フィードバックは 2 つの定数政策に**制限**されています。
- 認知制御のモデルから導いたものでもありません（原文のコメント）。「2 政策モデルでインターフェースを検証した」という範囲の結果です。

### 0.3 ファイル冒頭のコメント（日本語訳）

> 定理24→26のインターフェースのための、2 つの作用を持つ制御モデル。
>
> `Theorem24_26_Model` と違い、このモデルは、閉ループの力学が異なる 2 つの制御作用を持つ。許容される Borel マルコフ・フィードバックは、2 つの定数政策に制限される：作用 `true` は \(x'=-x\) を与え、作用 `false` は \(x'=0\) を与える。どちらも同じ走る費用 \(3x^2\) と割引率 1 を使う。したがって、それぞれの値は \(x_0^2\) と \(3x_0^2\) であり、第 1 の政策が最適で、最適な零価値目標は \(\{0\}\) である。これは 2 政策モデルでの定理のインターフェースを検証するが、任意のフィードバック制御や、認知制御のモデルから、論文の仮定を導くものではない。

名前空間は `Tomabechi.Theorem24_26_ControlledModel`（`open MeasureTheory Set`、`open Tomabechi.Theorem24_26`、`open Tomabechi.Theorem24_26_Model`）。

---

<a id="Tomabechi.Theorem24_26_ControlledModel.Control"></a>

## 定義 `Control`

### 式

$$U=\{\text{true},\text{false}\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

制御空間は 2 点（`Bool`）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.Feedback"></a>

## 定義 `Feedback`

### 式

$$\Pi=\text{Borel マルコフ・フィードバック}:\mathbb R\to U$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

制御を状態から決める Borel 可測な写像の型です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.dynamics"></a>

## 定義 `dynamics`

### 式

$$f(x,u)=\begin{cases}-x&(u=\text{true})\\0&(u=\text{false})\end{cases}$$

### Lean のコメント（日本語訳）

> 2 つの制御作用は、線形のドリフト \(-x\) と \(0\) を選ぶ。

### 定義の説明

制御に応じた速度場です。

### 証明の概略

1. `if u then -x else 0`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimalFeedback"></a>

## 定義 `optimalFeedback`

### 式

$$\pi_{\rm opt}\equiv\text{true}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

常に `true` を選ぶ定数政策（最適になる）。

### 証明の概略

1. 定数写像（可測：`measurable_const`）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.zeroDriftFeedback"></a>

## 定義 `zeroDriftFeedback`

### 式

$$\pi_{\rm 0}\equiv\text{false}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

常に `false` を選ぶ定数政策（動かない）。

### 証明の概略

1. 定数写像。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.admissible"></a>

## 定義 `admissible`

### 式

$$\mathrm{adm}(\pi)\iff\pi\equiv\text{true}\ \lor\ \pi\equiv\text{false}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

許容フィードバックを、2 つの定数政策に**制限**する定義です。

### 証明の概略

1. 「すべての \((t,y)\) で `true`」または「すべてで `false`」。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimalFeedback_admissible"></a>

## 定理 `optimalFeedback_admissible`

### 式

$$\mathrm{adm}(\pi_{\rm opt})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`optimalFeedback` が許容であること。

### 証明の概略

1. 左の選択肢で証明。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.zeroDriftFeedback_admissible"></a>

## 定理 `zeroDriftFeedback_admissible`

### 式

$$\mathrm{adm}(\pi_0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`zeroDriftFeedback` が許容であること。

### 証明の概略

1. 右の選択肢で証明。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.trajectory"></a>

## 定義 `trajectory`

### 式

$$x_\pi(s)=\begin{cases}xe^{T-s}&\text{(action at }(T,x)=\text{true)}\\x&\text{(false)}\end{cases}$$

### Lean のコメント（日本語訳）

> フィードバックに付随する、明示的な閉ループの軌道。

### 定義の説明

初期の組 \((x,T)\) での方策の作用で場合分けした軌道です。

### 証明の概略

1. `if π.action (T, x) then flow x T s else x`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.trajectory_eq_flow_of_true"></a>

## 定理 `trajectory_eq_flow_of_true`

### 式

$$\pi\equiv\text{true}\Rightarrow x_\pi=\mathrm{flow}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

常に `true` の政策の軌道は、`Theorem24_26_Model` の `flow` と一致します。

### 証明の概略

1. `trajectory` の定義の `if` を `hπ` で簡約。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.trajectory_eq_const_of_false"></a>

## 定理 `trajectory_eq_const_of_false`

### 式

$$\pi\equiv\text{false}\Rightarrow x_\pi(s)=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

常に `false` の政策の軌道は定数です。

### 証明の概略

1. `trajectory` の定義の `if` を `hπ` で簡約。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.runningCost"></a>

## 定義 `runningCost`

### 式

$$\ell(\pi,x,T,s)=3x^2$$

### Lean のコメント（日本語訳）

> どちらの作用も、非負の走る費用 \(3x^2\) を共有する。制御が影響するのは、モデルの軌道の部分である。

### 定義の説明

費用は共通で、政策の違いは軌道だけに現れます。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.discountedIntegrand"></a>

## 定義 `discountedIntegrand`

### 式

$$e^{-(s-T)}\cdot3\,x_\pi(s)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

政策 \(\pi\) の軌道に沿った割引費用の被積分関数。

### 証明の概略

1. 定義：`theorem26DiscountWeight 1 T s * runningCost π (trajectory π x T s) s`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.policyValue"></a>

## 定義 `policyValue`

### 式

$$J_\pi(x,T)=\int_{[T,\infty)}\text{discountedIntegrand}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

政策 \(\pi\) の価値（割引積分）。

### 証明の概略

1. 定義：`futureLebesgueMeasure T` に関する積分。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.discountedIntegrand_eq_of_true"></a>

## 定理 `discountedIntegrand_eq_of_true`

### 式

$$\pi\equiv\text{true}\Rightarrow\text{integrand}=3x^2e^{-3(s-T)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`true` 政策の被積分関数は、`Theorem24_26_Model` のものと同じです。

### 証明の概略

1. `trajectory_eq_flow_of_true` で書き換えて `rfl`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.discountedIntegrand_eq_of_false"></a>

## 定理 `discountedIntegrand_eq_of_false`

### 式

$$\pi\equiv\text{false}\Rightarrow\text{integrand}=3x^2e^{-(s-T)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`false` 政策では軌道が止まるので、被積分関数は \(3x^2e^{-(s-T)}\)（割引だけが減衰）です。

### 証明の概略

1. `trajectory_eq_const_of_false` で書き換えて整理。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.exp_future_integrable"></a>

## 定理 `exp_future_integrable`

### 式

$$3x^2e^{-(s-T)}\ \text{は将来の半直線上で可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`false` 政策の被積分関数の可積分性です。

### 証明の概略

1. \(e^{-s}\) の半直線上の可積分性に定数を掛ける（17 行）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.policyIntegrand_integrable"></a>

## 定理 `policyIntegrand_integrable`

### 式

$$\mathrm{adm}(\pi)\Rightarrow\text{discountedIntegrand は可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容な政策の被積分関数が可積分であること。2 つの場合に分けます。

### 証明の概略

1. `hπ` を `true`/`false` で場合分け。
2. それぞれ `discountedIntegrand_integrable`（Model）と `exp_future_integrable`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.policyValue_eq_sq_of_true"></a>

## 定理 `policyValue_eq_sq_of_true`

### 式

$$\pi\equiv\text{true}\Rightarrow J_\pi=x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`true` 政策の価値は \(x^2\)。

### 証明の概略

1. 被積分関数を `Theorem24_26_Model` のものに書き換え、`value_eq_sq` に帰着（9 行）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.policyValue_eq_three_sq_of_false"></a>

## 定理 `policyValue_eq_three_sq_of_false`

### 式

$$\pi\equiv\text{false}\Rightarrow J_\pi=3x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`false` 政策の価値は \(3x^2\)（\(\int 3x^2e^{-(s-T)}=3x^2\)）。

### 証明の概略

1. 被積分関数を \(3x^2e^{-(s-T)}\) に書き換え、`future_exp_integral`（\(c=1\)）を適用。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimalFeedback_attains_and_is_minimal"></a>

## 定理 `optimalFeedback_attains_and_is_minimal`

### 式

$$\mathrm{adm}(\pi_{\rm opt})\ \wedge\ J_{\pi_{\rm opt}}=x^2\ \wedge\ \forall\pi\ \mathrm{adm},\ x^2\le J_\pi$$

### Lean のコメント（日本語訳）

> `true` の作用の政策は、許容な 2 つの定常フィードバックの中で最適であり、その値はちょうど \(x^2\) である。

### 補題の説明

**2 つの政策を比べて最適を選ぶ**部分です：\(x^2\le 3x^2\) なので `true` が最適。

### 証明の概略

1. 許容性は `optimalFeedback_admissible`、値は `policyValue_eq_sq_of_true`。
2. 任意の許容政策を `true`/`false` で場合分けし、\(x^2\le x^2\) と \(x^2\le3x^2\)（\(x^2\ge0\)）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.zeroValueTarget"></a>

## 定義 `zeroValueTarget`

### 式

$$N(T)=\{x\mid x^2=0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適値 \(x^2\) による零価値目標です。

### 証明の概略

1. 定義：`theorem26ZeroValueTarget Set.univ (fun x _ => x^2) T`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.zeroValueTarget_eq_singleton"></a>

## 定理 `zeroValueTarget_eq_singleton`

### 式

$$N(T)=\{0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零価値の点は 0 だけ。

### 証明の概略

1. 定義を展開し `sq_eq_zero_iff`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.concrete_condition26A"></a>

## 定理 `concrete_condition26A`

### 式

$$d^2=W,\ \tfrac d{ds}W=-2W,\ x^2=d^2$$

### Lean のコメント（日本語訳）

> 定理26-A の Lyapunov、目標、値の境界は、モデルへの仮定ではなく、明示的な最適から従う。

### 補題の説明

`Theorem24_26_Model` の 26-A の確認を、このモデルの `zeroValueTarget` の言葉に直したものです。

### 証明の概略

1. `model_satisfies_condition26A` の結論を、`zeroValueTarget = zeroTarget`（どちらも \(\{0\}\)）で書き換える。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.concrete_condition26A_full"></a>

## 定理 `concrete_condition26A_full`

### 式

$$\text{alive 不変・目標が閉かつ非空・距離評価・指数散逸（}s\ge T\text{）}$$

### Lean のコメント（日本語訳）

> 前向きの時間区間での定理26-Aが使う、完全な幾何学的パッケージ：alive の不変性、閉で非空な零価値目標、2 つの Lyapunov の距離評価、指数的な散逸。

### 補題の説明

26-A の全項目を 1 つの定理にまとめたものです。

### 証明の概略

1. `Theorem24_26_Model.concrete_condition26A` を呼び、目標の言い換えを `zeroValueTarget_eq_singleton` で行う。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.trajectory_hasDerivAt"></a>

## 定理 `trajectory_hasDerivAt`

### 式

$$\dot x_\pi=\begin{cases}-x_\pi&(\text{true})\\0&(\text{false})\end{cases}$$

### Lean のコメント（日本語訳）

> 軌道は、`true` の作用のフィードバックでは \(x'=-x\)、零ドリフトのフィードバックでは \(x'=0\) という制御方程式を解く。

### 補題の説明

軌道が ODE の解であることの確認です。

### 証明の概略

1. 許容性で場合分け。`true` の場合は `flow_hasDerivAt`、`false` の場合は定数関数の微分 0。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.trajectory_solves_controlled_ode"></a>

## 定理 `trajectory_solves_controlled_ode`

### 式

$$\dot x_\pi(s)=f\bigl(x_\pi(s),\pi(s,x_\pi(s))\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`dynamics` を使った形の ODE：軌道は制御系 \(\dot x=f(x,u)\) を、方策 \(u=\pi(s,x)\) のもとで解く。

### 証明の概略

1. 場合分けして `trajectory_hasDerivAt` を `dynamics` の形に直す。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.topRunningValue"></a>

## 定義 `topRunningValue`

### 式

$$\text{走る価値 }\ell(\pi,x_\pi(s),T,s)$$

### Lean のコメント（日本語訳）

> 一般の PZS と最適値のインターフェースが使う、走る価値。

### 定義の説明

定理26のインターフェースが要求する形の走る価値です。

### 証明の概略

1. `runningCost` を軌道に沿って評価。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.feedbackPZS_iff_zeroValueTarget"></a>

## 定理 `feedbackPZS_iff_zeroValueTarget`

### 式

$$\mathrm{PZS}(x,T)\Longleftrightarrow x\in N(T)$$

### Lean のコメント（日本語訳）

> この具体的な制御モデルでは、PZS は、すでに証明された定理26のインターフェースによって、零価値目標への所属と同値である。

### 補題の説明

**PZS ⇔ 零価値目標**（2 政策モデル）。

### 証明の概略

1. `optimalFeedback_attains_and_is_minimal` で最適値が \(x^2\)。
2. `feedbackPZS_iff_optimal_value_eq_zero`（PZS ⇔ 最適値が 0）に、可積分性 `policyIntegrand_integrable` を渡す（29 行）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.concrete_theorem24_to26_bridge"></a>

## 定理 `concrete_theorem24_to26_bridge`

### 式

$$V_{\rm low}>0\ \wedge\ \neg\mathrm{PZS}_{\rm low}\ \wedge\ (\mathrm{PZS}_{\rm top}\iff x\in N)$$

### Lean のコメント（日本語訳）

> 定理24→定理26の分類の 2 層のインスタンス：条件 24-A は下位層で PZS を排除し、明示的な最適な上位層のフィードバックは、その零価値目標でまさに PZS を持つ。

### 補題の説明

**橋**：下位層では 24-A により PZS が起こらず、上位層では PZS が \(\{0\}\) への所属と同値、という分類の具体例です。

### 証明の概略

1. `lower_model_theorem24` で \(V_{\rm low}>0\)。
2. `theorem24_no_feedbackPZS_of_condition24A` で下位層に PZS なし。
3. 上位層は `feedbackPZS_iff_zeroValueTarget`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimal_feedback_exponential_convergence"></a>

## 定理 `optimal_feedback_exponential_convergence`

### 式

$$W(s)\le W(T)e^{-2(s-T)},\ d\le\sqrt{W(T)}e^{-(s-T)}$$

### Lean のコメント（日本語訳）

> 最適フィードバックの軌道は、一般の定理26の条件付き結果で証明された、定量的な収束の境界を継承する。

### 補題の説明

最適政策の軌道（`trajectory optimalFeedback`）での指数収束です。

### 証明の概略

1. `model_theorem26_exponential_convergence`（Model）を、`trajectory optimalFeedback = flow` で書き換えて適用。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimal_feedback_full_convergence"></a>

## 定理 `optimal_feedback_full_convergence`

### 式

$$\text{指数評価}\ \wedge\ J\to0\ \wedge\ (W=0\iff\text{target})$$

### Lean のコメント（日本語訳）

> 2 作用のモデルの最適フィードバックについての、定理26のすべての結論：最適値の極限と、零残差/目標の同値を含む。これは、明示的な流れについての Dini ベースの結果を、検証された `true` 作用のフィードバックの軌道を通じて運ぶ。

### 補題の説明

`Theorem24_26_Model` の完全な収束定理を、最適政策の軌道へ移したものです。

### 証明の概略

1. `model_theorem26_full_convergence` を、`trajectory_eq_flow_of_true`・`policyValue_eq_sq_of_true` で最適政策の言葉に翻訳（31 行）。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimal_feedback_alive_for_all_times"></a>

## 定理 `optimal_feedback_alive_for_all_times`

### 式

$$\forall s,\ x_{\rm opt}(s)\in\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生存集合が全体なので、軌道は常に生存集合の中にあります。

### 証明の概略

1. `Set.mem_univ`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.optimal_feedback_target_forward_invariant"></a>

## 定理 `optimal_feedback_target_forward_invariant`

### 式

$$x\in N(T)\Rightarrow\forall s,\ x_{\rm opt}(s)\in N(s)$$

### Lean のコメント（日本語訳）

> 最適な閉ループの軌道は、零価値目標を保つ。

### 補題の説明

目標 \(\{0\}\) の前向き不変性。

### 証明の概略

1. `model_forward_complete_and_target_invariant`（Model）を、`trajectory_eq_flow_of_true` で最適政策に移す。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.HierarchyState"></a>

## 定義 `HierarchyState`

### 式

$$\text{false}\mapsto\text{Unit},\ \text{true}\mapsto\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の状態の型（下位は 1 点、上位は \(\mathbb R\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.HierarchyFeedback"></a>

## 定義 `HierarchyFeedback`

### 式

$$\text{false}\mapsto\text{LowerFeedback},\ \text{true}\mapsto\Pi$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層のフィードバックの型。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.hierarchyTrajectory"></a>

## 定義 `hierarchyTrajectory`

### 式

$$\text{false}:x,\quad\text{true}:x_\pi(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の軌道。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.hierarchyValueDensity"></a>

## 定義 `hierarchyValueDensity`

### 式

$$\text{false}:1,\quad\text{true}:3x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の価値密度（走る費用）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.hierarchyAdmissible"></a>

## 定義 `hierarchyAdmissible`

### 式

$$\text{false}:\text{lowerAdmissible},\quad\text{true}:\mathrm{adm}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の許容性。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.hierarchyOptimalValue"></a>

## 定義 `hierarchyOptimalValue`

### 式

$$V^*(x,T)=x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の最適値です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.hierarchyAlive"></a>

## 定義 `hierarchyAlive`

### 式

$$\text{alive}=\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の生存集合は全体。

### 証明の概略

1. `Set.univ`。

----

<a id="Tomabechi.Theorem24_26_ControlledModel.concrete_hierarchy_pzs_classification"></a>

## 定理 `concrete_hierarchy_pzs_classification`

### 式

$$\bigl(\forall a<\top,\ \neg\mathrm{PZS}_a\bigr)\ \wedge\ \bigl(\mathrm{PZS}_\top(x,T)\iff x\in N_{\rm top}\bigr)$$

### Lean のコメント（日本語訳）

> 具体的な 2 層のモデルは、定理の PZS の完全な分類を満たす：下位の政策はどれも永続的に零ではなく、上位では、PZS は、零最適値の目標 \(\{0\}\) への所属とまさに同値である。

### 補題の説明

**(26.3) 型の分類**を、実際の制御モデルで確かめたものです。上位層のすべての許容フィードバックを比較しており、選ばれた最適政策だけを見ているのではありません。

### 証明の概略

1. 一般定理 `theorem24_26_pzs_classification_expDiscount` を、`HierarchyState` などの 2 層データに適用。
2. 下位層：費用が 1 なので 24-A。上位層：`feedbackPZS_iff_zeroValueTarget` と同様の手順（94 行）。

----


## コメント修正記録

（なし）
