# Theorem24_26_Model.lean 解説

> 対象: [`Theorem24_26_Model.lean`](../Theorem24_26_Model.lean)（定理24→26のインターフェースのための具体的なスカラーモデル）。
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
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理24 → 26 のインターフェースが**実際に使える**ことを示すための、ごく小さなスカラーモデルです。トップ層では状態が \(\dot x=-x\)（解 \(x(t)=x_0e^{-(t-T)}\)）、走る費用が \(3x^2\)、割引率が 1 です。すると割引積分の値は \(\int_T^\infty 3x_0^2e^{-2(s-T)}\,e^{-(s-T)}ds=x_0^2\) となり、零価値の目標は \(\{0\}\)、Lyapunov 関数は \(W(x)=x^2\) です。下位層は走る費用が定数 1 で、条件 24-A（零費用の軌道がない）を確かめるための層です。

最後に、この 2 層のデータを一般の `Theorem24NonnegativeTimeData` / `Theorem26NonnegativeTimeDynamics` のインスタンス（`sourceData`, `sourceDynamics`）として構成し、一般定理の結論（下位層の最適値が正、PZS ⇔ 目標、指数減衰）を取り出します。

### 0.2 このファイルが証明していないこと

- **特殊モデルです。** 論文の認知制御の一般的設定から仮定を導いたものではありません（原文のコメントのとおり）。
- 制御空間は 1 点集合（`PUnit`）なので、最適性は「選択の余地がない」特殊な場合です。フィードバックは実際の Borel マルコフ写像で、すべての定理は、プロジェクトの割引積分と PZS のインターフェースで検査されています。
- したがって「定理26を証明した」のではなく、「定理26の仮定を満たす具体モデルが 1 つある」ことの証明です。

### 0.3 ファイル冒頭のコメント（日本語訳）

> 定理24→26のインターフェースのための、具体的なスカラーモデル。
>
> このファイルは、意図的に小さな有限次元の割引制御モデルを展開する。トップ層では状態が \(x(t)=x_0\exp(-(t-T))\) に従い、走る費用は \(3x^2\)、割引率は 1 である。意図された値は \(x_0^2\) で、零価値の目標は \(\{0\}\)、\(W(x)=x^2\) は厳密な Lyapunov 証明書になる。別の低抽象層は定数の走る費用 1 を持ち、そこで条件 24-A を検証する。
>
> これは、明示的な特殊モデルであり、論文の仮定を一般的な認知制御の設定から導いたものではない。制御空間は 1 点集合なので、最適性は意図的に選択のない特殊な場合である。それでも、フィードバックは実際の Borel マルコフ写像であり、すべての定理の主張は、プロジェクトの割引積分と PZS のインターフェースで検査される。

名前空間は `Tomabechi.Theorem24_26_Model`（`open MeasureTheory Set`、`open Tomabechi.Theorem24_26`）。

---

<a id="Tomabechi.Theorem24_26_Model.Control"></a>

## 定義 `Control`

### 式

$$U=\{\ast\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

制御空間を 1 点集合にします（選択の余地なし）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.Feedback"></a>

## 定義 `Feedback`

### 式

$$\Pi=\text{Borel マルコフ・フィードバック}:\mathbb R\to U$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態 \(x\in\mathbb R\) から制御を決める Borel 可測な写像の型です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.commonFeedback"></a>

## 定義 `commonFeedback`

### 式

$$\pi_0(x)=\ast$$

### Lean のコメント（日本語訳）

> 唯一の制御の作用を、Borel マルコフ・フィードバックとして与える。

### 定義の説明

唯一のフィードバックです。

### 証明の概略

1. 定数写像として定義。

----

<a id="Tomabechi.Theorem24_26_Model.commonFeedback_measurable"></a>

## 定理 `commonFeedback_measurable`

### 式

$$\pi_0\ \text{は可測}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定数写像なので可測です。

### 証明の概略

1. `BorelMarkovFeedback` の構造体フィールド `measurable_action`（定数写像として構成した際の可測性の証明）。

----

<a id="Tomabechi.Theorem24_26_Model.admissible"></a>

## 定義 `admissible`

### 式

$$\mathrm{adm}(\pi,x,T)\equiv\text{True}$$

### Lean のコメント（日本語訳）

> 選択のないこのモデルでは、すべての Borel マルコフ・フィードバックが許容される。

### 定義の説明

すべてのフィードバックを許容とする定義です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.flow"></a>

## 定義 `flow`

### 式

$$\mathrm{flow}(x,T,s)=x\,e^{T-s}$$

### Lean のコメント（日本語訳）

> \(\dot x=-x\) の大域の閉ループの流れ。

### 定義の説明

解 \(x(s)=x\,e^{-(s-T)}\) の閉じた式です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.runningCost"></a>

## 定義 `runningCost`

### 式

$$\ell(x,s)=3x^2$$

### Lean のコメント（日本語訳）

> 二次の走る費用。割引した価値がちょうど \(x^2\) になるように、係数を調整してある。

### 定義の説明

走る費用 \(3x^2\) です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.discountedIntegrand"></a>

## 定義 `discountedIntegrand`

### 式

$$e^{-(s-T)}\cdot 3\,\mathrm{flow}(x,T,s)^2$$

### Lean のコメント（日本語訳）

> 定理26の割引した走る費用を、閉ループの流れに沿って評価したもの。

### 定義の説明

積分する被積分関数 \(w(T,s)\,\ell(x(s),s)\) です（\(w\) は割引の重み）。

### 証明の概略

1. 定義：`theorem26DiscountWeight 1 T s * runningCost (flow x T s) s`。

----

<a id="Tomabechi.Theorem24_26_Model.value"></a>

## 定義 `value`

### 式

$$V(x,T)=\int_{[T,\infty)}\text{discountedIntegrand}\ \mathrm d s$$

### Lean のコメント（日本語訳）

> トップ層のモデルの値で、閉ループの割引積分によって定める。

### 定義の説明

割引積分で定義された価値関数です。

### 証明の概略

1. 定義：`futureLebesgueMeasure T` に関する積分。

----

<a id="Tomabechi.Theorem24_26_Model.lowerRunningCost"></a>

## 定義 `lowerRunningCost`

### 式

$$\ell_{\rm low}\equiv1$$

### Lean のコメント（日本語訳）

> 下位の抽象は、走る費用が零の軌道を持たない。

### 定義の説明

下位層の走る費用は常に 1 です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.LowerFeedback"></a>

## 定義 `LowerFeedback`

### 式

$$\text{1 点集合}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

下位層のフィードバックの型です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.lowerAdmissible"></a>

## 定義 `lowerAdmissible`

### 式

$$\equiv\text{True}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

下位層では常に許容です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.lowerTrajectory"></a>

## 定義 `lowerTrajectory`

### 式

$$x(s)=x$$

### Lean のコメント（日本語訳）

> 下位層の（自明な）制御された軌道。定理24のインターフェースのために、初期状態を明示的に記録する。

### 定義の説明

状態が動かない軌道です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.lower_condition24A"></a>

## 定理 `lower_condition24A`

### 式

$$\neg\bigl(\ell_{\rm low}=0\ \text{a.e.}\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**条件 24-A**（走る費用が a.e. で 0 になる軌道がない）の下位層での確認です。費用が定数 1 だからです。

### 証明の概略

1. `theorem24_condition24A_of_ae_strictlyPositive`（a.e. 厳密正なら 24-A）を、費用が 1 であることで呼ぶ。

----

<a id="Tomabechi.Theorem24_26_Model.discountedIntegrand_eq"></a>

## 定理 `discountedIntegrand_eq`

### 式

$$\text{discountedIntegrand}=3x^2e^{-3(s-T)}$$

### Lean のコメント（日本語訳）

> 将来の割引した被積分関数は、率 3 の指数関数である。

### 補題の説明

割引 \(e^{-(s-T)}\) と、流れの二乗 \(x^2e^{-2(s-T)}\) を掛けて、\(3x^2e^{-3(s-T)}\) になります。

### 証明の概略

1. 定義を展開し、`T - s = -(s - T)` と指数法則で整理。

----

<a id="Tomabechi.Theorem24_26_Model.discountedIntegrand_integrable"></a>

## 定理 `discountedIntegrand_integrable`

### 式

$$\text{discountedIntegrand は将来の半直線上で可積分}$$

### Lean のコメント（日本語訳）

> 具体的な割引した費用の、将来の半直線上での可積分性。

### 補題の説明

指数減衰する関数は可積分です。

### 証明の概略

1. `discountedIntegrand_eq` で指数関数に書き換え。
2. \(\int_{\mathrm{Ioi}} e^{-cs}\) の可積分性（Mathlib）に \(3x^2e^{3T}\) を掛けて結論。

----

<a id="Tomabechi.Theorem24_26_Model.value_eq_sq"></a>

## 定理 `value_eq_sq`

### 式

$$V(x,T)=x^2$$

### Lean のコメント（日本語訳）

> 割引積分は、初期状態に関する二次の値に、ちょうど等しい。

### 補題の説明

\(\int_T^\infty 3x^2e^{-3(s-T)}ds=x^2\) の計算です。

### 証明の概略

1. `discountedIntegrand_eq` で書き換え、定数を積分の外に出す。
2. `integral_exp_mul_Ioi`（指数の半直線積分）で \(e^{-3T}/3\) を得る。
3. \(e^{3T}e^{-3T}=1\) で整理して \(x^2\)。

----

<a id="Tomabechi.Theorem24_26_Model.future_exp_integral"></a>

## 定理 `future_exp_integral`

### 式

$$\int_{[T,\infty)}e^{-c(s-T)}\,\mathrm ds=\frac1c\quad(c>0)$$

### Lean のコメント（日本語訳）

> 将来の Lebesgue 測度のもとでの指数モーメント。

### 補題の説明

指数関数の半直線積分の公式です（下位層の価値の計算に使う）。

### 証明の概略

1. `integral_Ici_eq_integral_Ioi` で半開区間を開区間に。
2. `integral_exp_mul_Ioi` で \(e^{-cT}/c\) を得て、\(e^{cT}\) を掛ける。

----

<a id="Tomabechi.Theorem24_26_Model.lowerValue"></a>

## 定義 `lowerValue`

### 式

$$V_{\rm low}(T)=\int e^{-(s-T)}\cdot1\ \mathrm ds$$

### Lean のコメント（日本語訳）

> 下位層の、定数費用のモデルは、達成された最適値 1 を持つ。

### 定義の説明

下位層の価値の定義です（値は 1）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.lowerPolicyValue"></a>

## 定義 `lowerPolicyValue`

### 式

$$V_\pi=V_{\rm low}(T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

下位層の政策の価値（唯一の政策なので最適値と同じ）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.lowerValue_eq_one"></a>

## 定理 `lowerValue_eq_one`

### 式

$$V_{\rm low}(T)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`future_exp_integral` で \(c=1\)。

### 証明の概略

1. 割引の重みと費用を展開し、`future_exp_integral`（\(c=1\)）を適用。

----

<a id="Tomabechi.Theorem24_26_Model.lower_policy_value_attained"></a>

## 定理 `lower_policy_value_attained`

### 式

$$\exists\pi\ \text{admissible},\ V_\pi=V_{\rm low}\ \wedge\ \forall\pi',\ V_{\rm low}\le V_{\pi'}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

下位層の最適値が、唯一の政策で**達成**されることです。

### 証明の概略

1. 唯一の政策が許容で、価値が最適値と一致する（`rfl`）。
2. 任意の政策の価値は同じなので、不等式は等号から。

----

<a id="Tomabechi.Theorem24_26_Model.lower_discounted_integrand_integrable"></a>

## 定理 `lower_discounted_integrand_integrable`

### 式

$$e^{-(s-T)}\cdot1\ \text{は可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

下位層の被積分関数の可積分性です。

### 証明の概略

1. `mul_one` と `neg_one_mul` で \(e^{-(s-T)}\) に書き換え。
2. 指数関数の半直線上の可積分性を、`IntegrableOn` で示す。

----

<a id="Tomabechi.Theorem24_26_Model.zeroTarget"></a>

## 定義 `zeroTarget`

### 式

$$N(T)=\{x\mid V(x,T)=0\}$$

### Lean のコメント（日本語訳）

> スカラーモデルの零価値の集合は、1 点の平衡である。

### 定義の説明

定理26の零価値目標を、このモデルの価値関数で具体化したものです。

### 証明の概略

1. 定義：`theorem26ZeroValueTarget Set.univ value T`（生存集合は全体）。

----

<a id="Tomabechi.Theorem24_26_Model.zeroTarget_eq_singleton"></a>

## 定理 `zeroTarget_eq_singleton`

### 式

$$N(T)=\{0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(V=x^2\) なので、零価値の点は 0 だけです。

### 証明の概略

1. 定義を展開し、`value_eq_sq` で \(x^2=0\iff x=0\)。

----

<a id="Tomabechi.Theorem24_26_Model.infDist_zeroTarget_sq"></a>

## 定理 `infDist_zeroTarget_sq`

### 式

$$d(x,N(T))^2=x^2$$

### Lean のコメント（日本語訳）

> モデルの目標までの距離の二乗は、二次の Lyapunov 値にちょうど等しい。

### 補題の説明

目標が \(\{0\}\) なので距離は \(|x|\) です。

### 証明の概略

1. `zeroTarget_eq_singleton` と `Metric.infDist_singleton`、`sq_abs`。

----

<a id="Tomabechi.Theorem24_26_Model.flow_hasDerivAt"></a>

## 定理 `flow_hasDerivAt`

### 式

$$\frac{d}{ds}\mathrm{flow}(x,T,s)=-\mathrm{flow}(x,T,s)$$

### Lean のコメント（日本語訳）

> 閉ループの軌道は、\(\dot x=-x\) の大域解である。

### 補題の説明

`flow` が実際に ODE \(\dot x=-x\) を満たすことの確認です。

### 証明の概略

1. \(T-u\) の微分は \(-1\)。
2. 合成関数の微分で \(\frac{d}{ds}e^{T-s}=-e^{T-s}\)。
3. 定数 \(x\) との積の微分で結論。

----

<a id="Tomabechi.Theorem24_26_Model.lyapunov"></a>

## 定義 `lyapunov`

### 式

$$W(x,t)=x^2$$

### Lean のコメント（日本語訳）

> スカラーモデルの、状態と時刻に依存する Lyapunov 関数。

### 定義の説明

Lyapunov 関数 \(W=x^2\) です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.WAlong"></a>

## 定義 `WAlong`

### 式

$$W_{\rm along}(s)=W(\mathrm{flow}(x,T,s),s)$$

### Lean のコメント（日本語訳）

> 明示的な閉ループの流れに沿って評価した Lyapunov 関数。

### 定義の説明

軌道に沿った \(W\) の値です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.WAlong_hasDerivAt"></a>

## 定理 `WAlong_hasDerivAt`

### 式

$$\frac{d}{ds}W_{\rm along}=-2W_{\rm along}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\frac d{ds}x^2=2x\dot x=-2x^2\) の計算で、**指数率 \(\lambda=2\) の下降**を得ます。

### 証明の概略

1. `flow_hasDerivAt` と `HasDerivAt.pow 2`（\(x^2\) の微分）を組み合わせる。

----

<a id="Tomabechi.Theorem24_26_Model.model_satisfies_condition26A"></a>

## 定理 `model_satisfies_condition26A`

### 式

$$d(x(s),N(s))^2=W,\quad \tfrac{d}{ds}W=-2W,\quad V(x(s),s)=d^2$$

### Lean のコメント（日本語訳）

> 条件 26-A の要件はすべて、\(c_1=c_2=1\)、\(\lambda=2\)、\(W(x)=x^2\) で成り立つ。値の境界 (26.C) は、\(\omega(r)=r^2\) で成り立つ。

### 補題の説明

**26-A の確認**：下側・上側の距離評価（\(c_1=c_2=1\)）、指数下降（\(\lambda=2\)）、値の境界（\(\omega(r)=r^2\)）です。

### 証明の概略

1. `infDist_zeroTarget_sq` で距離評価。
2. `WAlong_hasDerivAt` の `deriv` 版で下降率。
3. `value_eq_sq` で値 \(=x^2\)。

----

<a id="Tomabechi.Theorem24_26_Model.flow_semigroup"></a>

## 定理 `flow_semigroup`

### 式

$$\mathrm{flow}(\mathrm{flow}(x,T,s),s,u)=\mathrm{flow}(x,T,u)$$

### Lean のコメント（日本語訳）

> 閉じた形の流れは半群の性質を持つので、共通のフィードバックを中間の状態から再始動しても、同じ大域軌道が再現される。

### 補題の説明

**再始動の恒等式**（定理27のアダプタが要求するもの）の、具体モデルでの成立です。

### 証明の概略

1. 指数法則 \(e^{T-s}e^{s-u}=e^{T-u}\) を `calc` で計算。

----

<a id="Tomabechi.Theorem24_26_Model.model_forward_complete_and_target_invariant"></a>

## 定理 `model_forward_complete_and_target_invariant`

### 式

$$x\in N(T)\Rightarrow\forall u,\ \mathrm{flow}(x,T,u)\in N(u)$$

### Lean のコメント（日本語訳）

> 明示的な流れについて、大域存在、alive 集合の不変性、零価値の目標の前向き不変性が成り立つ。

### 補題の説明

解が全時間で存在すること、目標 \(\{0\}\) が不変（\(0\) は平衡点）であることです。

### 証明の概略

1. \(x\in N(T)\) なら \(x=0\)（`value_eq_sq`）。
2. \(\mathrm{flow}(0,T,u)=0\in N(u)\)。
3. alive 集合は全体 `Set.univ` なので自明。

----

<a id="Tomabechi.Theorem24_26_Model.topRunningValue"></a>

## 定義 `topRunningValue`

### 式

$$\text{トップ層の走る価値}$$

### Lean のコメント（日本語訳）

> 定理26のインターフェースに与える、走る価値の関数。

### 定義の説明

定理26が要求する形の走る価値（`runningCost` を流れに沿って評価）です。

### 証明の概略

1. 定義のみ（`runningCost` を使う）。

----

<a id="Tomabechi.Theorem24_26_Model.commonFeedback_is_optimal"></a>

## 定理 `commonFeedback_is_optimal`

### 式

$$V(x,T)=J_{\pi_0}(x,T)\ \wedge\ \forall\pi\,V\le J_\pi$$

### Lean のコメント（日本語訳）

> 共通のフィードバックは最適値を達成し、このモデルでは、すべての許容フィードバックが同じ値を持つ。

### 補題の説明

唯一のフィードバック \(\pi_0\) が最適です（選択の余地がないので自明）。

### 証明の概略

1. 許容性は `True`。
2. 値は定義どおり一致、不等式は等号から。

----

<a id="Tomabechi.Theorem24_26_Model.model_PZS_iff_target"></a>

## 定理 `model_PZS_iff_target`

### 式

$$\mathrm{PZS}(x,T)\Longleftrightarrow x\in N(T)=\{0\}$$

### Lean のコメント（日本語訳）

> 既存の定理26のインターフェースを、具体的な Borel マルコフ・フィードバックに適用すると、PZS が、このモデルの零状態とまさに同一視される。

### 補題の説明

**PZS ⇔ 零状態**：永続的に苦がゼロであるのは、状態が 0 のときだけ、というモデルでの結果です。

### 証明の概略

1. `commonFeedback_is_optimal` で最適性。
2. `feedbackPZS_iff_mem_theorem26ZeroValueTarget_borelMarkov`（定理26の PZS ⇔ 目標）に、可積分性 `discountedIntegrand_integrable` を渡して適用。

----

<a id="Tomabechi.Theorem24_26_Model.top_value_attained_for_all_initial_pairs"></a>

## 定理 `top_value_attained_for_all_initial_pairs`

### 式

$$V=J_{\pi_0}\ \wedge\ \forall\pi\,V\le J_\pi$$

### Lean のコメント（日本語訳）

> (26.1) で使う、完全な割引価値の恒等式と共通フィードバックの最適性。すべての初期の組について達成される。

### 補題の説明

すべての初期の組 \((x,T)\) で最適値が達成される、という (26.1) の入力です。

### 証明の概略

1. `commonFeedback_is_optimal` から値と不等式の部分を取り出す。

----

<a id="Tomabechi.Theorem24_26_Model.lower_model_theorem24"></a>

## 定理 `lower_model_theorem24`

### 式

$$\text{24-A}\ \wedge\ V_\pi=V_{\rm low}\ \wedge\ V_{\rm low}>0$$

### Lean のコメント（日本語訳）

> 下位層のモデルは、24-A を満たし、正の達成された値を持つ。

### 補題の説明

**定理24の結論**（24-A ならば最適値は正）の具体例での確認です。

### 証明の概略

1. `lower_discounted_integrand_integrable` と、`theorem24_positive_optimal_value_of_condition24A_ennreal`（24-A ⇒ 最適値が正）を使う。
2. 割引の重みが a.e. 正（`theorem26DiscountWeight_pos_ae`）であることを渡す（46 行）。

----

<a id="Tomabechi.Theorem24_26_Model.concrete_condition26A"></a>

## 定理 `concrete_condition26A`

### 式

$$\text{26-A の目標・距離・下降・値の境界 (すべての }s\ge T)$$

### Lean のコメント（日本語訳）

> このモデルは、条件 26-A の、厳密な値、Lyapunov、目標の関係を、すべての初期の組とすべての将来時刻で満たす。

### 補題の説明

`model_satisfies_condition26A` を、目標が閉・非空であることも含めた形に整えた版です。

### 証明の概略

1. `model_satisfies_condition26A` から等式と下降を取り、`zeroTarget_eq_singleton` で目標が \(\{0\}\)（閉・非空）であることを示す。

----

<a id="Tomabechi.Theorem24_26_Model.model_theorem26_full_convergence"></a>

## 定理 `model_theorem26_full_convergence`

### 式

$$W(s)\le W(T)e^{-2(s-T)},\ d\le\sqrt{W(T)}e^{-(s-T)},\ V\to0,\ (W=0\iff x\in N)$$

### Lean のコメント（日本語訳）

> スカラーモデルについての、定理26のすべての動的な結論：定量的な指数評価、最適値の収束、零 Lyapunov 残差の、非空な閉の零価値目標への所属による特徴づけ。証明は、一般定理の Dini/右傾斜版を呼び出すようになった。

### 補題の説明

**定理26の結論を、具体モデルに一般定理を適用して取り出した**ものです（直接計算ではない）。指数評価・価値の 0 への収束・「\(W=0\iff\) 目標に属する」の 3 つ。

### 証明の概略

1. `rightSlopeBound_of_hasDerivAt_le`（微分可能な不等式を右傾斜の評価に）と `WAlong_hasDerivAt` で 26-A の右傾斜条件。
2. `theorem26_full_conditional_convergence_of_rightSlopeBound`（一般定理）を適用（50 行）。

----

<a id="Tomabechi.Theorem24_26_Model.model_theorem26_exponential_convergence"></a>

## 定理 `model_theorem26_exponential_convergence`

### 式

$$W(s)\le W(T)e^{-2(s-T)}\ \wedge\ d(x(s),N(s))\le\sqrt{W(T)}\,e^{-(s-T)}$$

### Lean のコメント（日本語訳）

> 具体的なスカラー軌道についての、定理26の定量的な指数評価の、点ごとの形。

### 補題の説明

上の定理の第 1 の結論を、時刻ごとの形に取り出したものです。

### 証明の概略

1. `model_theorem26_full_convergence` の第 1 成分。

----

<a id="Tomabechi.Theorem24_26_Model.SourceAbstraction"></a>

## 定義 `SourceAbstraction`

### 式

$$\{\text{false}<\text{true}=\top\}$$

### Lean のコメント（日本語訳）

> 非負時間の一般定理を具体化するために使う、2 層の抽象の順序：`false` が下位層、`true = ⊤` がスカラーのトップ。

### 定義の説明

抽象のレベルを 2 点の順序（`Bool`）で与えます。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_Model.SourceState"></a>

## 定義 `SourceState`

### 式

$$\text{false}\mapsto\text{Unit},\ \text{true}\mapsto\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの状態の型（下位は 1 点、トップは \(\mathbb R\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.SourceFeedback"></a>

## 定義 `SourceFeedback`

### 式

$$\text{false}\mapsto\text{PUnit},\ \text{true}\mapsto\Pi_{\ge0}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとのフィードバックの型（トップは非負時間の Borel マルコフ）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.sourceFeedback0"></a>

## 定義 `sourceFeedback0`

### 式

$$\pi^0\equiv\ast$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

非負時間版の唯一のフィードバックです。

### 証明の概略

1. 定数写像。

----

<a id="Tomabechi.Theorem24_26_Model.sourceTrajectory"></a>

## 定義 `sourceTrajectory`

### 式

$$\text{false}:x,\quad\text{true}:\mathrm{flow}(x,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの軌道（下位は静止、トップは流れ）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.sourceRunningCost"></a>

## 定義 `sourceRunningCost`

### 式

$$\text{false}:1,\quad\text{true}:\text{runningCost}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの走る費用です。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.sourceOptimalValue"></a>

## 定義 `sourceOptimalValue`

### 式

$$\text{false}:V_{\rm low}(T),\quad\text{true}:V(x,T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適値です。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.sourceOptimalPolicy"></a>

## 定義 `sourceOptimalPolicy`

### 式

$$\text{最適政策（唯一の政策）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適政策です（唯一）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.sourceAdmissible"></a>

## 定義 `sourceAdmissible`

### 式

$$\text{すべて許容}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの許容性（常に True）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_Model.source_lower_lintegral_eq"></a>

## 定理 `source_lower_lintegral_eq`

### 式

$$\mathrm{ofReal}(V_{\rm low})=\int^-\mathrm{ofReal}(w\ell_{\rm low})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

下位層の価値を、下積分（拡大非負実数値の積分）の形で表します。`Theorem24NonnegativeTimeData` が要求する形です。

### 証明の概略

1. 可積分性（`lower_discounted_integrand_integrable`）から、`ofReal_integral_eq_lintegral_ofReal` 型の変換（7 行）。

----

<a id="Tomabechi.Theorem24_26_Model.source_top_lintegral_eq"></a>

## 定理 `source_top_lintegral_eq`

### 式

$$\mathrm{ofReal}(V(x,T))=\int^-\mathrm{ofReal}(w\,\ell(\mathrm{flow}))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

トップ層の価値の下積分表示です。

### 証明の概略

1. `discountedIntegrand_integrable` から同様の変換（10 行）。

----

<a id="Tomabechi.Theorem24_26_Model.sourceData"></a>

## 定義 `sourceData`

### 式

$$\mathcal D=(\text{layers},\text{traj},\ell,\text{adm},V^*,\pi^*)$$

### Lean のコメント（日本語訳）

> 2 層のインスタンスのソース領域のデータ：下位層は定数の正の費用を持ち、トップ層は、このファイルの明示的な Borel 制御のスカラー流である。

### 定義の説明

一般の `Theorem24NonnegativeTimeData` の、具体的なインスタンスです（54 行の構成）。各フィールドの条件（可積分性・下積分の表示・最適性）は、上の補題から埋めます。

### 証明の概略

1. 各フィールドに `sourceTrajectory` などを割り当て、条件を `lower_discounted_integrand_integrable`・`discountedIntegrand_integrable`・`source_*_lintegral_eq` で証明。

----

<a id="Tomabechi.Theorem24_26_Model.sourceTopPseudoMetric"></a>

## インスタンス `sourceTopPseudoMetric`

### 式

$$d(x,y)=|x-y|$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

トップ層の状態空間 \(\mathbb R\) の擬距離のインスタンス（ローカル）。

### 証明の概略

1. `SourceState true = ℝ` なので、実数の擬距離を再利用。

----

<a id="Tomabechi.Theorem24_26_Model.sourceTopMeasurableSpace"></a>

## インスタンス `sourceTopMeasurableSpace`

### 式

$$\text{Borel}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

トップ層の可測空間のインスタンス。

### 証明の概略

1. 実数の Borel を再利用。

----

<a id="Tomabechi.Theorem24_26_Model.sourceTopBorelSpace"></a>

## インスタンス `sourceTopBorelSpace`

### 式

$$\text{BorelSpace}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

可測構造が Borel であることのインスタンス。

### 証明の概略

1. 実数の `BorelSpace` を再利用。

----

<a id="Tomabechi.Theorem24_26_Model.sourceTopProductBorelSpace"></a>

## インスタンス `sourceTopProductBorelSpace`

### 式

$$\text{BorelSpace}([0,\infty)\times\mathbb R)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

積空間 \([0,\infty)\times\mathbb R\) が Borel であることのインスタンス。

### 証明の概略

1. 積の `BorelSpace` の既存インスタンスを使う。

----

<a id="Tomabechi.Theorem24_26_Model.sourceNormedMetric_eq_real"></a>

## 定理 `sourceNormedMetric_eq_real`

### 式

$$\text{ノルム由来の擬距離}=\text{実数の擬距離}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

インスタンスが二重に出ても食い違わないことの確認です。

### 証明の概略

1. `PseudoMetricSpace.ext`（距離関数の外延性）と `Real.dist_eq`（7 行）。

----

<a id="Tomabechi.Theorem24_26_Model.sourceData_target_eq"></a>

## 定理 `sourceData_target_eq`

### 式

$$N_{\text{top}}(\mathcal D)=\text{zeroTarget}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`sourceData` から定理26の定義で作った零価値目標が、このファイルで具体的に定義した `zeroTarget` と一致します。

### 証明の概略

1. 定義を展開し、`sourceOptimalValue` が `value` であることで `rfl`。

----

<a id="Tomabechi.Theorem24_26_Model.sourceDynamics"></a>

## 定義 `sourceDynamics`

### 式

$$\mathcal E=(W,\lambda,c_1,c_2,\text{target},\text{alive},\text{feedback})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem26NonnegativeTimeDynamics` の具体的なインスタンスです（87 行）。\(W=x^2\)、\(\lambda=2\)、\(c_1=c_2=1\)、目標 \(\{0\}\)、alive は全体、フィードバックは `sourceFeedback0` と最適政策。各条件は、上の具体的な補題で埋めます。

### 証明の概略

1. `sourceData_target_eq`、`zeroTarget_eq_singleton`、`model_forward_complete_and_target_invariant`、`WAlong_hasDerivAt`、`sourceNormedMetric_eq_real` などを、フィールドごとに割り当てる。

----

<a id="Tomabechi.Theorem24_26_Model.source_model_general_lower_positive"></a>

## 定理 `source_model_general_lower_positive`

### 式

$$V^*_{\rm low}(T)>0\quad(T\ge0)$$

### Lean のコメント（日本語訳）

> 明示的なスカラーモデルは、一般の非負時間の定理24→26のインターフェースのインスタンスになった。この外側の包みは、各非負の初期の組での、結合した結果を表に出す。

### 補題の説明

**定理24の結論**（下位層の最適値が正）を、一般定理 `theorem24_to26_from_nonnegativeTimeData` を通じて取り出したものです。

### 証明の概略

1. `theorem24_to26_from_nonnegativeTimeData sourceData sourceDynamics` を適用し、下位層の成分を取り出す。

----

<a id="Tomabechi.Theorem24_26_Model.source_model_general_top_pzs"></a>

## 定理 `source_model_general_top_pzs`

### 式

$$\mathrm{PZS}(x,T)\Longleftrightarrow x\in N_{\text{top}}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

トップ層の **PZS ⇔ 零価値目標**（一般定理を通じた版）です。

### 証明の概略

1. 同じ一般定理の結論から、トップ層の PZS の同値の成分を取り出す。

----

<a id="Tomabechi.Theorem24_26_Model.source_model_general_exponential_decay"></a>

## 定理 `source_model_general_exponential_decay`

### 式

$$W\le W_0e^{-\lambda(s-T)}\ \wedge\ d\le\sqrt{W_0/c_1}\,e^{-(\lambda/2)(s-T)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般定理を通じた**指数減衰**の結論です。

### 証明の概略

1. 同じ一般定理の結論から、指数評価の成分を取り出す。

----


## コメント修正記録

（なし）
