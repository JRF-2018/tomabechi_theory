# Theorem24_26_GainControl.lean 解説

> 対象: [`Theorem24_26_GainControl.lean`](../Theorem24_26_GainControl.lean)（定理24→26のための、スカラーの Markov フィードバックの連続族（ゲイン制御））。
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
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem24_26_Model`／`Theorem24_26_ControlledModel` は「政策が 1〜2 個」でしたが、このファイルは**連続な族のフィードバック**を扱う、より本格的なモデルです。制御は線形の Markov 則 \(u=\alpha x\)（\(\alpha>0\)、**ゲイン**）、状態方程式は \(\dot x=-u\)、費用は \(q x^2+r u^2\)、割引率は \(\rho\) です。\(m>0\) を与え \(q=r\,m\,(m+\rho)\) と選ぶと、
$$\text{ゲイン }\alpha=m\text{ が、ゲインの族の中で（費用の係数として）一意の最小化元}$$
で、しかも**任意の非零の初期状態に対して**値の一意最小化元になります。最適値は \(V^*(x)=r\,m\,x^2\)、零価値の目標は \(\{0\}\) です。

このファイルの中心は **HJB の検証定理**です。候補値 \(V=rmx^2\) について、HJB の残差が
$$\text{running cost}+V'(x)\cdot(-u)-\rho V=r\,(u-mx)^2\ \ge0$$
と**完全平方**になる（`hamiltonian_gap_eq_square`）ことを使い、有限地平 → 無限地平の検証不等式を作ります。その結果、**競合するフィードバックを「ゲインの族」に制限せず、有限費用の古典閉ループ軌道を持つ任意の Borel マルコフ・フィードバックと比べても**、\(u=mx\) が最適であることが示されます。一般論（任意のスカラー力学・任意の走る費用、さらに時間依存・合同 Fréchet 微分可能な価値）の検証定理も、途中に独立の補題として置かれています。

最後に、2 層のデータ（下位層：定数費用、上位層：このゲイン・モデル）を一般の `Theorem24NonnegativeTimeData`／`Theorem26NonnegativeTimeDynamics` のインスタンスとして構成し、一般定理の結論を直接取り出します（`gainSource_general_bridge`）。

### 0.2 このファイルが証明していないこと

- **競合の範囲**：任意の可測な制御ではなく、(i) 古典的な（ほぼ至るところでなく、すべての \(s\) で微分可能な）閉ループ軌道を持ち、(ii) 割引費用が有限、である Borel マルコフ・フィードバックだけを競合に含めます。競合の存在の仮定は、初期の組ごと・フィードバックごとに変わり得ます（最適フィードバック自身は変わりません）。
- スカラー・二次・線形力学の特殊モデルであり、論文の認知制御の一般モデルから仮定を導いたものではありません（冒頭コメント）。
- 下位層は定数費用の Unit モデルです。

### 0.3 ファイル冒頭のコメント（日本語訳）

> 定理24→26のための、スカラーの Markov フィードバックの連続族。
>
> 制御は線形の Markov 則 \(u=\alpha x\)（\(\alpha>0\)）で、状態方程式は \(x'=-u\)、費用は \(qx^2+ru^2\) である。\(m>0\) が与えられたとき、\(q=rm(m+\rho)\) と選ぶと、\(\alpha=m\) が、この連続な政策のクラスの中での費用係数の一意の最小化元であり、すべての非零の初期状態についての値の一意の最小化元になる。これは自明でないモデルであるが、任意の可測な制御ではなく、定数の線形ゲインに制限されている。

（注：後半で、競合を任意の Borel マルコフ・フィードバックに広げた検証定理が追加されており、上のコメントの最後の「制限されている」は、**ゲインの族そのもの**についての記述です。）

名前空間は `Tomabechi.Theorem24_26_GainControl`（`open MeasureTheory Set`、`open Tomabechi.Theorem24_26`、`open Tomabechi.Theorem24_26_LinearFamily`、`open Tomabechi.Theorem24_26_Model`）。

---

<a id="Tomabechi.Theorem24_26_GainControl.Gain"></a>

## 定義 `Gain`

### 式

$$\mathrm{Gain}=\{\alpha\in\mathbb R\mid\alpha>0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

正の実数の部分型で、線形フィードバックのゲインを表します。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.feedback"></a>

## 定義 `feedback`

### 式

$$\pi_\alpha(t,x)=\alpha x$$

### Lean のコメント（日本語訳）

> 正のゲインは、Borel マルコフ・フィードバック \((t,x)\mapsto a\cdot x\) を誘導する。

### 定義の説明

ゲイン \(\alpha\) から、方策 \(u=\alpha x\) を作ります（可測性は `fun_prop`）。

### 証明の概略

1. 定義：`⟨fun p => a.1 * p.2, by fun_prop⟩`。

----

<a id="Tomabechi.Theorem24_26_GainControl.feedback_action"></a>

## 定理 `feedback_action`

### 式

$$\pi_\alpha(t,x)=\alpha x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`feedback` の作用の式です。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Theorem24_26_GainControl.controlOutput"></a>

## 定義 `controlOutput`

### 式

$$u_\alpha(x)=\pi_\alpha(0,x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

時刻に依存しない制御出力 \(u=\alpha x\)。

### 証明の概略

1. 定義：`(feedback a).action (0, x)`。

----

<a id="Tomabechi.Theorem24_26_GainControl.controlOutput_eq"></a>

## 定理 `controlOutput_eq`

### 式

$$u_\alpha(x)=\alpha x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

制御出力の式。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Theorem24_26_GainControl.trajectory"></a>

## 定義 `trajectory`

### 式

$$x_\alpha(s)=x\,e^{-\alpha(s-T)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゲイン \(\alpha\) の閉ループ軌道（`Theorem24_26_LinearFamily.flow` と同じ）。

### 証明の概略

1. 定義：`Theorem24_26_LinearFamily.flow a.1 x T s`。

----

<a id="Tomabechi.Theorem24_26_GainControl.trajectory_hasDerivAt"></a>

## 定理 `trajectory_hasDerivAt`

### 式

$$\dot x_\alpha=-u_\alpha(x_\alpha)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道が \(\dot x=-u\) を満たすこと。

### 証明の概略

1. `Theorem24_26_LinearFamily.flow_hasDerivAt` を `controlOutput_eq` で書き換える。

----

<a id="Tomabechi.Theorem24_26_GainControl.runningCost"></a>

## 定義 `runningCost`

### 式

$$\ell_\alpha(x)=rm(m+\rho)x^2+r\,u_\alpha(x)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

走る費用：状態の二次項 \(qx^2\)（\(q=rm(m+\rho)\)）と制御の二次項 \(ru^2\) の和。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.runningCost_eq_coeff"></a>

## 定理 `runningCost_eq_coeff`

### 式

$$\ell_\alpha(x)=\bigl(rm(m+\rho)+r\alpha^2\bigr)x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲイン政策の下では費用が \(x^2\) の定数倍になる（\(u=\alpha x\) を代入）。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Theorem24_26_GainControl.inputRunningCost"></a>

## 定義 `inputRunningCost`

### 式

$$\ell(x,u)=rm(m+\rho)x^2+r\,u^2$$

### Lean のコメント（日本語訳）

> 線形ゲイン政策に制限する前の、任意の瞬間的な入力の関数としての走る費用。

### 定義の説明

任意の入力 \(u\) に対する費用です（競合の比較に使います）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.candidateValue"></a>

## 定義 `candidateValue`

### 式

$$V(x)=rm\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

候補となる価値関数。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.candidateValueGradient"></a>

## 定義 `candidateValueGradient`

### 式

$$V'(x)=2rm\,x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

候補値の勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainJointValue"></a>

## 定義 `gainJointValue`

### 式

$$V(x,t)=rm\,x^2$$

### Lean のコメント（日本語訳）

> 合同 Fréchet 検証定理を具体化するために使う、二次の候補の、時間・状態の形。

### 定義の説明

時間と状態の組 \(z=(x,t)\) の関数としての候補値（時間には依存しない）。

### 証明の概略

1. 定義：`candidateValue m r z.1`。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainJointDerivative"></a>

## 定義 `gainJointDerivative`

### 式

$$\mathrm dV(x,t)(\xi,\tau)=2rm\,x\,\xi$$

### Lean のコメント（日本語訳）

> `gainJointValue` の合同微分。その時間成分は 0 である。

### 定義の説明

合同 Fréchet 微分を連続線形写像として具体的に書いたものです。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainJointValue_hasFDerivAt"></a>

## 定理 `gainJointValue_hasFDerivAt`

### 式

$$V\ \text{は}\ \mathrm dV\ \text{を Fréchet 微分に持つ}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gainJointDerivative` が実際に Fréchet 微分であること。

### 証明の概略

1. `hasFDerivAt_fst` の冪乗と定数倍で計算。

----

<a id="Tomabechi.Theorem24_26_GainControl.hamiltonian_gap_eq_square"></a>

## 定理 `hamiltonian_gap_eq_square`

### 式

$$\ell(x,u)+V'(x)(-u)-\rho V(x)=r\,(u-mx)^2$$

### Lean のコメント（日本語訳）

> 候補値 \(rmx^2\) についての HJB の残差は、すべての実数の制御入力について、まさに平方であり、線形ゲイン政策に限らない。

### 補題の説明

**このファイルの鍵になる恒等式**（完全平方）です。残差が非負で、\(u=mx\) のときだけ 0 になります。

### 証明の概略

1. 各定義を展開して `ring`。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainJoint_hjb_residual_eq_square"></a>

## 定理 `gainJoint_hjb_residual_eq_square`

### 式

$$\ell(x,u)+\mathrm dV(x,0)(-u,1)-\rho V=r(u-mx)^2$$

### Lean のコメント（日本語訳）

> 一般の時間依存 HJB 検証定理が使う、合同 Fréchet の時間・状態の記法での、同じ平方の恒等式。

### 補題の説明

同じ恒等式を、合同微分の形で述べたもの。

### 証明の概略

1. 定義を展開して `simp` と `ring`。

----

<a id="Tomabechi.Theorem24_26_GainControl.hamiltonian_gap_nonneg"></a>

## 定理 `hamiltonian_gap_nonneg`

### 式

$$r\ge0\Rightarrow\ell(x,u)+V'(x)(-u)-\rho V\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

HJB の残差の非負性（\(r(u-mx)^2\ge0\)）。

### 証明の概略

1. `hamiltonian_gap_eq_square` と `mul_nonneg`、`sq_nonneg`。

----

<a id="Tomabechi.Theorem24_26_GainControl.hamiltonian_minimizer_unique"></a>

## 定理 `hamiltonian_minimizer_unique`

### 式

$$r>0,\ \text{残差}=0\Rightarrow u=mx$$

### Lean のコメント（日本語訳）

> 正の努力の重みについて、Hamiltonian は、実数の作用の全空間にわたって、\(u=mx\) により一意に最小化される。

### 補題の説明

残差が 0 になるのは \(u=mx\) のときだけです。

### 証明の概略

1. 平方の恒等式から \(r(u-mx)^2=0\)、\(r>0\) なので \(u=mx\)。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalFeedback_hamiltonian_is_minimizing"></a>

## 定理 `optimalFeedback_hamiltonian_is_minimizing`

### 式

$$\text{ゲイン }m\text{ の入力 }u=mx\text{ で残差}=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適ゲイン \(m\) の制御出力が、Hamiltonian の最小化元であること。

### 証明の概略

1. 平方の恒等式に \(u=mx\) を代入。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedInputCost"></a>

## 定義 `discountedInputCost`

### 式

$$e^{-\rho(s-T)}\,\ell\bigl(x(s),u(s)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

任意の入力と状態の経路についての、割引した費用の被積分関数。

### 証明の概略

1. 定義：`theorem26DiscountWeight ρ T s * inputRunningCost …`。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedInputEffort"></a>

## 定義 `discountedInputEffort`

### 式

$$e^{-\rho(s-T)}\,r\,u(s)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

割引した努力（制御の二次項）だけの被積分関数。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedInputCost_integrable_of_boundedState_and_effort"></a>

## 定理 `discountedInputCost_integrable_of_boundedState_and_effort`

### 式

$$\|x\|\le B,\ \text{努力が可積分}\Rightarrow\text{費用が可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

状態が有界で割引した努力が可積分なら、割引費用も可積分です（状態の項は \(B^2e^{-\rho(s-T)}\) で抑えられる）。

### 証明の概略

1. 費用 = 状態項 + 努力項に分ける。
2. 状態項は有界 × 指数減衰で可積分、努力項は仮定。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedSquareGap"></a>

## 定義 `discountedSquareGap`

### 式

$$e^{-\rho(s-T)}\,r\,(u(s)-mx(s))^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

割引した完全平方の残差。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.inputSquareGap_le_twice_runningCost"></a>

## 定理 `inputSquareGap_le_twice_runningCost`

### 式

$$m,\rho,r>0\Rightarrow r(u-mx)^2\le2\,\ell(x,u)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平方の残差は、走る費用の 2 倍以下です（この評価で、費用が可積分なら残差も可積分になります）。

### 証明の概略

1. \(r(u-mx)^2\le2r u^2+2rm^2x^2\) と、\(\ell\ge rm(m+\rho)x^2\) の比較（`nlinarith`）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedSquareGap_integrable_of_inputCost_integrable"></a>

## 定理 `discountedSquareGap_integrable_of_inputCost_integrable`

### 式

$$\text{費用が可積分}\Rightarrow\text{割引した平方の残差が可積分}$$

### Lean のコメント（日本語訳）

> 二乗の HJB 残差は、非負の二次の走る費用が可積分なら、可積分である。その係数は費用の 2 倍で抑えられる。

### 補題の説明

`inputSquareGap_le_twice_runningCost` の可積分版です。

### 証明の概略

1. `Integrable.mono` で、残差を \(2\times\) 費用で抑える（可測性は仮定）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedSquareGap_intervalIntegrable_of_inputCost_integrable"></a>

## 定理 `discountedSquareGap_intervalIntegrable_of_inputCost_integrable`

### 式

$$\text{残差が将来で可積分}\Rightarrow[T,S]\text{ で区間可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

半直線で可積分なら有限区間でも区間可積分。

### 証明の概略

1. 仮定（残差が将来の半直線 \([T,\infty)\) 上で可積分）を `IntegrableOn` の形に書き直す。
2. 部分集合 \((T,S]\subset[T,\infty)\) に制限して `IntegrableOn`（`IntegrableOn.mono_set`）。
3. `intervalIntegrable_iff_integrableOn_Ioc_of_le`（\(T\le S\)）で区間可積分に直す（14 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedInputCost_intervalIntegrable_of_integrable"></a>

## 定理 `discountedInputCost_intervalIntegrable_of_integrable`

### 式

$$\text{費用が将来で可積分}\Rightarrow[T,S]\text{ で区間可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

費用の区間可積分性。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedCandidateValue"></a>

## 定義 `discountedCandidateValue`

### 式

$$F(s)=e^{-\rho(s-T)}\,V(x(s))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

割引した候補値 \(F(s)\)（検証の主役）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedCandidateValue_integrable_of_inputCost_integrable"></a>

## 定理 `discountedCandidateValue_integrable_of_inputCost_integrable`

### 式

$$\text{費用が可積分}\Rightarrow F\in L^1$$

### Lean のコメント（日本語訳）

> 有限の割引した二次費用は、割引した候補値を \(L^1\) で制御する。これは、合同 Fréchet の HJB 検証子が必要とする、候補値の可積分性の前提である。

### 補題の説明

\(V=rmx^2\) は、状態項 \(qx^2\) の定数倍（\(rm/q=1/(m+\rho)\)）なので、費用で抑えられます。

### 証明の概略

1. \(0\le F\le\frac{rm}{q}\times\)費用 を示す。
2. `Integrable.mono` で結論（47 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedCandidateValue_tendsto_zero_of_bounded_state"></a>

## 定理 `discountedCandidateValue_tendsto_zero_of_bounded_state`

### 式

$$\|x\|\le B\Rightarrow F(s)\to0\ (s\to\infty)$$

### Lean のコメント（日本語訳）

> 正の割引は、状態が将来の半直線上で有界である限り、候補の終端値を 0 に消す。

### 補題の説明

横断性条件 \(F\to0\) の、有界状態の場合です。\(F\le rmB^2e^{-\rho(s-T)}\to0\)。

### 証明の概略

1. `squeeze_zero` で、\(0\le F\le rmB^2e^{-\rho(s-T)}\) と指数関数の極限 0。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedInputCost_interval_tendsto_futureIntegral"></a>

## 定理 `discountedInputCost_interval_tendsto_futureIntegral`

### 式

$$\int_T^{h_n}\mathrm{cost}\ \to\ \int_{[T,\infty)}\mathrm{cost}$$

### Lean のコメント（日本語訳）

> 将来の半直線上で可積分な割引費用について、任意の尽くす列の有限地平での積分は、実際の将来の Lebesgue 積分に収束する。これは、普通の可積分性から、無限地平検証定理の費用の極限の仮定を供給する。

### 補題の説明

有限地平の積分が無限地平の積分に収束する、という補題です。

### 証明の概略

1. 費用が \([T,\infty)\) で可積分なので、開半直線 \((T,\infty)\) 上でも可積分（`integrableOn_Ici_iff_integrableOn_Ioi`）。
2. Mathlib の `intervalIntegral_tendsto_integral_Ioi`（有限区間の積分が \(h_n\to\infty\) のとき半直線の積分に収束）を適用する。
3. 将来測度 `futureLebesgueMeasure T` での積分と \((T,\infty)\) 上の積分が等しいこと（`integral_Ici_eq_integral_Ioi`）で書き換える（30 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.integrable_future_intervalIntegrable"></a>

## 定理 `integrable_future_intervalIntegrable`

### 式

$$g\in L^1([T,\infty))\Rightarrow g\ \text{は }[T,S]\text{ で区間可積分}$$

### Lean のコメント（日本語訳）

> 将来の半直線上で可積分な関数は、すべての有限の前向きの区間で区間可積分である。

### 補題の説明

半直線で可積分なら、その部分区間でも可積分です。

### 証明の概略

1. `IntegrableOn` の単調性（区間は半直線の部分集合）。

----

<a id="Tomabechi.Theorem24_26_GainControl.integrable_future_interval_tendsto_integral"></a>

## 定理 `integrable_future_interval_tendsto_integral`

### 式

$$g\in L^1([T,\infty)),\ h_n\to\infty\Rightarrow\int_T^{h_n}g\to\int g$$

### Lean のコメント（日本語訳）

> 将来の半直線上の可積分性は、任意の尽くす地平に沿った有限区間の積分を、実際の将来の Lebesgue 積分に収束させる。

### 補題の説明

`intervalIntegral_tendsto_integral_Ioi` 型の一般補題です。

### 証明の概略

1. \([T,\infty)\) を `Ioi` に直し、Mathlib の `MeasureTheory.intervalIntegral_tendsto_integral_Ioi` を適用（15 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.integrable_future_tendsto_zero_of_hasDerivAt"></a>

## 定理 `integrable_future_tendsto_zero_of_hasDerivAt`

### 式

$$F\in L^1,\ F'\in L^1\Rightarrow F\to0$$

### Lean のコメント（日本語訳）

> 可積分な割引した候補で、その導関数が将来の半直線上で可積分なものは、横断性の極限を満たす。これは、別に仮定された終端条件を置き換える、解析的な段階をまとめたものである。

### 補題の説明

\(F\) と \(F'\) がともに可積分なら \(F(s)\to0\)（無限遠で値が 0 に近づく）、という解析の補題です。

### 証明の概略

1. Mathlib の `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi`（導関数が可積分で関数も可積分なら 0 に収束）を適用。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedCandidateValue_hasDerivAt"></a>

## 定理 `discountedCandidateValue_hasDerivAt`

### 式

$$F'(s)=e^{-\rho(s-T)}\bigl(V'(x)(-u)-\rho V(x)\bigr)$$

### Lean のコメント（日本語訳）

> 制御されたスカラー力学 \(x'=-u\) に沿って割引した候補値を微分すると、検証の恒等式で使う導関数が得られる。

### 補題の説明

積の微分（割引の指数 × 二次式）の計算です。

### 証明の概略

1. \(e^{-\rho(s-T)}\) の微分 \(-\rho e^{\cdots}\)。
2. \(x^2\) の微分 \(2x\dot x=-2xu\)。
3. 積の微分で結論。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedCandidateValue_tendsto_zero_of_integrable_inputCost"></a>

## 定理 `discountedCandidateValue_tendsto_zero_of_integrable_inputCost`

### 式

$$\text{費用が可積分}\Rightarrow F(s)\to0$$

### Lean のコメント（日本語訳）

> 有限の割引した二次費用は、横断性を供給する：割引した候補値とその導関数は、将来の半直線上で可積分になる。

### 補題の説明

**状態の有界性を仮定せずに**、費用の可積分性だけから横断性 \(F\to0\) を得ます。

### 証明の概略

1. `discountedCandidateValue_hasDerivAt` と平方の恒等式 `hamiltonian_gap_eq_square` から、\(F'(s)=\)（割引した平方残差）\(-\)（割引した費用）。
2. 割引した平方残差の可積分性：`discountedSquareGap_integrable_of_inputCost_integrable`。費用は仮定で可積分なので、\(F'\) も可積分。
3. \(F\) 自身の可積分性：\(0\le F\le\frac{rm}{q}\times\)費用（状態の項 \(qx^2\) との比較）で `Integrable.mono`。
4. \(F\) と \(F'\) がともに可積分なら \(F\to0\)（Mathlib の `tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` 型の補題）（97 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteHorizon_verification_identity"></a>

## 定理 `finiteHorizon_verification_identity`

### 式

$$\int_T^S\mathrm{cost}=F(T)-F(S)+\int_T^S\mathrm{gap}$$

### Lean のコメント（日本語訳）

> 任意の入力経路についての有限地平の検証恒等式。導関数の仮定は、\(F\) が \(x'=-u\) を満たす状態に沿った割引した候補値であることを述べる。費用は、\(F\) の減少を、非負の平方の残差の積分の分だけ上回る。

### 補題の説明

**検証恒等式**：費用の積分 ＝ 候補値の減少 ＋ 平方の残差の積分。残差が非負だから、費用 ≥ 候補値の減少。

### 証明の概略

1. `hamiltonian_gap_eq_square` で \(F'=-\)割引費用\(+\)割引した平方残差（点ごとの恒等式。\(F'=w\,(V'(-u)-\rho V)\)、`theorem26DiscountWeight` を掛けた形）。
2. 区間 \([T,S]\) で微積分の基本定理（`intervalIntegral.integral_eq_sub_of_hasDerivAt`）：\(\int_T^SF'=F(S)-F(T)\)。
3. 両辺を整理して \(\int_T^S\text{cost}=F(T)-F(S)+\int_T^S\text{gap}\)（45 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteHorizon_cost_ge_candidateDrop_general"></a>

## 定理 `finiteHorizon_cost_ge_candidateDrop_general`

### 式

$$\mathrm{cost}=-F'+\mathrm{res},\ \mathrm{res}\ge0\Rightarrow F(T)-F(S)\le\int_T^S\mathrm{cost}$$

### Lean のコメント（日本語訳）

> 一般の有限地平の検証不等式。割引費用の被積分関数が、候補値の導関数の負と非負の残差の和であるときはいつでも、累積費用は候補値の減少を上回る。これは、任意の二次モデルや特定の Hamiltonian の平方完成から独立な、比較の中核のステップである。

### 補題の説明

**モデルに依存しない**核心の補完：費用 = −(候補値の導関数)+非負の残差 ⇒ 費用の累積 ≥ 候補値の減少。

### 証明の概略

1. 微積分の基本定理で \(\int_T^S(-F')=F(T)-F(S)\)。
2. 残差の積分が非負（`integral_nonneg`）。
3. 差をとって結論（24 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedGeneralCost"></a>

## 定義 `discountedGeneralCost`

### 式

$$e^{-\rho(s-T)}L\bigl(x(s),u(s)\bigr)$$

### Lean のコメント（日本語訳）

> スカラーの状態・制御の経路に沿った、一般の指数割引費用。

### 定義の説明

任意の走る費用 \(L\) についての割引費用。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedGeneralCandidate"></a>

## 定義 `discountedGeneralCandidate`

### 式

$$F(s)=e^{-\rho(s-T)}V(x(s))$$

### Lean のコメント（日本語訳）

> スカラーの状態の経路に沿った、割引した候補値。

### 定義の説明

任意の候補値 \(V\) についての割引候補値。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedGeneralHJBResidual"></a>

## 定義 `discountedGeneralHJBResidual`

### 式

$$e^{-\rho(s-T)}\bigl[L+V'(x)f(x,u)-\rho V(x)\bigr]$$

### Lean のコメント（日本語訳）

> 力学 \(x'=f(x,u)\)、走る費用 \(L\)、微分可能な候補値 \(V\) についての、割引した HJB の残差。

### 定義の説明

一般のスカラー力学・費用での割引 HJB 残差。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteHorizon_hjb_cost_ge_candidateDrop"></a>

## 定理 `finiteHorizon_hjb_cost_ge_candidateDrop`

### 式

$$\text{HJB 残差}\ge0\Rightarrow F(T)-F(S)\le\int_T^S\text{cost}$$

### Lean のコメント（日本語訳）

> 任意のスカラー力学と走る費用についての、有限地平の HJB 検証。微分可能な候補値の Hamiltonian の残差が、競合の軌道に沿って非負なら、その割引費用は、候補値の減少を上回る。これは、平方完成の公式を仮定せずに、前の二次の例を一般化する。

### 補題の説明

二次モデルの完全平方を使わず、**HJB の残差が非負でさえあれば**検証不等式が成り立つ、という一般版です。

### 証明の概略

1. `discountedGeneralCandidate` の導関数を連鎖律で計算（`hV`, `hODE`）。
2. `cost = −F' + 残差` と残差 ≥ 0 から、`finiteHorizon_cost_ge_candidateDrop_general` を適用（49 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteHorizon_hjb_cost_ge_candidateDrop_normed"></a>

## 定理 `finiteHorizon_hjb_cost_ge_candidateDrop_normed`

### 式

$$\text{（ノルム空間上の）有限地平 HJB 検証}$$

### Lean のコメント（日本語訳）

> 任意の実ノルム空間の状態空間上での、有限地平 HJB 検証。候補値は Fréchet 微分可能で、制御された軌道は古典的な導関数を持つ。これは、ソースモデルが 1 次元でないときに使う、状態空間について一般な形である。

### 補題の説明

スカラーから**ノルム空間**（状態が \(\mathbb R^n\) など）へ一般化した検証不等式です。

### 証明の概略

1. 連鎖律（Fréchet 微分と曲線の微分）で `F' = 割引 ×(DV·f − ρV)`。
2. 費用 = −F' + 残差から有限地平の不等式を得る（43 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteHorizon_cost_ge_candidateDrop"></a>

## 定理 `finiteHorizon_cost_ge_candidateDrop`

### 式

$$F(T)-F(S)\le\int_T^S\mathrm{cost}$$（二次モデル）

### Lean のコメント（日本語訳）

> 二次の HJB の平方の残差は、一般の有限地平の検証不等式の、具体的なインスタンスを与える。

### 補題の説明

二次モデルでの、有限地平の検証不等式です。

### 証明の概略

1. `finiteHorizon_cost_ge_candidateDrop_general` に、費用 = −F' + 平方の残差 と残差 ≥ 0 を渡す（23 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_cost_ge_initialValue"></a>

## 定理 `infiniteHorizon_cost_ge_initialValue`

### 式

$$V_0-F(h_n)\le\int_T^{h_n}c\ \ \wedge\ F\to0\ \wedge\ \int_T^{h_n}c\to J\Rightarrow V_0\le J$$

### Lean のコメント（日本語訳）

> 有限地平の検証不等式から無限地平の費用への、モデルに依存しない移行。候補値は、尽くす終端の地平に沿って消えなければならず、打ち切った費用は、実際の総費用に収束しなければならない。

### 補題の説明

**極限を取る**補題です：各有限地平で \(V_0-F(h_n)\le\int_T^{h_n}c\)、\(F(h_n)\to0\)、\(\int_T^{h_n}c\to J\) から \(V_0\le J\)。

### 証明の概略

1. \(V_0-F(h_n)\) の極限が \(V_0\)、\(\int_T^{h_n}c\) の極限が \(J\)。
2. `le_of_tendsto_of_tendsto'`（不等式の極限）を適用（12 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_cost_ge_candidateValue"></a>

## 定理 `infiniteHorizon_cost_ge_candidateValue`

### 式

$$V_0\le J\quad(\text{二次モデル})$$

### Lean のコメント（日本語訳）

> 二次の制御モデルについての無限地平の検証。上のモデルに依存しない極限の定理を使う。

### 補題の説明

上の極限補題の二次モデル版です。

### 証明の概略

1. `infiniteHorizon_cost_ge_initialValue` に `cost := discountedInputCost …` を渡す（5 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_hjb_cost_ge_candidate"></a>

## 定理 `infiniteHorizon_hjb_cost_ge_candidate`

### 式

$$V(x(T))\le\int_{[T,\infty)}e^{-\rho(s-T)}L\ \mathrm ds$$（一般スカラー）

### Lean のコメント（日本語訳）

> 任意のスカラー力学と走る費用についての無限地平の検証。HJB の不等式と局所区間可積分性が、有限地平の各比較を与え、横断性と総費用の収束が、それを無限地平へ運ぶ。

### 補題の説明

一般のスカラー力学・走る費用での、無限地平の検証不等式です。

### 証明の概略

1. 各 \(n\) で `finiteHorizon_hjb_cost_ge_candidateDrop`。
2. `infiniteHorizon_cost_ge_initialValue` で極限を取る（20 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_hjb_cost_ge_candidate_normed"></a>

## 定理 `infiniteHorizon_hjb_cost_ge_candidate_normed`

### 式

$$V(x(T))\le\int_{[T,\infty)}e^{-\rho(s-T)}L\ \mathrm ds$$（ノルム空間）

### Lean のコメント（日本語訳）

> 任意の実ノルム空間の状態空間上での、無限地平 HJB の検証。Fréchet 微分を使った有限地平の定理と、モデルに依存しない、尽くす地平の極限の議論を組み合わせる。

### 補題の説明

ノルム空間版の無限地平 HJB 検証です。

### 証明の概略

1. `finiteHorizon_hjb_cost_ge_candidateDrop_normed` と `infiniteHorizon_cost_ge_initialValue`（17 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.normedMarkovTrajectoryCost"></a>

## 定義 `normedMarkovTrajectoryCost`

### 式

$$J_\pi(x,T)=\int_{[T,\infty)}e^{-\rho(s-T)}L\bigl(x_\pi(s),\pi(s,x_\pi(s))\bigr)\mathrm ds$$

### Lean のコメント（日本語訳）

> ノルム空間の状態空間で、与えられた閉ループの軌道に沿った、Borel マルコフ・フィードバックの割引費用。

### 定義の説明

フィードバックの割引費用の一般の定義です（走る費用 \(L\)、軌道の族を引数にとる）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.commonMarkovFeedback_optimal_at_pair"></a>

## 定理 `commonMarkovFeedback_optimal_at_pair`

### 式

$$J_{\pi^*}(x,T)\le J_\pi(x,T)$$

### Lean のコメント（日本語訳）

> 共通の Borel マルコフ・フィードバックは、その費用が滑らかな候補値を達成し、すべての許容な競合が一般の HJB 検証の仮定を満たす、どの初期の組でも最適である。この定理を適用するすべての初期の組に、同じ \(\pi^*\) が使われる。

### 補題の説明

**1 つの共通のフィードバック** \(\pi^*\) が、検証の仮定を満たす競合のすべてに対して最適であることを述べる、一般定理です（自律系）。

### 証明の概略

1. \(\pi^*\) の費用が候補値 \(V(x)\) に等しい（仮定）。
2. 競合 \(\pi\) について `infiniteHorizon_hjb_cost_ge_candidate_normed` で \(V(x)\le J_\pi\)（10 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.normedMarkovTrajectoryCostTimeDependent"></a>

## 定義 `normedMarkovTrajectoryCostTimeDependent`

### 式

$$J_\pi(x,T)=\int e^{-\rho(s-T)}L(x_\pi(s),\pi,s)\mathrm ds$$（時間依存）

### Lean のコメント（日本語訳）

> 時間に依存する走る価値についての割引費用。

### 定義の説明

走る費用が時刻に依存してよい版です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.jointValueAlongTrajectory_hasDerivAt"></a>

## 定理 `jointValueAlongTrajectory_hasDerivAt`

### 式

$$\frac{d}{dt}V(x(t),t)=\mathrm dV(x(s),s)\bigl(f(x,u,s),1\bigr)$$

### Lean のコメント（日本語訳）

> 非自律の制御された ODE の解に沿った、合同 Fréchet 微分可能な時間依存の価値の連鎖律。

### 補題の説明

時間と状態の組での連鎖律です。

### 証明の概略

1. \(t\mapsto(x(t),t)\) の微分は \((f,1)\)。
2. `HasFDerivAt.comp_hasDerivAt`。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_hjb_cost_ge_candidate_timeDependent"></a>

## 定理 `infiniteHorizon_hjb_cost_ge_candidate_timeDependent`

### 式

$$V(x(T),T)\le\int e^{-\rho(s-T)}L(x,u,s)\mathrm ds$$

### Lean のコメント（日本語訳）

> 時間依存の費用と候補値についての、与えられた制御された軌道に沿った無限地平の HJB 検証。\(G\) は、その軌道に沿った \(V(x(t),t)\) の導関数であり、呼び出す側が、非自律の閉ループ方程式と正則性の仮定から確立する。HJB の不等式は \(L+G-\rho V\ge0\) である。

### 補題の説明

時間依存版の無限地平検証です。

### 証明の概略

1. 時間依存の有限地平の検証（候補値の導関数 \(G\) を使う）を各 \(n\) で行い、`infiniteHorizon_cost_ge_initialValue` で極限を取る（51 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.commonMarkovFeedback_optimal_at_pair_timeDependent"></a>

## 定理 `commonMarkovFeedback_optimal_at_pair_timeDependent`

### 式

$$J_{\pi^*}\le J_\pi$$（時間依存）

### Lean のコメント（日本語訳）

> 単一の Borel マルコフ・フィードバックは、それが候補値を達成し、すべての許容な競合が時間依存の HJB 検証の条件を満たすとき、非自律モデルのこの初期の組で最適である。

### 補題の説明

時間依存版の共通フィードバックの最適性。

### 証明の概略

1. `infiniteHorizon_hjb_cost_ge_candidate_timeDependent` を競合に適用（10 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_hjb_cost_ge_candidate_joint"></a>

## 定理 `infiniteHorizon_hjb_cost_ge_candidate_joint`

### 式

$$V(x(T),T)\le\int e^{-\rho(s-T)}L\,\mathrm ds$$（合同 Fréchet）

### Lean のコメント（日本語訳）

> 合同 Fréchet 微分可能な、時間と状態の値による、無限地平の HJB 検証。HJB の残差の全微分は、非自律の ODE と合同 Fréchet 微分から得られ、無関係な軌道の仮定として与えられるのではない。

### 補題の説明

`jointValueAlongTrajectory_hasDerivAt` で全微分を作り、時間依存版へ渡す形です。

### 証明の概略

1. `jointValueAlongTrajectory_hasDerivAt` で \(G\) を構成。
2. `infiniteHorizon_hjb_cost_ge_candidate_timeDependent` を適用（18 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable"></a>

## 定理 `infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable`

### 式

$$\text{候補値・残差・費用が }[T,\infty)\text{ で可積分}\Rightarrow V\le\int\cdots$$

### Lean のコメント（日本語訳）

> 極限のすべての仮定を、半直線上の可積分性から導いた、合同 Fréchet 検証。候補値、HJB の残差、走る費用は、\([T,\infty)\) 上で可積分であることを要求され、これらは、横断性、局所区間可積分性、打ち切った費用の収束を意味する。

### 補題の説明

仮定を**可積分性だけ**に減らした版です。

### 証明の概略

1. `integrable_future_tendsto_zero_of_hasDerivAt` で横断性。
2. `integrable_future_intervalIntegrable` で局所可積分性。
3. `integrable_future_interval_tendsto_integral` で費用の収束。
4. `infiniteHorizon_hjb_cost_ge_candidate_joint` を適用（73 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainModel_jointHJB_candidate_le_cost_of_integrable"></a>

## 定理 `gainModel_jointHJB_candidate_le_cost_of_integrable`

### 式

$$rm\,x(T)^2\le\int_{[T,\infty)}\text{discountedInputCost}$$

### Lean のコメント（日本語訳）

> スカラーの二次の制御モデルは、合同 Fréchet の無限地平 HJB 検証子のインスタンスである。有限の割引した走る費用は、候補値の可積分性、残差の可積分性、横断性、極限の費用積分を供給する。

### 補題の説明

ゲイン・モデルで、**任意の入力 \(u(\cdot)\)** について、候補値 \(rmx(T)^2\) が割引費用の下界になることを示す、このファイルの中心の結果の 1 つです。

### 証明の概略

1. `gainJointValue_hasFDerivAt` と平方の恒等式で HJB の残差が非負（平方）。
2. 費用が可積分なら、候補値・残差が可積分（`…_integrable_of_inputCost_integrable`）。
3. `infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable` を適用（58 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.commonMarkovFeedback_optimal_at_pair_joint"></a>

## 定理 `commonMarkovFeedback_optimal_at_pair_joint`

### 式

$$J_{\pi^*}\le J_\pi$$（合同 Fréchet）

### Lean のコメント（日本語訳）

> 共通フィードバックの検証定理で、軌道に沿った候補値の導関数が、合同 Fréchet 微分可能な値と、非自律の閉ループ ODE から導かれる。

### 補題の説明

共通のフィードバックの最適性の、合同 Fréchet 版です。

### 証明の概略

1. 軌道に沿った \(V(x(t),t)\) の導関数を、合同 Fréchet 微分と閉ループ ODE から `jointValueAlongTrajectory_hasDerivAt` で得る（\(G(y,v,t)=\mathrm dV(y,t)(f(y,v,t),1)\)）。
2. 時間依存版の共通フィードバックの最適性 `commonMarkovFeedback_optimal_at_pair_timeDependent` に、この \(V_c,G_c\) と HJB の仮定・極限の仮定を渡して結論を得る（66 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.commonMarkovFeedback_optimal_at_pair_joint_of_integrable"></a>

## 定理 `commonMarkovFeedback_optimal_at_pair_joint_of_integrable`

### 式

$$J_{\pi^*}\le J_\pi$$（可積分性の仮定だけ）

### Lean のコメント（日本語訳）

> 競合の候補値、残差、費用が将来の半直線上で可積分であるとき、1 つの共通の Borel マルコフ・フィードバックについての、組ごとの最適性。これは、横断性と地平の極限を内部で導く。

### 補題の説明

仮定を可積分性に絞った、共通フィードバックの最適性です。

### 証明の概略

1. `infiniteHorizon_hjb_cost_ge_candidate_joint_of_integrable` を競合に適用（10 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedIntegrand"></a>

## 定義 `discountedIntegrand`

### 式

$$e^{-\rho(s-T)}\,\ell_\alpha\bigl(x_\alpha(s)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゲイン \(\alpha\) の政策の被積分関数。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.policyValue"></a>

## 定義 `policyValue`

### 式

$$J_\alpha(x,T)=\int_{[T,\infty)}\text{discountedIntegrand}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゲイン政策の価値。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.admissible"></a>

## 定義 `admissible`

### 式

$$\mathrm{adm}(\alpha,x,T)\equiv\text{True}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

すべてのゲインを許容とする定義です（ゲインの族の中での比較）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.modelRunningValue"></a>

## 定義 `modelRunningValue`

### 式

$$\ell_\alpha\bigl(x_\alpha(s)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理26のインターフェースに渡す走る価値。

### 証明の概略

1. 定義：`runningCost m ρ r a (trajectory a x t s)`。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalValue"></a>

## 定義 `optimalValue`

### 式

$$V^*(x,t)=rm\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適値（候補値と同じ）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedFeedbackValue_eq_policyValue"></a>

## 定理 `discountedFeedbackValue_eq_policyValue`

### 式

$$\text{定理26の価値}=J_\alpha$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理26のインターフェース（`discountedFeedbackValue`）の価値が、ここで定義した `policyValue` と一致する。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Theorem24_26_GainControl.discountedIntegrand_eq_linearFamily"></a>

## 定理 `discountedIntegrand_eq_linearFamily`

### 式

$$\text{integrand}=\text{LinearFamily の integrand}\ (q=rm(m+\rho)+r\alpha^2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲイン政策の被積分関数が、`Theorem24_26_LinearFamily` の \(\lambda=\alpha\)、\(q=rm(m+\rho)+r\alpha^2\) の被積分関数に一致する。

### 証明の概略

1. 定義を展開し、`runningCost_eq_coeff` で書き換える。

----

<a id="Tomabechi.Theorem24_26_GainControl.policyValue_eq_linearValue"></a>

## 定理 `policyValue_eq_linearValue`

### 式

$$J_\alpha=V_{\rm Linear}(\alpha,\rho,q_\alpha,x,T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲイン政策の価値が `Theorem24_26_LinearFamily.value` に一致する。

### 証明の概略

1. `discountedIntegrand_eq_linearFamily` による積分の書き換え。

----

<a id="Tomabechi.Theorem24_26_GainControl.policyValue_eq_formula"></a>

## 定理 `policyValue_eq_formula`

### 式

$$J_\alpha(x,T)=\frac{rm(m+\rho)+r\alpha^2}{\rho+2\alpha}\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**ゲイン政策の価値の公式**（`Theorem24_26_LinearFamily.value_eq_formula` から）。

### 証明の概略

1. `policyValue_eq_linearValue` と `Theorem24_26_LinearFamily.value_eq_formula`。

----

<a id="Tomabechi.Theorem24_26_GainControl.costCoefficient_sub_optimal"></a>

## 定理 `costCoefficient_sub_optimal`

### 式

$$\frac{rm(m+\rho)+ra^2}{\rho+2a}-rm=\frac{r(a-m)^2}{\rho+2a}$$

### Lean のコメント（日本語訳）

> 平方完成により、選ばれたゲイン \(m\) に対する費用の差が得られる。

### 補題の説明

費用係数と最適係数 \(rm\) の差が、**完全平方**になることの計算です。

### 証明の概略

1. 通分して整理（`field_simp` と `ring`）。

----

<a id="Tomabechi.Theorem24_26_GainControl.costCoefficient_minimal"></a>

## 定理 `costCoefficient_minimal`

### 式

$$r>0\Rightarrow rm\le\frac{rm(m+\rho)+ra^2}{\rho+2a}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

費用係数が \(rm\) 以上であること（差が \(\frac{r(a-m)^2}{\rho+2a}\ge0\)）。

### 証明の概略

1. `costCoefficient_sub_optimal` と、非負性。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_attains"></a>

## 定理 `optimalGain_attains`

### 式

$$J_m(x,T)=rm\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適ゲイン \(m\) の価値が \(rmx^2\) になること。

### 証明の概略

1. `policyValue_eq_formula` に \(\alpha=m\) を代入して整理（8 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_minimal_among_transversalInputs"></a>

## 定理 `optimalGain_minimal_among_transversalInputs`

### 式

$$J_m(x_0,T)\le\int e^{-\rho(s-T)}\ell(x,u)\,\mathrm ds$$（横断性を満たす任意の入力）

### Lean のコメント（日本語訳）

> 任意の実数値の制御に対する検証定理。割引した候補値の導関数の恒等式、有限地平の可積分性、横断性の条件を満たす、任意の入力と状態の対は、最適ゲインのフィードバックの費用以上の費用を持つ。これは、もはや競合を定数の線形ゲインに制限しない。

### 補題の説明

**競合を任意の実数値の入力に広げた**検証定理です（横断性を仮定）。

### 証明の概略

1. 区間可積分性：残差は `discountedSquareGap_intervalIntegrable_of_inputCost_integrable`、費用は `discountedInputCost_intervalIntegrable_of_integrable`。
2. 各 \(n\) の有限地平の不等式：`finiteHorizon_cost_ge_candidateDrop`（\(F\) の導関数は `discountedCandidateValue_hasDerivAt`、残差の非負性は `hamiltonian_gap_eq_square`）。
3. 有限地平の積分の極限（`discountedInputCost_interval_tendsto_futureIntegral`）と横断性 \(F\to0\) から、`infiniteHorizon_cost_ge_candidateValue` で \(V(x_0)\le\int\text{cost}\)。左辺は `optimalGain_attains` で \(J_m\)（80 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_minimal_among_integrableInputs"></a>

## 定理 `optimalGain_minimal_among_integrableInputs`

### 式

$$\text{費用が可積分}\Rightarrow J_m(x_0,T)\le\int\cdots$$

### Lean のコメント（日本語訳）

> 有限な割引費用それ自身が横断性を意味するので、任意の可測な入力経路について、別に有界な状態の仮定は必要ない。

### 補題の説明

横断性を、費用の可積分性から導いた版です（`discountedCandidateValue_tendsto_zero_of_integrable_inputCost`）。

### 証明の概略

1. 状態 \(x\) の連続性（ODE の解）から可測、入力 \(u=-x'\) も可測（`measurable_deriv`）。
2. `gainModel_jointHJB_candidate_le_cost_of_integrable`（合同 Fréchet の HJB 検証）で \(rmx_0^2\le\int\text{cost}\)。
3. 左辺 \(J_m=rmx_0^2\)（`optimalGain_attains`）で書き換える（35 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_minimal_among_boundedInputs"></a>

## 定理 `optimalGain_minimal_among_boundedInputs`

### 式

$$\|x\|\le B,\ \text{努力が可積分}\Rightarrow J_m\le\int\cdots$$

### Lean のコメント（日本語訳）

> 将来の状態が有界であることは、任意の入力の検証定理における、横断性の仮定の、具体的な十分条件である。

### 補題の説明

横断性を、状態の有界性＋努力の可積分性から導く版です。

### 証明の概略

1. `discountedCandidateValue_tendsto_zero_of_bounded_state` と `discountedInputCost_integrable_of_boundedState_and_effort`、`optimalGain_minimal_among_transversalInputs`（10 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.markovFeedbackInput"></a>

## 定義 `markovFeedbackInput`

### 式

$$u(s)=\pi(s,x(s))$$

### Lean のコメント（日本語訳）

> 与えられた状態の軌道に沿って、Borel マルコフ・フィードバックが選ぶ制御。

### 定義の説明

フィードバックを軌道に沿って評価した入力です。

### 証明の概略

1. 定義：`π.action (s, x s)`。

----

<a id="Tomabechi.Theorem24_26_GainControl.markovTrajectoryCost"></a>

## 定義 `markovTrajectoryCost`

### 式

$$J(\pi,x)=\int_{[T,\infty)}e^{-\rho(s-T)}\ell\bigl(x(s),\pi(s,x(s))\bigr)\mathrm ds$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

軌道 \(x(\cdot)\) に沿った、フィードバック \(\pi\) の実際の軌道積分としての費用。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.markovTrajectoryCost_feedback_eq_policyValue"></a>

## 定理 `markovTrajectoryCost_feedback_eq_policyValue`

### 式

$$J(\pi_\alpha,x_\alpha)=J_\alpha(x_0,T)$$

### Lean のコメント（日本語訳）

> 係数の政策の積分価値は、対応する閉ループの流れに沿った、その単一の大域 Borel マルコフ写像が生成する費用に、まさに等しい。

### 補題の説明

`policyValue`（ゲインの族の価値）と、**実際の Borel マルコフ・フィードバックの軌道積分**が一致することの確認です。

### 証明の概略

1. `feedback_action` と `trajectory` の定義を展開し、被積分関数が一致することを示す（9 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_markovFeedback_attains_value"></a>

## 定理 `optimalGain_markovFeedback_attains_value`

### 式

$$J(\pi_m,x_m)=V^*(x_0,T)$$

### Lean のコメント（日本語訳）

> 共通の Borel マルコフ・フィードバックは、ゲインの族の `policyValue` だけでなく、実際の軌道積分として、候補の最適値を達成する。

### 補題の説明

最適フィードバックが、実際の軌道積分で最適値 \(rmx_0^2\) を達成する。

### 証明の概略

1. `markovTrajectoryCost_feedback_eq_policyValue` と `optimalGain_attains`（4 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.FiniteCostMarkovTrajectory"></a>

## 定義 `FiniteCostMarkovTrajectory`

### 式

$$\text{(i) }x(T)=x_0,\ \text{(ii) }\dot x=-\pi(s,x),\ \text{(iii) 割引費用が可積分}$$

### Lean のコメント（日本語訳）

> 許容な有限費用の Markov 軌道は、1 つの大域フィードバックと、指定した初期の組からの古典的な閉ループ経路、有限の割引した走る費用を記録する。

### 定義の説明

「競合」の定義です：Borel マルコフ・フィードバック \(\pi\) と、その閉ループの（すべての \(s\) で微分可能な）軌道 \(x(\cdot)\)、有限の割引費用の組。

### 証明の概略

1. 述語の定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteCostMarkovTrajectoryValues"></a>

## 定義 `finiteCostMarkovTrajectoryValues`

### 式

$$\{J(\pi,x)\mid\mathrm{FiniteCost}(\pi,x)\}$$

### Lean のコメント（日本語訳）

> Borel マルコフのクラスの、固定された初期の組から、許容な古典的閉ループ軌道が達成する、すべての有限の割引費用の集合。

### 定義の説明

競合が達成できる費用の集合です。

### 証明の概略

1. 集合の定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_minimal_among_boundedMarkovFeedback"></a>

## 定理 `optimalGain_minimal_among_boundedMarkovFeedback`

### 式

$$\text{状態有界・努力可積分}\Rightarrow J_m(x_0,T)\le J(\pi,x)$$

### Lean のコメント（日本語訳）

> 閉ループの軌道が有界な状態と有限の割引した入力の努力を持つ、任意の Borel マルコフ・フィードバックは、この初期の組について、共通の最適な線形フィードバックより小さい費用にはなり得ない。

### 補題の説明

競合を**任意の Borel マルコフ・フィードバック**にした最適性です（有界性つき）。

### 証明の概略

1. `optimalGain_minimal_among_boundedInputs` を、`u := markovFeedbackInput π x` で適用（7 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_minimal_among_integrableMarkovFeedback"></a>

## 定理 `optimalGain_minimal_among_integrableMarkovFeedback`

### 式

$$\text{費用が可積分}\Rightarrow J_m(x_0,T)\le J(\pi,x)$$

### Lean のコメント（日本語訳）

> 古典的な閉ループ軌道と有限の割引した走る費用を持つ、すべての Borel マルコフ・フィードバックは、最適な線形フィードバックにより支配される。競合の軌道に有界性の仮定は必要ない。

### 補題の説明

有界性なしの、競合が任意の（有限費用の）Borel マルコフ・フィードバックである最適性です。

### 証明の概略

1. `optimalGain_minimal_among_integrableInputs` を、`u := markovFeedbackInput π x` で適用（6 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_commonMarkovFeedback_all_initial_pairs"></a>

## 定理 `optimalGain_commonMarkovFeedback_all_initial_pairs`

### 式

$$\forall(x_0,T),\ \forall\pi\ \text{競合},\ J(\pi_m,x_m)\le J(\pi,x)$$

### Lean のコメント（日本語訳）

> 同じ 1 つの Borel マルコフ・フィードバックが、スカラーモデルの、すべての初期の状態・時刻の組で、古典的な閉ループ軌道が有限の割引費用を持つ、任意の競合 Borel マルコフ・フィードバックに対して、最適である。競合の存在の仮定は、組とフィードバックに応じて変わってよいが、最小化するフィードバック `feedback ⟨m, hm⟩` は変わらない。

### 補題の説明

**共通のフィードバック `feedback ⟨m,hm⟩` が、すべての初期の組で最適**（競合の仮定は組ごとに変わってよい）。論文の定理26が要求する「単一の共通フィードバック」の具体例です。

### 証明の概略

1. 任意の初期の組・競合 \(\pi\) について、`optimalGain_minimal_among_integrableMarkovFeedback` で \(J_m\le\) 競合の費用。
2. 最適フィードバック自身の軌道積分が \(J_m\) に一致すること（`markovTrajectoryCost_feedback_eq_policyValue`）で、左辺を最適フィードバックの `markovTrajectoryCost` に置き換える（29 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalValue_isLeast_finiteCostMarkovTrajectories"></a>

## 定理 `optimalValue_isLeast_finiteCostMarkovTrajectories`

### 式

$$V^*(x_0,T)=\min\{J(\pi,x)\mid\text{FiniteCost}\}$$

### Lean のコメント（日本語訳）

> `optimalValue` は、この初期の組についての、有限費用の古典的な閉ループの Borel マルコフ軌道の、実際に達成される費用の集合の、最小の元である。最小は、単一の線形フィードバックによって達成される。

### 補題の説明

最適値が、**実際に達成される費用の集合の最小値**であることです（`IsLeast`）。

### 証明の概略

1. 最小元であること：最適フィードバック `feedback ⟨m,hm⟩` の軌道 `trajectory` が `FiniteCostMarkovTrajectory` を満たすことを示す（初期値、ODE `trajectory_hasDerivAt`・`feedback_action`・`controlOutput_eq`、費用が `Theorem24_26_LinearFamily.discountedIntegrand` に一致 `discountedIntegrand_eq_linearFamily` して可積分）。その費用が最適値（`optimalGain_markovFeedback_attains_value`）。
2. 下界：任意の競合の費用が最適値以上（`optimalGain_commonMarkovFeedback_all_initial_pairs`）（48 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost"></a>

## 定理 `markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost`

### 式

$$J(\pi,x)=0\iff\ell\bigl(x(s),\pi(s,x(s))\bigr)=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 有限費用の古典的な閉ループの Borel マルコフ軌道のそれぞれについて、割引費用が 0 であることは、瞬間的な制御費用がほとんど至るところ 0 であることと同値である。正の指数割引は、非零の費用を隠せない。

### 補題の説明

**割引費用 = 0 ⇔ 走る費用が a.e. で 0**。PZS の定義（走る価値が a.e. で 0）と、割引した積分の値 0 を結ぶ補題です。

### 証明の概略

1. 非負で可積分な関数の積分が 0 ⇔ a.e. で 0（`integral_eq_zero_iff_of_nonneg`）。
2. 割引の重みが正なので、重み付けしても a.e. の 0 は変わらない。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalValue_eq_zero_iff_exists_finiteCostMarkovPZS"></a>

## 定理 `optimalValue_eq_zero_iff_exists_finiteCostMarkovPZS`

### 式

$$V^*(x_0,T)=0\iff\exists(\pi,x)\ \text{有限費用},\ \ell=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> スカラーの二次モデルで、最適値が 0 であるのは、ちょうど、ある有限費用の古典的な閉ループ Borel マルコフ政策が、ほとんど至るところ永続的に零費用であるときである。これは、実際の任意のフィードバックの比較クラスを、PZS の定義に結びつける。一般の Borel フィードバックのため、古典的な有限費用の軌道の存在は、証人に明示されている。

### 補題の説明

最適値 0 ⇔ 競合のクラスに PZS の証人がいる、という結びつけです。

### 証明の概略

1. (⇒)：最適フィードバックが証人（`optimalValue_isLeast_…` と `markovTrajectoryCost_eq_zero_iff_ae_zero_runningCost`）。
2. (⇐)：証人の費用が 0 ⇒ 最適値 ≤ 0（最小性）。最適値 ≥ 0 から 0（22 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteCostMarkovTrajectory_satisfies_condition24A"></a>

## 定理 `finiteCostMarkovTrajectory_satisfies_condition24A`

### 式

$$x_0\ne0\Rightarrow\neg\bigl(\ell=0\ \text{a.e.}\bigr)$$

### Lean のコメント（日本語訳）

> 条件 24-A は、初期状態が非零のとき、スカラーモデルのすべての Borel マルコフ・フィードバック軌道について導かれる。フィードバックが、後で状態を 0 に駆動しても、連続性と正の状態費用の項が、正の測度の初期区間で、厳密に正の走る費用を強制する。

### 補題の説明

**条件 24-A を導出**：初期状態が非零なら、連続性により、初期の短い区間で状態は非零のままで、走る費用が厳密に正になる（その区間の測度は正）。

### 証明の概略

1. \(x\) は連続で \(x(T)=x_0\ne0\) なので、\(T\) の近傍で \(x\ne0\)。
2. その区間で \(\ell\ge qx^2>0\)。
3. 正測度の集合で \(\ell>0\) なので、a.e. で 0 でない（61 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalValue_pos_of_nonzero_initial_via_condition24A"></a>

## 定理 `optimalValue_pos_of_nonzero_initial_via_condition24A`

### 式

$$x_0\ne0\Rightarrow V^*(x_0,T)>0$$

### Lean のコメント（日本語訳）

> 定理24の厳密に正の最適値の結論は、このモデルで、有限費用の古典的な Borel マルコフ軌道のクラス全体に適用される。非零のすべての初期状態について、競合のそれぞれに条件 24-A が上で導かれ、達成される共通のフィードバックは、大域的に最小である。

### 補題の説明

**定理24の結論**（24-A ⇒ 最適値が正）が、競合のクラス全体に対して成り立つ、このモデルでの具体的な確認です。

### 証明の概略

1. 全競合のクラスで、各競合が条件 24-A を満たす（`finiteCostMarkovTrajectory_satisfies_condition24A`）ことを示す。
2. 最適値が競合の費用の最小（`optimalValue_isLeast_finiteCostMarkovTrajectories`）で、達成される。割引の重みが a.e. 正（`theorem26DiscountWeight_pos_ae`）。
3. 一般定理 `theorem24_positive_optimal_value_of_condition24A` を適用して最適値が正（55 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.HasFiniteCostMarkovPZS"></a>

## 定義 `HasFiniteCostMarkovPZS`

### 式

$$\exists(\pi,x)\ \text{有限費用},\ \ell=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 固定した初期の組からの、有限費用の古典的な閉ループ Borel マルコフ軌道のすべての中での、永続的零苦の政策の存在。

### 定義の説明

競合のクラスでの PZS の存在を述べる述語です。

### 証明の概略

1. 述語の定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.finiteCostMarkovPZS_iff_mem_zeroTarget"></a>

## 定理 `finiteCostMarkovPZS_iff_mem_zeroTarget`

### 式

$$\mathrm{HasFiniteCostMarkovPZS}\iff x_0\in N=\{0\}$$

### Lean のコメント（日本語訳）

> 有限費用の古典的な Markov 軌道のクラス全体で、永続的な零苦は、零最適値の目標への所属と、まさに同値である。前向きと逆向きの含意は、最適費用の比較・達成と、割引の重みの正値性を使う。

### 補題の説明

**競合のクラス全体で、PZS ⇔ 零価値目標**。

### 証明の概略

1. `optimalValue_eq_zero_iff_exists_finiteCostMarkovPZS` で PZS ⇔ 最適値 0。
2. 最適値 \(rmx_0^2=0\iff x_0=0\)（17 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_is_minimal"></a>

## 定理 `optimalGain_is_minimal`

### 式

$$J_m(x,T)\le J_a(x,T)\quad(\forall a>0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲインの族の中で、\(m\) が最小の価値を持つ。

### 証明の概略

1. `policyValue_eq_formula` と `costCoefficient_minimal` から（\(x^2\ge0\)）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_PZS_iff_zeroTarget"></a>

## 定理 `optimalGain_PZS_iff_zeroTarget`

### 式

$$\mathrm{PZS}(x,T)\iff x\in N$$（ゲインの族）

### Lean のコメント（日本語訳）

> 上位層の永続的零価値政策は、連続なゲイン制御問題の零価値目標にちょうど一致する。

### 補題の説明

ゲインの族を許容な政策としたときの、定理26のインターフェースでの **PZS ⇔ 目標** です。

### 証明の概略

1. 割引費用の被積分関数を `Theorem24_26_LinearFamily` のもの（`discountedIntegrand_eq_linearFamily`、`runningCost_eq_coeff`）に一致させ、可積分性を `Theorem24_26_LinearFamily.discountedIntegrand_integrable` から得る。
2. 最適値の達成 `optimalGain_attains`・最小性 `optimalGain_is_minimal`、価値の一致 `discountedFeedbackValue_eq_policyValue`。
3. `feedbackPZS_iff_mem_theorem26ZeroValueTarget`（定理26：PZS ⇔ 零価値目標）に渡し、目標は `zeroTarget_eq_singleton` で書き換える（66 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_unique"></a>

## 定理 `optimalGain_unique`

### 式

$$\frac{rm(m+\rho)+ra^2}{\rho+2a}=rm\Rightarrow a=m$$

### Lean のコメント（日本語訳）

> 選ばれたゲインは、別のゲインが同じ最小費用係数を持つときはいつでも、一意の最小化元である。

### 補題の説明

最小化元の**一意性**です。

### 証明の概略

1. `costCoefficient_sub_optimal` から \(\frac{r(a-m)^2}{\rho+2a}=0\)、\(r>0\) なので \(a=m\)（12 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_full_convergence"></a>

## 定理 `optimalGain_full_convergence`

### 式

$$W\le W_0e^{-2m(s-T)},\ d\le\sqrt{W_0}e^{-m(s-T)},\ V\to0,\ (W=0\iff\text{target})$$

### Lean のコメント（日本語訳）

> 最適フィードバックの閉ループは、検証された正率の線形族から、定理26の条件付きの結論をすべて継承する。

### 補題の説明

`Theorem24_26_LinearFamily.full_convergence` を、\(\lambda=m\) で使った結論です。

### 証明の概略

1. `Theorem24_26_LinearFamily.full_convergence`（\(\lambda=m\)、\(q=rm(m+\rho)+rm^2\)）を得る。
2. 価値の極限の部分は、`policyValue_eq_linearValue` で `policyValue` と `Theorem24_26_LinearFamily.value` が一致することで書き換える（25 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainOptimalZeroTarget"></a>

## 定義 `gainOptimalZeroTarget`

### 式

$$N(s)=\{x\mid V^*(x,s)=0\}$$

### Lean のコメント（日本語訳）

> ゲイン・モデルの実際の最適値で定義した、動く目標。

### 定義の説明

最適値 \(rmx^2\) による零価値目標（`Theorem24_26_LinearFamily.zeroTarget` ではなく、モデル自身の最適値で定義）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainOptimalZeroTarget_eq_singleton"></a>

## 定理 `gainOptimalZeroTarget_eq_singleton`

### 式

$$N(s)=\{0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零価値の点は 0 だけ。

### 証明の概略

1. \(rmx^2=0\iff x=0\)（\(r,m>0\)）（14 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_satisfies_condition26A"></a>

## 定理 `optimalGain_satisfies_condition26A`

### 式

$$\text{26-A の Lyapunov・目標・値の係数の評価（}\omega(d)=rm\,d^2\text{）}$$

### Lean のコメント（日本語訳）

> 二次モデルの実際の最適 Borel フィードバックについての、条件 26-A の、Lyapunov、目標、値の係数の条項の直接の検証。ここで \(W=|x|^2\)、目標は証明された最適値の零集合で、\(\omega(d)=rmd^2\) であり、両方の距離の比較は定数 1 で成り立つ。

### 補題の説明

**26-A を、モデルの実際の最適値から直接検証**したものです（線形族の収束の近道を使わない）。

### 証明の概略

1. alive 不変性（\(\mathbb R\) 全体）、目標が \(\{0\}\)（`gainOptimalZeroTarget_eq_singleton`）。
2. `Theorem24_26_LinearFamily.WAlong_hasDerivAt` で右傾斜条件（`RightSlopeBound`）、距離評価、値 \(=rm\,d^2\)（24 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.optimalGain_full_convergence_from_condition26A"></a>

## 定理 `optimalGain_full_convergence_from_condition26A`

### 式

$$\text{（上の）26-A 一式}\Rightarrow\text{定理26の動的結論}$$

### Lean のコメント（日本語訳）

> モデルから導いた 26-A のパッケージを、一般の定理26に入れることで、すべての動的結論を導き直す。これは、意図した依存の向きを検証する：収束の結果は、別の線形族の収束の近道ではなく、証明されたソースの条項を使う。

### 補題の説明

`optimalGain_satisfies_condition26A` の出力を、一般定理 `theorem26_full_conditional_convergence_of_rightSlopeBound` に渡して、収束の結論を導き直します。

### 証明の概略

1. `optimalGain_satisfies_condition26A` で 26-A 一式を得る。
2. 一般の定理26 `…_of_rightSlopeBound` を適用（67 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.theorem24To26GainControlStatement"></a>

## 定義 `theorem24To26GainControlStatement`

### 式

$$\text{下位層の定理24}\ \wedge\ \text{上位層の PZS 同値}\ \wedge\ \text{定量収束}$$

### Lean のコメント（日本語訳）

> 定理24（下位層）と定理26（上位のスカラーモデル）の結合した結果。PZS の同値と定量的な収束を含む。

### 定義の説明

結論をまとめた命題（`Prop`）の定義です（20 行）。

### 証明の概略

1. 命題の定義のみ（各成分は既出の定理）。

----

<a id="Tomabechi.Theorem24_26_GainControl.theorem24_to26_gain_control_bridge"></a>

## 定理 `theorem24_to26_gain_control_bridge`

### 式

$$\text{theorem24To26GainControlStatement}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`theorem24To26GainControlStatement` が成り立つこと。

### 証明の概略

1. `lower_model_theorem24`、`optimalGain_PZS_iff_zeroTarget`、`optimalGain_full_convergence` を並べる（10 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.theorem24_to26_gain_control_bridge_all_initial_pairs"></a>

## 定理 `theorem24_to26_gain_control_bridge_all_initial_pairs`

### 式

$$\forall(x,T):\ \text{Statement}\ \wedge\ \bigl(J(\pi_m,x_m)=V^*\ \wedge\ \forall\text{競合},\ V^*\le J(\pi,x)\bigr)$$

### Lean のコメント（日本語訳）

> スカラーのゲイン・モデルの、すべての初期の組での、完全な定理24→26の橋。1 つの具体的なフィードバック写像による、すべての有限費用の古典的な Markov の競合に対する最小化を含む。

### 補題の説明

すべての初期の組での結合結果です。

### 証明の概略

1. 各初期の組 \((x,T)\) で `theorem24_to26_gain_control_bridge` を適用。
2. 最適フィードバックの軌道積分の達成（`optimalGain_markovFeedback_attains_value`）と、競合に対する最小性（`optimalGain_commonMarkovFeedback_all_initial_pairs`）を組にする（31 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.theorem24_to26_gain_control_full_classification"></a>

## 定理 `theorem24_to26_gain_control_full_classification`

### 式

$$\text{下位 24-A}\ \wedge\ (x\ne0\Rightarrow V^*>0)\ \wedge\ \text{PZS}\iff\text{target}\ \wedge\ \text{共通フィードバックの最適性}\ \wedge\ \text{26 の収束}$$

### Lean のコメント（日本語訳）

> スカラーの二次の制御モデルについての、統合された定理24→26の結果。下位層は 24-A を満たし、上位層では、非零のすべての初期状態が正の最適値を持ち、任意の有限費用の古典的な Borel マルコフの PZS が、零価値目標でちょうど存在し、同じフィードバックがすべての初期の組で最適であり、モデルから導いた 26-A の条件が、定量的な収束を与える。

### 補題の説明

**このモデルの総まとめ**の定理です。

### 証明の概略

1. `lower_model_theorem24`（下位）、`optimalValue_pos_of_nonzero_initial_via_condition24A`、`finiteCostMarkovPZS_iff_mem_zeroTarget`、`theorem24_to26_gain_control_bridge_all_initial_pairs` を並べる（11 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.GainSourceAbstraction"></a>

## 定義 `GainSourceAbstraction`

### 式

$$\{\text{false}<\text{true}=\top\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の抽象の順序（`Bool`）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_GainControl.GainSourceState"></a>

## 定義 `GainSourceState`

### 式

$$\text{false}\mapsto\text{Unit},\ \text{true}\mapsto\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの状態の型。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.GainSourceFeedback"></a>

## 定義 `GainSourceFeedback`

### 式

$$\text{false}\mapsto\text{PUnit},\ \text{true}\mapsto\Pi_{\ge0}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとのフィードバックの型（上位は非負時間の Borel マルコフ）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourcePolicy"></a>

## 定義 `gainSourcePolicy`

### 式

$$\pi_\alpha(t,x)=\alpha x\ \ (t\ge0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゲイン \(\alpha\) の線形フィードバックを、非負時間の Borel マルコフ・フィードバックとして与える。

### 証明の概略

1. 作用 `fun p => a.1 * p.2`、可測性は `fun_prop`。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourcePolicy_injective"></a>

## 定理 `gainSourcePolicy_injective`

### 式

$$\pi_\alpha=\pi_\beta\Rightarrow\alpha=\beta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲインから方策への対応が単射であること（方策が等しければゲインも等しい）。

### 証明の概略

1. 作用を \(x=1\) で評価して \(\alpha=\beta\)（7 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceAdmissible"></a>

## 定義 `gainSourceAdmissible`

### 式

$$\mathrm{adm}(\pi)\iff\exists\alpha>0,\ \pi=\pi_\alpha$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

許容な政策を、ゲイン政策だけに制限する定義です。

### 証明の概略

1. 存在量化で定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourcePolicyGain"></a>

## 定義 `gainSourcePolicyGain`

### 式

$$\pi\mapsto\alpha\ \text{（許容なら元のゲイン、さもなくば }m\text{）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

政策の作用を \((t,x)=(0,1)\) で評価した値 \(\pi(0,1)\) が正ならそれをゲインとして返し、そうでなければ最適ゲイン \(m\) を返す（ゲイン政策なら \(\pi(0,1)=\alpha\) なので元のゲインに戻る）。

### 証明の概略

1. `if 0 < π.action (0,1) then ⟨π.action (0,1), _⟩ else ⟨m, hm⟩` で定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourcePolicyGain_eq"></a>

## 定理 `gainSourcePolicyGain_eq`

### 式

$$\mathrm{adm}(\pi)\Rightarrow\text{gainSourcePolicyGain}=\text{choose}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容（\(\pi=\pi_\alpha\) となるゲインが存在する）なとき、取り出されるゲインは、その存在の証人（`Classical.choose`）に一致します。

### 証明の概略

1. 許容（\(\pi=\pi_\alpha\) となるゲイン \(\alpha\) が存在）から、証人 `Classical.choose` で \(\pi=\pi_{\rm choose}\)。
2. 作用を \((0,1)\) で評価すると \(\pi(0,1)=\)choose \(>0\)。
3. `gainSourcePolicyGain` の `if` の正の枝が選ばれ（`dif_pos`）、値が choose に一致（`Subtype.ext`）（18 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourcePolicyGain_of_policy"></a>

## 定理 `gainSourcePolicyGain_of_policy`

### 式

$$\text{gainSourcePolicyGain}(\pi_\alpha)=\alpha$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲイン政策から取り出したゲインは元のゲインに戻る。

### 証明の概略

1. \(\pi_\alpha(0,1)=\alpha>0\) なので `if` の正の枝になり、値が \(\alpha\)（11 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceTrajectory"></a>

## 定義 `gainSourceTrajectory`

### 式

$$\text{false}:x,\quad\text{true}:x_{\alpha(\pi)}(s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの軌道（上位はゲイン政策の軌道）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceRunningCost"></a>

## 定義 `gainSourceRunningCost`

### 式

$$\text{false}:1,\quad\text{true}:\ell_{\alpha(\pi)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの走る費用。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceOptimalValue"></a>

## 定義 `gainSourceOptimalValue`

### 式

$$\text{false}:\rho^{-1},\quad\text{true}:rm\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適値（下位は \(\int e^{-\rho s}=\rho^{-1}\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceOptimalPolicy"></a>

## 定義 `gainSourceOptimalPolicy`

### 式

$$\text{最適政策}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適政策（上位はゲイン \(m\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceIsAdmissible"></a>

## 定義 `gainSourceIsAdmissible`

### 式

$$\text{false}:\text{True},\quad\text{true}:\text{gainSourceAdmissible}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの許容性。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceLowerIntegrand_integrable"></a>

## 定理 `gainSourceLowerIntegrand_integrable`

### 式

$$\rho>0\Rightarrow e^{-\rho(s-T)}\ \text{は可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

下位層の被積分関数（割引の重み）の可積分性。

### 証明の概略

1. 指数関数の半直線上の可積分性（17 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceLowerValue_integral"></a>

## 定理 `gainSourceLowerValue_integral`

### 式

$$\rho^{-1}=\int_{[T,\infty)}e^{-\rho(s-T)}\mathrm ds$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

下位層の価値 \(\rho^{-1}\) が割引積分に等しい。

### 証明の概略

1. `Theorem24_26_LinearFamily`/`Theorem24_26_Model` の `future_exp_integral` に帰着（3 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceIntegrand_eq_gainIntegrand"></a>

## 定理 `gainSourceIntegrand_eq_gainIntegrand`

### 式

$$\text{source の被積分関数}=\text{discountedIntegrand}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般の `Theorem24NonnegativeTimeData` の被積分関数が、このファイルのゲインの被積分関数と一致すること。

### 証明の概略

1. `hπ`（\(\pi=\pi_\alpha\)）で書き換え、`gainSourcePolicyGain_of_policy` と軌道の一致を使う（11 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceData"></a>

## 定義 `gainSourceData`

### 式

$$\mathcal D=(\text{layers},\text{traj},\ell,\text{adm},V^*,\pi^*)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem24NonnegativeTimeData` の、このゲイン・モデルでのインスタンス（199 行の構成）。各フィールドの条件（可積分性・下積分の表示・最適性）は、このファイルの補題から埋めます。

### 証明の概略

1. 各フィールドを割り当て、条件を `gainSourceLowerIntegrand_integrable`・`gainSourceIntegrand_eq_gainIntegrand`・`optimalGain_*` などで証明。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceData_top_optimalValue"></a>

## 定理 `gainSourceData_top_optimalValue`

### 式

$$\mathcal D.V^*_\top=rm\,x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gainSourceData` の上位層の最適値が `optimalValue` に一致（定義どおり）。

### 証明の概略

1. `rfl`（`@[simp]`）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceData_top_optimalTrajectory"></a>

## 定理 `gainSourceData_top_optimalTrajectory`

### 式

$$\mathcal D.\mathrm{traj}_\top(\pi_m)=x_m$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の最適政策の軌道が、このファイルの最適ゲインの軌道に一致。

### 証明の概略

1. 定義と `gainSourcePolicyGain_of_policy` で書き換え（3 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceData_true_optimalTrajectory"></a>

## 定理 `gainSourceData_true_optimalTrajectory`

### 式

$$\mathcal D.\mathrm{traj}_{\text{true}}(\pi_m)=x_m$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同じことを `true` の層で述べたもの。

### 証明の概略

1. 同上（4 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceData_target_eq"></a>

## 定理 `gainSourceData_target_eq`

### 式

$$N_{\text{top}}(\mathcal D)=\{x\mid\cdots\}=\text{LinearFamily.zeroTarget}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gainSourceData` から定理26の定義で作った零価値目標が、`Theorem24_26_LinearFamily.zeroTarget` に一致する。

### 証明の概略

1. 最適値 \(rmx^2\) の零点と、`Theorem24_26_LinearFamily` の価値の零点を比べる（9 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceTopPseudoMetric"></a>

## インスタンス `gainSourceTopPseudoMetric`

### 式

$$d(x,y)=|x-y|$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の状態空間 \(\mathbb R\) の擬距離のインスタンス（ローカル）。

### 証明の概略

1. 実数の擬距離を再利用。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceTopMeasurableSpace"></a>

## インスタンス `gainSourceTopMeasurableSpace`

### 式

$$\text{Borel}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の可測空間のインスタンス。

### 証明の概略

1. 実数の Borel を再利用。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceTopBorelSpace"></a>

## インスタンス `gainSourceTopBorelSpace`

### 式

$$\text{BorelSpace}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

可測構造が Borel であることのインスタンス。

### 証明の概略

1. 実数の `BorelSpace` を再利用。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceTopProductBorelSpace"></a>

## インスタンス `gainSourceTopProductBorelSpace`

### 式

$$\text{BorelSpace}([0,\infty)\times\mathbb R)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

積空間が Borel であることのインスタンス。

### 証明の概略

1. 積の `BorelSpace` を再利用。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceNormedMetric_eq_real"></a>

## 定理 `gainSourceNormedMetric_eq_real`

### 式

$$\text{ノルム由来の擬距離}=\text{実数の擬距離}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

インスタンスが二重に出ても食い違わないことの確認です。

### 証明の概略

1. `rfl` 相当（7 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSourceDynamics"></a>

## 定義 `gainSourceDynamics`

### 式

$$\mathcal E=(W,\lambda,c_1,c_2,\text{target},\text{alive},\text{feedback})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem26NonnegativeTimeDynamics` のゲイン・モデルでのインスタンス（128 行の構成）。\(W=x^2\)、\(\lambda=2m\)、目標は零価値の集合、フィードバックは最適ゲイン \(m\)。26-A の条項は、`optimalGain_satisfies_condition26A` などから埋めます。

### 証明の概略

1. `gainSourceData` から作る零価値目標が `Theorem24_26_LinearFamily.zeroTarget` に一致（`gainSourceData_target_eq`）、それが \(\{0\}\)（`zeroTarget_eq_singleton`）。
2. \(W=x^2\)、軌道は `gainSourceData_top_optimalTrajectory` で `trajectory ⟨m,hm⟩`、右傾斜条件は `Theorem24_26_LinearFamily.WAlong_hasDerivAt` と `rightSlopeBound_of_hasDerivAt_le`（Theorem1）から。
3. 距離の同一性は `gainSourceNormedMetric_eq_real`、最適値は `gainSourceData_top_optimalValue`。各フィールドをこれらで埋める（134 行）。

----

<a id="Tomabechi.Theorem24_26_GainControl.gainSource_general_bridge"></a>

## 定義 `gainSource_general_bridge`

### 式

$$\text{下位 24 の正値・PZS 排除}\wedge\text{上位 PZS 分類}\wedge\text{指数収束}\wedge\text{零集合の同値}\wedge\text{前向き不変性}$$

### Lean のコメント（日本語訳）

> 連続な正ゲイン・モデルへの、一般のソース時間の定理の直接の適用。結果は、下位層の定理24の正値性と PZS の排除、上位層の PZS の分類、定量的な指数収束、零集合の同値、前向きの不変性を含む。

### 定義の説明

`gainSourceData`・`gainSourceDynamics` を一般定理 `theorem24_to26_from_nonnegativeTimeData` に渡して、結論一式を取り出したものです（結論が複数の命題の組なので `def`）。

### 証明の概略

1. 一般定理に `gainSourceData m ρ r hm hρ hr` と `gainSourceDynamics …` を渡す（5 行）。

----


## コメント修正記録

（なし）
