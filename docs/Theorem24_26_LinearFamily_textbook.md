# Theorem24_26_LinearFamily.lean 解説

> 対象: [`Theorem24_26_LinearFamily.lean`](../Theorem24_26_LinearFamily.lean)（定理24→26のためのスカラーモデルのパラメータ族）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem24_26_Model` の「固定した率」のスカラーモデルを、**パラメータ族**に一般化したファイルです。減衰率 \(\lambda>0\)、割引率 \(\rho>0\)、費用の係数 \(q>0\) に対し、系 \(\dot x=-\lambda x\)・走る費用 \(q x^2\) の割引価値は
$$V(x)=\frac{q}{\rho+2\lambda}\,x^2$$
です。零価値目標は \(\{0\}\)、\(W(x)=x^2\) は、条件 26-A の Lyapunov と価値・距離の条項を、減衰率 \(2\lambda\) で満たします。最後に、定理24の下位層の障害（PZS が起こらない）と、定理26の定量的な収束が、この族のすべてのメンバーで**同時に**成り立つことを示します（`theorem24_to26_bridge`）。

### 0.2 このファイルが証明していないこと

- 1 次元の線形の特殊ケースの族であり、論文の一般のモデルの構成ではありません（原文のコメント）。
- 下位層は `Theorem24_26_Model` の「定数費用の Unit モデル」をそのまま使います。
- 制御の選択はありません（政策は 1 つ）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> 定理24→26のための、スカラーモデルのパラメータ族。
>
> 正の減衰率 `lam`、割引率 `ρ`、費用の係数 `q` に対し、走る費用 \(qx^2\) を持つスカラー系 \(x'=-\lambda x\) は、割引価値 \(q/(\rho+2\lambda)\cdot x^2\) を持つ。その零価値目標は \(\{0\}\) であり、\(W(x)=x^2\) は、減衰率 \(2\lambda\) で、条件 26-A の Lyapunov と価値・距離の条項を検証する。これは、固定率の例を一般化するが、論文の一般のモデルの構成ではなく、1 次元の線形の特殊ケースにとどまる。

名前空間は `Tomabechi.Theorem24_26_LinearFamily`（`open MeasureTheory Set`、`open Tomabechi.Theorem24_26`、`open Tomabechi.Theorem24_26_Model`）。

---

<a id="Tomabechi.Theorem24_26_LinearFamily.flow"></a>

## 定義 `flow`

### 式

$$\mathrm{flow}(\lambda,x,T,s)=x\,e^{-\lambda(s-T)}$$

### Lean のコメント（日本語訳）

> \(x'=-\lambda x\) の閉ループの解で、時刻 \(T\) に \(x\) から出発するもの。

### 定義の説明

指数減衰する解の閉じた式です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.runningCost"></a>

## 定義 `runningCost`

### 式

$$\ell=q\,x^2$$

### Lean のコメント（日本語訳）

> 走る費用の尺度は、割引した無限地平の価値が、平衡点からの距離の二乗に等しくなるようにとる。

### 定義の説明

走る費用 \(qx^2\)（係数 \(q\) がパラメータ）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand"></a>

## 定義 `discountedIntegrand`

### 式

$$e^{-\rho(s-T)}\cdot q\,\mathrm{flow}^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

割引率 \(\rho\) の重みと走る費用を、流れに沿って掛けた被積分関数。

### 証明の概略

1. 定義：`theorem26DiscountWeight ρ T s * runningCost … (flow …) s`。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.value"></a>

## 定義 `value`

### 式

$$V=\int_{[T,\infty)}\text{discountedIntegrand}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

割引積分で定義された価値。

### 証明の概略

1. 定義：`futureLebesgueMeasure T` に関する積分。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_eq"></a>

## 定理 `discountedIntegrand_eq`

### 式

$$\text{integrand}=qx^2e^{-(\rho+2\lambda)(s-T)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

割引 \(e^{-\rho(s-T)}\) と流れの二乗 \(x^2e^{-2\lambda(s-T)}\) の積が、率 \(\rho+2\lambda\) の指数関数になる。

### 証明の概略

1. 定義を展開し、指数法則で整理（16 行）。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.discountedIntegrand_integrable"></a>

## 定理 `discountedIntegrand_integrable`

### 式

$$\lambda,\rho>0\Rightarrow\text{discountedIntegrand は可積分}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

率 \(\rho+2\lambda>0\) の指数関数の可積分性。

### 証明の概略

1. `discountedIntegrand_eq` で指数関数に書き換え。
2. 半直線上の \(e^{-cs}\) の可積分性に定数を掛ける。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.value_eq_formula"></a>

## 定理 `value_eq_formula`

### 式

$$V=\frac{q}{\rho+2\lambda}\,x^2$$

### Lean のコメント（日本語訳）

> 正のすべての割引率と減衰率について、厳密な割引価値の公式。

### 補題の説明

\(\int_T^\infty qx^2e^{-(\rho+2\lambda)(s-T)}ds=\dfrac{qx^2}{\rho+2\lambda}\) の計算です。

### 証明の概略

1. `discountedIntegrand_eq` で書き換え、`integral_exp_mul_Ioi` で半直線積分（27 行）。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.zeroTarget"></a>

## 定義 `zeroTarget`

### 式

$$N(T)=\{x\mid V(x,T)=0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

このパラメータ族の零価値目標の定義。

### 証明の概略

1. `theorem26ZeroValueTarget` を使う。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.zeroTarget_eq_singleton"></a>

## 定理 `zeroTarget_eq_singleton`

### 式

$$\lambda,\rho,q>0\Rightarrow N(T)=\{0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(V=\frac{q}{\rho+2\lambda}x^2\) で係数が正なので、零になるのは \(x=0\) のときだけ。

### 証明の概略

1. `value_eq_formula` で \(V\) を書き換え、\(x\ne0\) なら \(V>0\)（`nlinarith`）で矛盾を導く。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.WAlong"></a>

## 定義 `WAlong`

### 式

$$W_{\rm along}(s)=\mathrm{flow}(s)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

軌道に沿った Lyapunov 関数 \(W=x^2\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.flow_hasDerivAt"></a>

## 定理 `flow_hasDerivAt`

### 式

$$\frac{d}{ds}\mathrm{flow}=-\lambda\,\mathrm{flow}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`flow` が \(\dot x=-\lambda x\) の解であること。

### 証明の概略

1. 指数関数の微分（`HasDerivAt.exp`）と定数倍で計算（16 行）。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.WAlong_hasDerivAt"></a>

## 定理 `WAlong_hasDerivAt`

### 式

$$\frac{d}{ds}W=-2\lambda W$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\frac d{ds}x^2=2x\dot x=-2\lambda x^2\)。減衰率 \(2\lambda\)。

### 証明の概略

1. `flow_hasDerivAt` と `HasDerivAt.pow`。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.sq_flow_abs_eq"></a>

## 定理 `sq_flow_abs_eq`

### 式

$$|x|^2=x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

絶対値の二乗は二乗に等しい（`sq_abs`）。

### 証明の概略

1. `sq_abs`。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.infDist_zeroTarget_sq"></a>

## 定理 `infDist_zeroTarget_sq`

### 式

$$d(\mathrm{flow}(T),N(T))^2=x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標が \(\{0\}\) なので、初期時刻での距離の二乗は \(x^2\) です。

### 証明の概略

1. `zeroTarget_eq_singleton` と `Metric.infDist_singleton`。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.full_convergence"></a>

## 定理 `full_convergence`

### 式

$$W(s)\le W(T)e^{-2\lambda(s-T)},\ d\le\sqrt{W(T)}e^{-\lambda(s-T)},\ V\to0,\ (W=0\iff\text{target})$$

### Lean のコメント（日本語訳）

> パラメータ付きのスカラー族は、一般の定理26の収束結果に必要なすべての条項を与える：alive の不変性、非空で閉の目標、厳密な二次の距離の比較、Dini の指数散逸、(26.C)。

### 補題の説明

**定理26の結論を、パラメータ族のすべてのメンバー**（\(\lambda,\rho,q>0\)）で取り出したものです。

### 証明の概略

1. `rightSlopeBound_of_hasDerivAt_le` と `WAlong_hasDerivAt` で 26-A の右傾斜条件。
2. `value_eq_formula` と `sq_flow_abs_eq` で価値と距離の関係。
3. 一般定理 `theorem26_full_conditional_convergence_of_rightSlopeBound` を適用（60 行）。

----

<a id="Tomabechi.Theorem24_26_LinearFamily.theorem24_to26_bridge"></a>

## 定理 `theorem24_to26_bridge`

### 式

$$\neg\mathrm{PZS}_{\rm low}\ \wedge\ V_{\rm low}>0\ \wedge\ \text{(26 の収束一式)}$$

### Lean のコメント（日本語訳）

> 定理24の下位抽象の障害と、定理26の定量的な収束の主張は、この線形族のすべてのメンバーについて同時に成り立つ。これは、スカラーモデル族についての検証された橋であり、その下位層は、明示的な定数費用の Unit モデルである。

### 補題の説明

下位層では 24-A により PZS が起こらず（\(V_{\rm low}>0\)）、上位層では指数収束する、という**橋**です。

### 証明の概略

1. `lower_model_theorem24`（Model）と `theorem24_no_feedbackPZS_of_condition24A` で下位層の部分。
2. `full_convergence` で上位層の部分（8 行）。

----


## コメント修正記録

（なし）
