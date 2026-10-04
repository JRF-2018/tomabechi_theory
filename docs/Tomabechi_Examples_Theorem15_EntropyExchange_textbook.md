# Tomabechi/Examples/Theorem15_EntropyExchange.lean 解説

> 対象: [`Tomabechi/Examples/Theorem15_EntropyExchange.lean`](../Tomabechi/Examples/Theorem15_EntropyExchange.lean)（定理15の Python 例（有限6層のエントロピー収支）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理15（エントロピー収支）の Python 例（`examples/theorem15_entropy_exchange.py`）の (A) の Lean 根拠です。**有限 6 層**（`Fin 6`）、換算重み \(w_k=2^{-k}\)、意味エントロピー \(H_k(t)=2+\sin(0.7(k+1)t)\)、散逸 \(\Pi\) は (a) \(\Pi\equiv0\)（理想的な閉鎖・可逆系）と (b) \(\Pi(t)=\tfrac12(1+\sin t)\ge0\) の 2 通り。物理エントロピーは、A7 の交換式をそのまま積分して定義します：
$$S_{\rm phys}(z)=5+\int_0^z\Bigl(-\sum_kw_kH_k'+\Pi\Bigr).$$

一般定理 `Tomabechi.Theorem15.theorem15_finite_layer_integral_balance`（A2/A5/A6′（有限層は自明）/A7 → 積分収支）の前提をすべて証明して適用し、次を得ます。

- **(I)** \(S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\ge0\)（一般化第二法則）
- **(II)** \(\Pi\equiv0\) なら \(S_{\rm gen}\) は定数。ただし \(S_{\rm phys}\) 単独は定数でない（\(S_{\rm phys}'(0)=-21/8\)）
- **(III)** 秩序化量の上界 \(\sum w[H(a)-H(b)]\le S_{\rm phys}(b)-S_{\rm phys}(a)\)

### 0.2 このファイルが証明していないこと

- **特殊例（有限 6 層）**であり、可算無限層の一般の定理15の代替ではありません。**可算無限層での A6′(ii) の欠如**（高木型反例）は `Theorem15_A6Failure.lean` が（一部だけ）扱います。
- Python 例の位相は \(+k\) から \(0\) に変更しました（\(t=0\) での微分が有理数になり、非保存性が示せるため）。
- 物理エントロピー \(S_{\rm phys}\) は、**A7 の交換式を積分して定義**したもので、物理的に独立に与えたものではありません（A7 は原文の独立公理であり、ここでは導出していません）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理15の Python 例（`examples/theorem15_entropy_exchange.py`）の Lean 根拠
>
> 有限 6 層（`Fin 6`）、換算重み \(w_k=2^{-k}\)、意味エントロピー \(H_k(t)=2+\sin(0.7(k+1)t)\)、散逸 \(\Pi\) は (a) \(\Pi\equiv0\)（理想的な閉鎖・可逆系）、(b) \(\Pi(t)=\tfrac12(1+\sin t)\ge0\)。物理エントロピーは A7 の交換式をそのまま積分して定義：\(S_{\rm phys}(z)=5+\int_0^z(-\sum w_kH_k'+\Pi)\)。
>
> 一般定理 `Tomabechi.Theorem15.theorem15_finite_layer_integral_balance`（A2/A5/A6′（有限層は自明）/A7 → 積分収支）の前提をすべて証明して適用する。
> * (I) \(S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\ge0\)（一般化第二法則）
> * (II) \(\Pi\equiv0\) なら \(S_{\rm gen}\) は定数、ただし \(S_{\rm phys}\) 単独は定数でない（\(S_{\rm phys}'(0)=-21/8\)）
> * (III) 秩序化量の上界 \(\sum w[H(a)-H(b)]\le S_{\rm phys}(b)-S_{\rm phys}(a)\)
>
> 注意：Python 例の位相は \(+k\) から \(0\) に変更した（\(t=0\) での微分が有理数で、非保存性が示せるため）。可算無限層での A6′(ii) の欠如（高木型反例）は本ファイルの対象外（未着手、対応表に記載）。

名前空間は `Tomabechi.Examples.Theorem15`（`open MeasureTheory intervalIntegral`）。

---

<a id="Tomabechi.Examples.Theorem15.ac_of_hasDerivAt"></a>

## 定理 `ac_of_hasDerivAt`

### 式

$$f'\ \text{連続}\Rightarrow f\ \text{は任意の区間で絶対連続}$$

### Lean のコメント（日本語訳）

> 連続な導関数をもつ関数は（任意の区間で）絶対連続。

### 補題の説明

**A2（絶対連続性）の確認用補題**：\(C^1\) の関数は絶対連続です。

### 証明の概略

1. 微積分の基本定理で \(f(t)=f(a)+\int_a^tf'\)（導関数が連続なので区間可積分）。
2. 積分で書ける関数は絶対連続（`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`）。定数 \(f(a)\) は Lipschitz なので絶対連続で、その和も絶対連続。

----

<a id="Tomabechi.Examples.Theorem15.freq"></a>

## 定義 `freq`

### 式

$$\mathrm{freq}_k=0.7\,(k+1)$$

### Lean のコメント（日本語訳）

> Python の層周波数 `0.7(k+1)`。

### 定義の説明

第 \(k\) 層（\(k=0,\dots,5\)）の周波数です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.H"></a>

## 定義 `H`

### 式

$$H_k(t)=2+\sin(\mathrm{freq}_k\,t)$$

### Lean のコメント（日本語訳）

> 意味エントロピー \(H_k(t)=2+\sin(\mathrm{freq}_kt)\)。

### 定義の説明

各層の意味エントロピー。常に正（\(1\le H\le3\)）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.dH"></a>

## 定義 `dH`

### 式

$$H_k'(t)=\mathrm{freq}_k\cos(\mathrm{freq}_k\,t)$$

### Lean のコメント（日本語訳）

> \(H_k\) の時間微分 \(dH_k/dt\)。

### 定義の説明

意味エントロピーの時間微分。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.w"></a>

## 定義 `w`

### 式

$$w_k=2^{-k}$$

### Lean のコメント（日本語訳）

> 換算重み \(w_k=2^{-k}\)。

### 定義の説明

層ごとの換算重みです。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.w_pos"></a>

## 定理 `w_pos`

### 式

$$w_k>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

重みが正（A5 の一部）。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Examples.Theorem15.H_nonneg"></a>

## 定理 `H_nonneg`

### 式

$$H_k(t)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

意味エントロピーが非負（\(\sin\ge-1\)）。

### 証明の概略

1. \(2+\sin\ge1>0\)。

----

<a id="Tomabechi.Examples.Theorem15.hasDerivAt_H"></a>

## 定理 `hasDerivAt_H`

### 式

$$\frac{d}{dt}H_k=H_k'$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`dH` が `H` の導関数であること（A2：滑らか）。

### 証明の概略

1. `Real.hasDerivAt_sin` の合成と定数倍。

----

<a id="Tomabechi.Examples.Theorem15.continuous_dH"></a>

## 定理 `continuous_dH`

### 式

$$H_k'\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

導関数の連続性（`ac_of_hasDerivAt` に使う）。

### 証明の概略

1. `fun_prop`（\(\cos\) と線形写像の合成）。

----

<a id="Tomabechi.Examples.Theorem15.cogRate"></a>

## 定義 `cogRate`

### 式

$$\sum_kw_kH_k'(t)$$

### Lean のコメント（日本語訳）

> 認知側の総レート \(\sum w_kH_k'\)。

### 定義の説明

意味エントロピーの重み付き総変化率。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.continuous_cogRate"></a>

## 定理 `continuous_cogRate`

### 式

$$\mathrm{cogRate}\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

総レートの連続性（有限和）。

### 証明の概略

1. `continuous_finset_sum` と `continuous_dH`。

----

<a id="Tomabechi.Examples.Theorem15.dSphys"></a>

## 定義 `dSphys`

### 式

$$S_{\rm phys}'(t)=-\sum_kw_kH_k'(t)+\Pi(t)$$

### Lean のコメント（日本語訳）

> A7 の交換式から定まる、物理エントロピーの変化率 \(-\sum w_kH_k'+\Pi\)。

### 定義の説明

**A7（交換式）**：物理エントロピーの変化率 ＝ −（認知側の総レート）＋ 散逸 \(\Pi\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.Sphys"></a>

## 定義 `Sphys`

### 式

$$S_{\rm phys}(z)=5+\int_0^z\mathrm{dSphys}$$

### Lean のコメント（日本語訳）

> 物理エントロピーを \(S_{\rm phys}(z)=5+\int_0^z\mathrm{dSphys}\) で定める。

### 定義の説明

A7 を積分して定義した物理エントロピー（初期値 5）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.hasDerivAt_Sphys"></a>

## 定理 `hasDerivAt_Sphys`

### 式

$$\Pi\ \text{連続}\Rightarrow S_{\rm phys}'=\mathrm{dSphys}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

微積分の基本定理：`Sphys` の導関数が `dSphys` であること。

### 証明の概略

1. 被積分関数 `dSphys` が連続なので、`Continuous.integral_hasStrictDerivAt`（微積分の基本定理）で \(\int_0^z\) の導関数が `dSphys`、定数 5 を足しても同じ。

----

<a id="Tomabechi.Examples.Theorem15.Sgen"></a>

## 定義 `Sgen`

### 式

$$S_{\rm gen}(z)=S_{\rm phys}(z)+\sum_kw_kH_k(z)$$

### Lean のコメント（日本語訳）

> 一般化総エントロピー。

### 定義の説明

**一般化総エントロピー**：物理エントロピーと、意味エントロピーの重み付き和の合計。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.balance"></a>

## 定理 `balance`

### 式

$$\Pi\ \text{連続・}\ge0,\ a\le b\Rightarrow S_{\rm gen}(b)-S_{\rm gen}(a)=\int_a^b\Pi\ \wedge\ 0\le\int_a^b\Pi$$

### Lean のコメント（日本語訳）

> 定理15 (I)(III)：任意の連続な \(\Pi\ge0\) について、交換収支が成り立つ。

### 補題の説明

**積分収支**：一般化総エントロピーの増分 ＝ 散逸の積分（\(\ge0\)）。**一般定理 `theorem15_finite_layer_integral_balance` の適用**です。

### 証明の概略

1. 各 \(H_k\) が絶対連続（`ac_of_hasDerivAt`）、重みが正、有限層の A6′ は自明、A7 の交換式は `Sphys` の定義による。
2. 一般定理 `theorem15_finite_layer_integral_balance` を適用。
3. \(\Pi\ge0\) から積分が非負（`intervalIntegral.integral_nonneg`）。

----

<a id="Tomabechi.Examples.Theorem15.closed_system_conserved"></a>

## 定理 `closed_system_conserved`

### 式

$$\Pi\equiv0\Rightarrow S_{\rm gen}(b)=S_{\rm gen}(a)$$

### Lean のコメント（日本語訳）

> Python の \(\Pi\equiv0\)（理想的な閉鎖・可逆系）：\(S_{\rm gen}\) は厳密に一定。

### 補題の説明

**閉鎖系での保存**：\(\Pi\equiv0\) なら \(S_{\rm gen}\) は変わりません。

### 証明の概略

1. `balance` で \(\Pi=0\) とすると増分が \(\int0=0\)。

----

<a id="Tomabechi.Examples.Theorem15.sphys_not_conserved"></a>

## 定理 `sphys_not_conserved`

### 式

$$\neg\,\forall t,\ S_{\rm phys}(t)=S_{\rm phys}(0)\quad(\Pi\equiv0)$$

### Lean のコメント（日本語訳）

> 物理層単独は保存しない：\(\Pi\equiv0\) でも \(S_{\rm phys}'(0)=-\sum w_k\mathrm{freq}_k=-21/8\)、したがって定数でない。

### 補題の説明

**物理エントロピー単独では保存しない**：総和 \(S_{\rm gen}\) が保存されるのに、\(S_{\rm phys}\) 単独は動く（意味エントロピーとの間で交換されるため）。

### 証明の概略

1. もし定数なら \(S_{\rm phys}'(0)=0\)。
2. \(S_{\rm phys}'(0)=-\sum_kw_k\mathrm{freq}_k=-\frac{21}8\ne0\)（\(\sum_{k=0}^5 2^{-k}\cdot0.7(k+1)\) の計算）で矛盾。

----

<a id="Tomabechi.Examples.Theorem15.Pi1"></a>

## 定義 `Pi1`

### 式

$$\Pi(t)=\tfrac12(1+\sin t)$$

### Lean のコメント（日本語訳）

> Python の \(\Pi(t)=\tfrac12(1+\sin t)\ge0\)。

### 定義の説明

非負の散逸の例。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem15.Pi1_nonneg"></a>

## 定理 `Pi1_nonneg`

### 式

$$\Pi(t)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\Pi\) の非負性。

### 証明の概略

1. \(\sin\ge-1\)。

----

<a id="Tomabechi.Examples.Theorem15.Pi1_continuous"></a>

## 定理 `Pi1_continuous`

### 式

$$\Pi\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\Pi\) の連続性。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem15.Sgen_monotone"></a>

## 定理 `Sgen_monotone`

### 式

$$a\le b\Rightarrow S_{\rm gen}(a)\le S_{\rm gen}(b)$$

### Lean のコメント（日本語訳）

> 一般化第二法則 (3.7)：\(S_{\rm gen}\) は単調非減少。

### 補題の説明

**一般化第二法則**：一般化総エントロピーは減りません。

### 証明の概略

1. `balance`（`Pi1` について）で増分が \(\int\Pi\ge0\)。

----

<a id="Tomabechi.Examples.Theorem15.ordering_bound"></a>

## 定理 `ordering_bound`

### 式

$$\sum_kw_k\bigl(H_k(a)-H_k(b)\bigr)\ \le\ S_{\rm phys}(b)-S_{\rm phys}(a)$$

### Lean のコメント（日本語訳）

> 秩序化量の上界 (3.8)：\(\sum w[H(a)-H(b)]\le S_{\rm phys}(b)-S_{\rm phys}(a)\)。

### 補題の説明

**秩序化の代償**：意味エントロピーを下げる（秩序化する）には、その分だけ物理エントロピーが増える必要がある。

### 証明の概略

1. `balance`（`Pi1`）の結論 \(S_{\rm gen}(b)-S_{\rm gen}(a)=\int\Pi\ge0\) を `Sgen` で展開：\(S_{\rm phys}(a)+\sum wH(a)\le S_{\rm phys}(b)+\sum wH(b)\)。\(\sum w(H(a)-H(b))\) を分配して移項し、`linarith`。

----


## コメント修正記録

（なし）
