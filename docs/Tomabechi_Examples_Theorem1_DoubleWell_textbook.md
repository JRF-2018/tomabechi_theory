# Tomabechi/Examples/Theorem1_DoubleWell.lean 解説

> 対象: [`Tomabechi/Examples/Theorem1_DoubleWell.lean`](../Tomabechi/Examples/Theorem1_DoubleWell.lean)（定理1の Python 例（二重井戸）の Lean 根拠）。
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
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理1（TCZ への指数収束）の Python 例（`examples/theorem01_receding_horizon.py`）の Lean 根拠です。**二重井戸**
$$V_0(x)=(x^2-1)^2+0.3\,x,\qquad\theta=0,\qquad\mathrm{TCZ}=\{V_0\le0\}$$
（左の谷。\(-1\in\mathrm{TCZ}\)、\(V_0(-1)=-0.3\)）を扱います。

**Lean が検証する閉ループは 2 つで、Python の有限地平 argmin 反復そのものではありません。**

- **(A) 目標点フィードバック** \(\dot x=-(x+1)\)（目標 \(g=-1\in\mathrm{TCZ}\)）、初期点 \(x_0=-1/2\)。補題0の前提（残差 \(\Phi=[V_0]_+\) の絶対連続性、a.e. 下降 \(\Phi'\le-2c\Phi\)（\(c=2/5\)）、誤差境界 \(\mathrm{dist}^2\le C\Phi\)（\(C=1/6\)）、TCZ が非空）を証明し、定理1の一般結論
$$\mathrm{dist}(x(t),\mathrm{TCZ})\le\sqrt{C\,\Phi(0)}\;e^{-ct}$$
を得ます。（Python では (A)(C) の反復ホライズンが、結果として目標側の谷へ向かうことを数値で見るだけで、その反復の下降条件は証明していません。）
- **(B) 反例側**：局所谷の停留点 \(x_{\rm loc}\in(0.9,1)\)（\(V_0'(x_{\rm loc})=0\)、\(V_0(x_{\rm loc})>0\)）では、定数軌道が閉ループ \(\dot x=-V_0'(x)\)（零フィードバック）の解で、補題0の下降条件が破れ、TCZ への距離は正のままです。「argmin だから収束」は出ない、という原文の注意の具体例です（反復ホライズン方策が実際にこの点に留まることは証明していません）。

### 0.2 このファイルが証明していないこと

- **反復ホライズンの argmin の挙動そのもの**は未証明です（今後の課題。トップの `README.md` を参照）。Lean の閉ループは、Python の制御則とは別の、解析的な制御則です。
- (B) は「仮定（下降条件）が破れたときの挙動」であって、原文の定理1の反例ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理1の Python 例（`examples/theorem01_receding_horizon.py`）の Lean 根拠
>
> 二重井戸 \(V_0(x)=(x^2-1)^2+0.3x\)、閾値 \(\theta=0\)、\(\mathrm{TCZ}=\{V_0\le0\}\)（左の谷。\(-1\in\mathrm{TCZ}\)、\(V_0(-1)=-0.3\)）。
>
> **Lean が検証する閉ループは 2 つで、Python の有限地平 argmin 反復そのものではない：**
> * (A) 目標点フィードバック \(\dot x=-(x+1)\)（目標 \(g=-1\in\mathrm{TCZ}\)）、初期点 \(x_0=-1/2\)。補題0の前提（残差 \(\Phi=[V_0]_+\) の AC、a.e. 下降 \(\Phi'\le-2c\Phi\)（\(c=2/5\)）、誤差境界 \(\mathrm{dist}^2\le C\Phi\)（\(C=1/6\)）、TCZ が非空）を証明し、定理1の一般結論 \(\mathrm{dist}(x(t),\mathrm{TCZ})\le\sqrt{C\Phi(0)}e^{-ct}\) を得る。（Python では (A)(C) の反復ホライズンが結果として目標側の谷へ向かうことを数値で見るだけで、その反復の下降条件は証明していない。）
> * (B) 反例側：局所谷の停留点 \(x_{\rm loc}\in(0.9,1)\)（\(V_0'(x_{\rm loc})=0\)、\(V_0(x_{\rm loc})>0\)）では、定数軌道が閉ループ \(\dot x=-V_0'(x)\)（零フィードバック）の解で、補題0の下降条件が破れ、TCZ への距離は正のまま。「argmin だから収束」は出ない、という原文の注意の具体例（反復ホライズン方策が実際にこの点に留まることは証明していない）。

### 0.4 節見出しのコメント（日本語訳）

> ## (B) 反例側：局所谷の停留点

名前空間は `Tomabechi.Examples.Theorem1DoubleWell`（`open Tomabechi.Theorem1 MeasureTheory`）。

---

<a id="Tomabechi.Examples.Theorem1DoubleWell.V0"></a>

## 定義 `V0`

### 式

$$V_0(x)=(x^2-1)^2+0.3\,x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二重井戸型のポテンシャル。\(x=\pm1\) の近くに 2 つの谷があり、\(0.3x\) の項で左の谷（\(x\approx-1\)）がより深くなります。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.dV0"></a>

## 定義 `dV0`

### 式

$$V_0'(x)=4x^3-4x+0.3$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(V_0\) の導関数（勾配）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.hasDerivAt_V0"></a>

## 定理 `hasDerivAt_V0`

### 式

$$\frac{d}{dx}V_0=\mathrm{dV}_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`dV0` が実際に `V0` の導関数であること。

### 証明の概略

1. べき・和・定数倍の微分（`HasDerivAt.pow` など）で計算し、整理。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.continuous_V0"></a>

## 定理 `continuous_V0`

### 式

$$V_0\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

多項式なので連続。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.V0_neg_left"></a>

## 定理 `V0_neg_left`

### 式

$$-1\le x\le-\tfrac34\Rightarrow V_0(x)<0$$

### Lean のコメント（日本語訳）

> 目標側の谷 \([-1,-3/4]\) では \(V_0<0\)（TCZ 内）。

### 補題の説明

左の谷の底では \(V_0<0\)（TCZ の中）。

### 証明の概略

1. 多項式の不等式（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.dV0_ge"></a>

## 定理 `dV0_ge`

### 式

$$-\tfrac34\le x\le-\tfrac12\Rightarrow V_0'(x)\ge\tfrac32$$

### Lean のコメント（日本語訳）

> \([-3/4,-1/2]\) で \(V_0'\ge3/2\)。

### 補題の説明

谷の壁（右側の斜面）で、勾配が下から評価できる。

### 証明の概略

1. 区間での多項式の評価（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.V0_le_mid"></a>

## 定理 `V0_le_mid`

### 式

$$-\tfrac34\le x\le-\tfrac12\Rightarrow V_0(x)\le\tfrac{33}{80}$$

### Lean のコメント（日本語訳）

> \([-3/4,-1/2]\) で \(V_0\le33/80\)。

### 補題の説明

同じ区間での \(V_0\) の上からの評価。

### 証明の概略

1. 区間での多項式の評価（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.desc_ineq"></a>

## 定理 `desc_ineq`

### 式

$$-\tfrac34\le x\le-\tfrac12\Rightarrow\tfrac45V_0(x)\le V_0'(x)\,(x+1)$$

### Lean のコメント（日本語訳）

> 下降の核：\([-3/4,-1/2]\) で \((4/5)V_0\le V_0'\cdot(x+1)\)。

### 補題の説明

**補題0の下降条件の核**：閉ループ \(\dot x=-(x+1)\) では \(\frac{d}{dt}V_0=-V_0'\cdot(x+1)\) なので、この不等式が \(\Phi'\le-\frac45\Phi\)（\(c=2/5\)）を与えます。

### 証明の概略

1. `dV0_ge` と `V0_le_mid` を使い、区間の端点での値を比べる（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.dV0_pos"></a>

## 定理 `dV0_pos`

### 式

$$-1\le x\le-\tfrac12\Rightarrow V_0'(x)\ge\tfrac3{10}$$

### Lean のコメント（日本語訳）

> \([-1,-1/2]\) で \(V_0'\ge3/10\)（\(V_0\) は狭義増加）。

### 補題の説明

この区間で \(V_0\) は厳密に増加します（残差が時間とともに狭義に減少する根拠）。

### 証明の概略

1. 区間での多項式の評価（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.xA"></a>

## 定義 `xA`

### 式

$$x_A(t)=-1+\tfrac12e^{-t}$$

### Lean のコメント（日本語訳）

> 閉ループ \(\dot x=-(x+1)\)（目標 \(g=-1\)）の解、初期点 \(x(0)=-1/2\)。

### 定義の説明

目標点 \(-1\) へ指数的に近づく解の閉じた式です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.hasDerivAt_xA"></a>

## 定理 `hasDerivAt_xA`

### 式

$$\dot x_A=-(x_A+1)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`xA` が閉ループ ODE の解であること。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成と定数倍。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.xA_zero"></a>

## 定理 `xA_zero`

### 式

$$x_A(0)=-\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期条件。

### 証明の概略

1. \(e^0=1\) で計算。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.xA_range"></a>

## 定理 `xA_range`

### 式

$$t\ge0\Rightarrow-1<x_A(t)\le-\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

解が区間 \((-1,-1/2]\) に留まること（上の評価が使える範囲）。

### 証明の概略

1. \(0<e^{-t}\le1\)。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.TCZset"></a>

## 定義 `TCZset`

### 式

$$\mathrm{TCZ}=\{x\mid V_0(x)\le0\}$$

### Lean のコメント（日本語訳）

> \(\mathrm{TCZ}=\{V_0\le0\}\)（定理1の \(K=\mathrm{univ}\)、時刻不変）。

### 定義の説明

閾値 \(\theta=0\) の部分準位集合として TCZ を定義。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.TCZ_nonempty"></a>

## 定理 `TCZ_nonempty`

### 式

$$\mathrm{TCZ}\ne\emptyset$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

TCZ が非空（\(-1\) が属する）。

### 証明の概略

1. \(V_0(-1)=-0.3\le0\)。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.error_bound"></a>

## 定理 `error_bound`

### 式

$$x\in[-1,-\tfrac12]\Rightarrow\mathrm{dist}(x,\mathrm{TCZ})^2\le\tfrac16\,[V_0(x)]_+$$

### Lean のコメント（日本語訳）

> 誤差境界 \(\mathrm{dist}(x,\mathrm{TCZ})^2\le(1/6)[V_0x]_+\)（\(x\in[-1,-1/2]\)）。

### 補題の説明

**誤差境界**：TCZ までの距離の二乗が残差 \([V_0]_+\) で上から抑えられる（\(C=1/6\)）。

### 証明の概略

1. TCZ に入っている（\(V_0\le0\)）なら距離は 0 で自明。
2. 外（\(V_0(x)>0\)）なら \(x>-\frac34\)（`V0_neg_left`）。中間値の定理で \([-\frac34,x]\) に \(V_0(q)=0\) となる \(q\) を取る（\(q\in\mathrm{TCZ}\)）。
3. よって \(\mathrm{dist}(x,\mathrm{TCZ})\le x-q\le\frac14\)。
4. 平均値の不等式で、\([q,x]\) 上の \(V_0'\ge\frac32\)（`dV0_ge`）から \(\frac32(x-q)\le V_0(x)\)。
5. \((x-q)^2\le\frac14(x-q)\le\frac14\cdot\frac23V_0(x)=\frac16V_0(x)\)。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.contDiff_g"></a>

## 定理 `contDiff_g`

### 式

$$s\mapsto V_0(x_A(s))\ \text{は }C^1$$

### Lean のコメント（日本語訳）

> \(g(s)=V_0(x(s))\) は滑らか。

### 補題の説明

合成関数の滑らかさ。

### 証明の概略

1. `ContDiff` の合成（`fun_prop` 相当）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.residual_ac"></a>

## 定理 `residual_ac`

### 式

$$\Phi(s)=[V_0(x_A(s))]_+\ \text{は絶対連続}$$

### Lean のコメント（日本語訳）

> 残差 \(\Phi(s)=[V_0(x(s))]_+\) は絶対連続。

### 補題の説明

**補題0の前提 (AC)**：\(C^1\) の関数の正の部分は絶対連続（Lipschitz 関数との合成）。

### 証明の概略

1. `contDiff_g` で \(g\) は \(C^1\)（区間上で Lipschitz）、`max · 0` は 1-Lipschitz なので合成も絶対連続。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.g_strictAnti"></a>

## 定理 `g_strictAnti`

### 式

$$0\le a<b\Rightarrow V_0(x_A(b))<V_0(x_A(a))$$

### Lean のコメント（日本語訳）

> \(V_0\circ x\) は \(t\ge0\) で狭義減少（\(V_0\) は \([-1,-1/2]\) で狭義増加、\(x\) は減少）。

### 補題の説明

軌道に沿った \(V_0\) の値が時間とともに厳密に減る。

### 証明の概略

1. `xA_range` で軌道は区間内、`xA` は減少、`dV0_pos` で \(V_0\) は狭義増加。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.zero_set_subsingleton"></a>

## 定理 `zero_set_subsingleton`

### 式

$$\{s\ge0\mid V_0(x_A(s))=0\}\ \text{は高々1点}$$

### Lean のコメント（日本語訳）

> \(V_0(x(s))=0\) となる \(s\ge0\) は高々 1 点。

### 補題の説明

狭義単調なので零点は高々 1 つ（微分の連鎖律で「a.e.」を扱うときに、測度 0 の例外集合として使います）。

### 証明の概略

1. `g_strictAnti` から単射。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.residual_decay_ae"></a>

## 定理 `residual_decay_ae`

### 式

$$\Phi'(s)\le-2\cdot\tfrac25\,\Phi(s)\ \text{ a.e.}$$

### Lean のコメント（日本語訳）

> a.e. 下降 \(\Phi'\le-\frac45\Phi\)（すなわち \(c=2/5\)）。

### 補題の説明

**補題0の前提（a.e. 下降）**：残差が指数的に下降する。

### 証明の概略

1. \(\Phi=\max(g,0)\) で、\(g(s)=0\) となる \(s\) は高々 1 点（`zero_set_subsingleton`）で、測度 0。
2. それ以外では \(g>0\) なら \(\Phi'=g'=-V_0'(x)(x+1)\le-\frac45V_0\)（`desc_ineq`）、\(g<0\) なら \(\Phi=0\) で \(\Phi'=0\)。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.theoremA"></a>

## 定理 `theoremA`

### 式

$$t\ge0\Rightarrow\mathrm{dist}(x_A(t),\mathrm{TCZ})\le\sqrt{\tfrac16\Phi(0)}\;e^{-\frac25t}$$

### Lean のコメント（日本語訳）

> (A) 定理1の一般結論：\(\mathrm{dist}(x(t),\mathrm{TCZ})\le\sqrt{C\Phi(0)}e^{-ct}\)（\(c=2/5\)、\(C=1/6\)）。

### 補題の説明

**定理1の一般結論を、この二重井戸で取り出した**もの：TCZ への距離が \(e^{-ct}\) で指数減衰します。

### 証明の概略

1. 補題0の前提を、`residual_ac`・`residual_decay_ae`・`error_bound`・`TCZ_nonempty` で満たし、一般定理 `Tomabechi.Theorem1` の指数収束（`theorem1_…`）を適用。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.TCZ_closed"></a>

## 定理 `TCZ_closed`

### 式

$$\mathrm{TCZ}\ \text{は閉集合}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

TCZ が閉集合であること（\(V_0\) が連続なので部分準位集合は閉）。

### 証明の概略

1. `isClosed_le`（`continuous_V0` と定数）。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.exists_local_stationary"></a>

## 定理 `exists_local_stationary`

### 式

$$\exists x\in(\tfrac9{10},1),\ V_0'(x)=0$$

### Lean のコメント（日本語訳）

> \(V_0'\) は \((9/10,1)\) に零点（局所谷の停留点）をもつ。

### 補題の説明

**(B) の反例側の停留点の存在**：右の谷（局所谷）の底。

### 証明の概略

1. 中間値の定理：\(V_0'(0.9)<0\)（\(4\cdot0.729-3.6+0.3=-0.384\)）、\(V_0'(1)=0.3>0\)。\(V_0'\) は連続なので区間内に零点。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.V0_pos_at_stationary"></a>

## 定理 `V0_pos_at_stationary`

### 式

$$x\in(\tfrac9{10},1)\Rightarrow V_0(x)\ge\tfrac{27}{100}>0$$

### Lean のコメント（日本語訳）

> 停留点 \(x_{\rm loc}\in(9/10,1)\) では \(V_0(x_{\rm loc})\ge27/100>0\)（\(\theta=0\) を超える）。

### 補題の説明

局所谷の底は TCZ（\(V_0\le0\)）の外です。

### 証明の概略

1. 区間 \((0.9,1)\) で \(V_0\) の下界を `nlinarith` で評価。

----

<a id="Tomabechi.Examples.Theorem1DoubleWell.caseB"></a>

## 定理 `caseB`

### 式

$$\text{定数軌道は閉ループの解}\wedge\text{下降条件が破れる}\wedge\mathrm{dist}>0\wedge\text{距離は 0 に収束しない}$$

### Lean のコメント（日本語訳）

> (B) 停留点 \(x_{\rm loc}\) での定数軌道は閉ループ \(\dot x=-V_0'(x)\) の解（\(V_0'(x_{\rm loc})=0\)）で、補題0の下降条件 \(\Phi'\le-2c\Phi\)（\(c>0\)）が破れ、TCZ への距離は正で一定のまま（収束しない）。

### 補題の説明

**反例**：局所谷の停留点に留まる軌道は、補題0の下降条件を満たさず、TCZ に収束しません。**仮定が破れたときの挙動**で、原文の定理1の反例ではありません。

### 証明の概略

1. 定数関数の微分は 0 \(=-V_0'(x_{\rm loc})\)。
2. \(\Phi\) は定数なので \(\Phi'=0\)。\(\Phi>0\)（`V0_pos_at_stationary`）なので \(0\le-2c\Phi<0\) は偽。
3. \(x_{\rm loc}\notin\mathrm{TCZ}\)（閉集合）なので距離は正、定数なので 0 に収束しない。

----


## コメント修正記録

（なし）
