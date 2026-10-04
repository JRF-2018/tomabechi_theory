# Tomabechi/Examples/Theorem20_SymbolicPresence.lean 解説

> 対象: [`Tomabechi/Examples/Theorem20_SymbolicPresence.lean`](../Tomabechi/Examples/Theorem20_SymbolicPresence.lean)（定理20の Python 例（記号的現前）の Lean 根拠）。
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
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理20（記号的現前）の Python 例（`examples/theorem20_symbolic_presence.py`）の Lean 根拠です。一般の実内積空間 \(E\)（Python は \(E=\mathbb R^2\)）で、目標集合 \(Z=\bar B(u,R)\)、基礎評価 \(V_0(y)=\tfrac12\|y-v\|^2\)、\(P\equiv1\)、距離型関数
$$D(y)=\tfrac14\bigl[(\|y-u\|^2-R^2)_+\bigr]^2,\qquad s(D)=-D\ (s'=-1),$$
\(\dot x=-\nabla(V_0-\kappa qPs(D))=-\nabla(V_0+KD)\)（\(M=\mathrm{id}\)、\(\kappa=K\)、\(q=1\)）を扱います。

- **ケース A**（\(v\in Z\)、すなわち \(\|u-v\|\le R\)）：一般定理 `theorem20_full_trajectory_conclusion_of_original_conditions` の**全前提**を示します。(20.A) は \(b>0\) 任意で成立し、(20.B) は \(b+c\le K\)、PL（Polyak–Łojasiewicz）条件は \(\mu=2R^2\)、誤差境界は \(C=1/R\)。結論：\(D\) と \(\mathrm{dist}(x,Z)\) が指数減衰。
- **ケース B**（\(v\notin Z\)）：具体的な \(E=\mathbb R^2\)、\(u=(2,0)\)、\(v=0\)、\(R=\tfrac12\)、\(K=\tfrac43\) で、停留点 \(x^\ast=(1,0)\)（\(x^\ast\notin Z\)）を**厳密に**与え、同じ ODE の定常解が結論 (20.1)/(20.2) を満たさないこと、および (20.A)(20.B) を同時に満たす \(b,c>0\) が存在しないことを証明します。

### 0.2 このファイルが証明していないこと

- Python の旧 \(D\)（\(\tfrac12\mathrm{dist}^2\)）は、境界での勾配の構成が重いので、\(C^1\) で多項式の勾配をもつ**距離型関数** \(\frac14[(\|\cdot-u\|^2-R^2)_+]^2\) に置き換えました（原文は \(D=0\iff x\in Z\) の距離型関数を要求するだけ）。
- ケース B は「(20.A)(20.B) が成り立たない場合に結論が出ない」例で、原文の定理20そのものの反例ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理20の Python 例（`examples/theorem20_symbolic_presence.py`）の Lean 根拠
>
> 一般の実内積空間 \(E\)（Python は \(E=\mathbb R^2\)）で、目標集合 \(Z=\mathrm{closedBall}\,u\,R\)、基礎評価 \(V_0(y)=\frac12\|y-v\|^2\)、\(P\equiv1\)、距離型関数 \(D(y)=\frac14[(\|y-u\|^2-R^2)_+]^2\)、\(s(D)=-D\)（\(s'=-1\)）、\(\dot x=-\nabla(V_0-\kappa qPs(D))=-\nabla(V_0+KD)\)（\(M=\mathrm{id}\)、\(\kappa=K\)、\(q=1\)）。
>
> * ケース A（\(v\in Z\)、すなわち \(\|u-v\|\le R\)）：一般定理 `theorem20_full_trajectory_conclusion_of_original_conditions` の全前提を示す。(20.A) は \(b\) 任意（\(b>0\)）で成立し、(20.B) は \(b+c\le K\)、PL は \(\mu=2R^2\)、誤差境界は \(C=1/R\)。
> * ケース B（\(v\notin Z\)）：具体的な \(E=\mathbb R^2\)、\(u=(2,0)\)、\(v=0\)、\(R=\frac12\)、\(K=\frac43\) で、停留点 \(x^\ast=(1,0)\)（\(x^\ast\notin Z\)）を厳密に与え、同じ ODE の定常解が結論 (20.1)/(20.2) を満たさないこと、および (20.A)(20.B) を同時に満たす \(b,c>0\) が存在しないことを証明する。
>
> 注意：Python の旧 \(D\)（\(\frac12\mathrm{dist}^2\)）は、境界での勾配の構成が重いので、\(C^1\) で多項式の勾配をもつ距離型関数 \(\frac14[(\|\cdot-u\|^2-R^2)_+]^2\) に置き換えた（原文は \(D=0\iff x\in Z\) の距離型関数を要求するだけ）。

### 0.4 節見出しのコメント（日本語訳）

> ## ケース B（反例）：\(v\notin Z\) で \(x^\ast=(1,0)\) が停留点

名前空間は `Tomabechi.Examples.Theorem20`（`open scoped Gradient RealInnerProductSpace`、`open Tomabechi.Theorem20`、`open Filter Topology`）。ファイル内に `section General`（一般の内積空間 `E` について）と `section CaseB`（具体的な `E2`）があります。

---

<a id="Tomabechi.Examples.Theorem20.hasDerivAt_sqPos"></a>

## 定理 `hasDerivAt_sqPos`

### 式

$$\frac{d}{dt}\bigl(\max(t,0)\bigr)^2=2\max(t,0)$$

### Lean のコメント（日本語訳）

> \(t\mapsto(\max t\,0)^2\) は \(C^1\)、導関数 \(2\max t\,0\)。

### 補題の説明

正の部分の二乗は \(C^1\) です（\(t=0\) で折れ曲がらない）。距離型関数 \(D\) が \(C^1\) になる根拠です。

### 証明の概略

1. \(t<0\) では近傍で定数 0、\(t>0\) では近傍で \(t^2\) なので、それぞれ微分は 0・\(2t\)。
2. \(t=0\) では、差分が \(O(h^2)=o(h)\) であることから微分が 0（`hasDerivAt_iff_isLittleO_nhds_zero`）。

----

<a id="Tomabechi.Examples.Theorem20.hasGradientAt_halfNormSq"></a>

## 定理 `hasGradientAt_halfNormSq`

### 式

$$\nabla\bigl(\tfrac12\|y-v\|^2\bigr)=y-v$$

### Lean のコメント（日本語訳）

> \(y\mapsto\frac12\|y-v\|^2\) の勾配は \(y-v\)。

### 補題の説明

基礎評価 \(V_0\) の勾配。

### 証明の概略

1. `HasGradientAt` を `HasFDerivAt` と Riesz の表現で書き換え、\(\|\cdot\|^2\) の微分（`hasStrictFDerivAt_norm_sq` と \(y-v\) への合成）。

----

<a id="Tomabechi.Examples.Theorem20.Dfun"></a>

## 定義 `Dfun`

### 式

$$D(y)=\tfrac14\Bigl[\bigl(\|y-u\|^2-R^2\bigr)_+\Bigr]^2$$

### Lean のコメント（日本語訳）

> 距離型関数 \(D(y)=\frac14[(\|y-u\|^2-R^2)_+]^2\)（\(D=0\iff\|y-u\|\le R\)）。

### 定義の説明

目標集合（球）の外へのはみ出し量を測る**距離型関数**。球の内部と境界で 0、外で正。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.gradD"></a>

## 定義 `gradD`

### 式

$$\nabla D(y)=\bigl(\|y-u\|^2-R^2\bigr)_+\,(y-u)$$

### Lean のコメント（日本語訳）

> \(D\) の勾配 \((\|y-u\|^2-R^2)_+\cdot(y-u)\)。

### 定義の説明

`Dfun` の勾配の閉じた式（多項式）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.hasGradientAt_D"></a>

## 定理 `hasGradientAt_D`

### 式

$$\nabla D=\mathrm{gradD}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gradD` が実際に `Dfun` の勾配であること（\(D\) は \(C^1\)）。

### 証明の概略

1. `hasDerivAt_sqPos` と \(\|y-u\|^2\) の勾配 \(2(y-u)\) の連鎖律：\(\nabla D=\frac14\cdot2m_+\cdot2(y-u)=m_+(y-u)\)（\(m=\|y-u\|^2-R^2\)）。

----

<a id="Tomabechi.Examples.Theorem20.Dfun_nonneg"></a>

## 定理 `Dfun_nonneg`

### 式

$$D\ge0$$

### Lean のコメント（日本語訳）

> \(D\ge0\)、かつ \(D\,y=0\iff y\in\mathrm{closedBall}\,u\,R\)（\(R>0\)）。

### 補題の説明

\(D\) の非負性。

### 証明の概略

1. 二乗の非負性。

----

<a id="Tomabechi.Examples.Theorem20.Dfun_eq_zero_iff"></a>

## 定理 `Dfun_eq_zero_iff`

### 式

$$R>0\Rightarrow\bigl(D(y)=0\iff\|y-u\|\le R\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(D=0\) と目標集合（閉球）への所属が同値。

### 証明の概略

1. \(D=0\iff(\|y-u\|^2-R^2)_+=0\iff\|y-u\|^2\le R^2\iff\|y-u\|\le R\)（\(R>0\)）。

----

<a id="Tomabechi.Examples.Theorem20.gradD_inner_self"></a>

## 定理 `gradD_inner_self`

### 式

$$\|\nabla D\|^2=4\,D\,\|y-u\|^2$$

### Lean のコメント（日本語訳）

> \(\|\nabla D\|^2=4D\|y-u\|^2\)、ゆえに目標外（\(\|y-u\|\ge R\)）で PL：\(4R^2D\le\|\nabla D\|^2\)。

### 補題の説明

**PL（Polyak–Łojasiewicz）条件の核**：勾配の二乗が \(D\) に比例して下から評価できる。

### 証明の概略

1. \(\|\nabla D\|^2=m_+^2\|y-u\|^2\)、\(D=\frac14m_+^2\)（`gradD` の定義から）。

----

<a id="Tomabechi.Examples.Theorem20.PL_bound"></a>

## 定理 `PL_bound`

### 式

$$R>0\Rightarrow 2\,(2R^2)\,D(y)\le\|\nabla D(y)\|^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**PL 条件**（\(\mu=2R^2\)）：\(2\mu D\le\|\nabla D\|^2\)。

### 証明の概略

1. `gradD_inner_self` で \(\|\nabla D\|^2=4D\|y-u\|^2\)。
2. 目標外では \(\|y-u\|\ge R\)、目標内では \(D=0\)。どちらでも \(4R^2D\le4D\|y-u\|^2\)。

----

<a id="Tomabechi.Examples.Theorem20.error_bound"></a>

## 定理 `error_bound`

### 式

$$R>0\Rightarrow\mathrm{dist}(y,Z)\le\frac1R\sqrt{D(y)}$$

### Lean のコメント（日本語訳）

> 誤差境界：\(\mathrm{infDist}\,y\,Z\le(1/R)\sqrt D\)。

### 補題の説明

**誤差境界**（\(C=1/R\)）：目標集合までの距離が \(\sqrt D\) で抑えられる。

### 証明の概略

1. 目標内（\(\|y-u\|\le R\)）なら距離は 0 で自明。
2. 目標外（\(r=\|y-u\|>R\)）では、中心 \(u\) 方向へ射影した点 \(u+\frac Rr(y-u)\)（球の上）までの距離が \(r-R\)。したがって \(\mathrm{dist}\le r-R\)。
3. \(\sqrt D=\frac{r^2-R^2}2\)（`Dfun` の定義）で、\(\frac1R\sqrt D=\frac{(r-R)(r+R)}{2R}\ge r-R\)（\(r+R\ge2R\)）。

----

<a id="Tomabechi.Examples.Theorem20.hasGradientAt_effective"></a>

## 定理 `hasGradientAt_effective`

### 式

$$\nabla\bigl(V_0+KD\bigr)(y)=(y-v)+K\,\nabla D(y)$$

### Lean のコメント（日本語訳）

> 実効ポテンシャル \(V_0+KD\) の勾配は \((y-v)+K\cdot\nabla D\)。

### 補題の説明

閉ループ \(\dot x=-\nabla(V_0+KD)\) の右辺。

### 証明の概略

1. `hasGradientAt_halfNormSq` と `hasGradientAt_D` の線形結合。

----

<a id="Tomabechi.Examples.Theorem20.caseA"></a>

## 定理 `caseA`

### 式

$$v\in Z,\ b,c>0,\ b+c\le K\Rightarrow D(x(t))\le D(x(t_0))\,e^{-2(2R^2)c(t-t_0)}\ \wedge\ \mathrm{dist}\le\tfrac1R\sqrt{D(x(t_0))}\,e^{-2R^2c(t-t_0)}\ \wedge\ \mathrm{dist}\to0$$

### Lean のコメント（日本語訳）

> ケース A の一般結論：閉ループ \(\dot x=-\nabla(V_0+KD)\)（\(P\equiv1\)、\(s(D)=-D\)、\(\kappa q=K\)）の任意の解について、\(v\in Z\)（\(\|u-v\|\le R\)）、\(b+c\le K\)、\(b,c>0\) のもとで、\(D\) と \(\mathrm{dist}(x,Z)\) が指数減衰する。一般定理 `theorem20_full_trajectory_conclusion_of_original_conditions` の全前提を示して得る。

### 補題の説明

**定理20の一般結論を、この具体的な \(V_0,D\) で取り出した**もの。(20.A)（\(b>0\) 任意）、(20.B)（\(b+c\le K\)）、PL、誤差境界、\(D\) の \(C^1\) 勾配をすべて確認して一般定理を適用します。

### 証明の概略

1. `hasGradientAt_halfNormSq`・`hasGradientAt_D` で勾配の構成（\(P\equiv1\)、\(s(D)=-D\)）、`PL_bound`・`error_bound` で PL と誤差境界、`Dfun_eq_zero_iff` で \(D=0\iff x\in Z\)。
2. (20.A)：目標外では \(\langle x-u,x-v\rangle\ge0\)（\(v\in Z\) なので、Cauchy–Schwarz で \(\|x-u\|^2-\|x-u\|\|u-v\|\ge0\)）。これと \(\nabla D=(\|x-u\|^2-R^2)(x-u)\) から \(-\langle\nabla D,x-v\rangle\le b\|\nabla D\|^2\) が \(b>0\) 任意で成立。
3. (20.B)：\(b+c\le K\) は仮定。
4. `theorem20_full_trajectory_conclusion_of_original_conditions`（Core 側）を適用。

----

<a id="Tomabechi.Examples.Theorem20.E2"></a>

## 定義 `E2`

### 式

$$E_2=\mathbb R^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 次元ユークリッド空間（ケース B の具体的な空間）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.vec"></a>

## 定義 `vec`

### 式

$$\mathrm{vec}(a,b)=(a,b)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

成分から \(E_2\) の元を作る記法。

### 証明の概略

1. 定義のみ（`!₂[a, b]`）。

----

<a id="Tomabechi.Examples.Theorem20.inner_vec"></a>

## 定理 `inner_vec`

### 式

$$\langle(a,b),(c,d)\rangle=ac+bd$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

内積の成分表示。

### 証明の概略

1. `EuclideanSpace` の内積の展開（`Fin.sum_univ_two`）。

----

<a id="Tomabechi.Examples.Theorem20.normSq_vec"></a>

## 定理 `normSq_vec`

### 式

$$\|(a,b)\|^2=a^2+b^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ノルムの二乗の成分表示。

### 証明の概略

1. `inner_vec` で自分自身との内積。

----

<a id="Tomabechi.Examples.Theorem20.vec_sub"></a>

## 定理 `vec_sub`

### 式

$$(a,b)-(c,d)=(a-c,b-d)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

差の成分表示。

### 証明の概略

1. `ext` と座標の計算。

----

<a id="Tomabechi.Examples.Theorem20.vec_smul"></a>

## 定理 `vec_smul`

### 式

$$k\,(a,b)=(ka,kb)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

スカラー倍の成分表示。

### 証明の概略

1. `ext` と座標の計算。

----

<a id="Tomabechi.Examples.Theorem20.uB"></a>

## 定義 `uB`

### 式

$$u_B=(2,0)$$

### Lean のコメント（日本語訳）

> Python のケース B：\(u=(2,0)\)、\(v=0\)、\(R=\frac12\)、\(K=\frac43\)。

### 定義の説明

ケース B の目標球の中心。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.vB"></a>

## 定義 `vB`

### 式

$$v_B=(0,0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B の基礎評価の最小点 \(v=0\)（目標球の外にある）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.xstar"></a>

## 定義 `xstar`

### 式

$$x^\ast=(1,0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B の停留点 \(x^\ast=(1,0)\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.RB"></a>

## 定義 `RB`

### 式

$$R_B=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B の目標球の半径。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.KB"></a>

## 定義 `KB`

### 式

$$K_B=\tfrac43$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B の係数 \(K\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.xstar_not_in_Z"></a>

## 定理 `xstar_not_in_Z`

### 式

$$x^\ast\notin\bar B(u_B,R_B)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\|x^\ast-u_B\|=1>\frac12=R_B\) なので、停留点は目標球の外です。

### 証明の概略

1. `normSq_vec` で \(\|(1,0)-(2,0)\|^2=1>\frac14\)。

----

<a id="Tomabechi.Examples.Theorem20.D_xstar"></a>

## 定理 `D_xstar`

### 式

$$D(x^\ast)=\tfrac9{64}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(D(x^\ast)=\frac14\bigl(1-\frac14\bigr)^2=\frac14\cdot\frac9{16}=\frac9{64}\)。

### 証明の概略

1. 定義を展開して数値計算（`norm_num`）。

----

<a id="Tomabechi.Examples.Theorem20.gradD_xstar"></a>

## 定理 `gradD_xstar`

### 式

$$\nabla D(x^\ast)=\bigl(-\tfrac34,0\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\nabla D(x^\ast)=\frac34\cdot(x^\ast-u_B)=\frac34\cdot(-1,0)=(-\frac34,0)\)。

### 証明の概略

1. 定義を展開し、`vec_sub`・`vec_smul` で成分計算。

----

<a id="Tomabechi.Examples.Theorem20.effective_gradient_xstar"></a>

## 定理 `effective_gradient_xstar`

### 式

$$(x^\ast-v_B)+K_B\,\nabla D(x^\ast)=0$$

### Lean のコメント（日本語訳）

> 停留点：\(\nabla(V_0+KD)(x^\ast)=(x^\ast-v)+K\nabla D(x^\ast)=(1,0)+\frac43\bigl(-\frac34,0\bigr)=0\)。

### 補題の説明

**停留点の厳密な確認**：実効ポテンシャルの勾配が 0 になる。

### 証明の概略

1. `vec` の成分計算：\(1+\frac43\cdot(-\frac34)=0\)。

----

<a id="Tomabechi.Examples.Theorem20.caseB_constant_solution"></a>

## 定理 `caseB_constant_solution`

### 式

$$\text{定数軌道は閉ループ ODE の解}\wedge x^\ast\notin Z\wedge\dot D=0\wedge\mathrm{dist}>0\wedge\text{距離は 0 に収束しない}$$

### Lean のコメント（日本語訳）

> 反例 (B)：定数軌道 \(x(t)\equiv x^\ast\) は同じ閉ループ ODE の解で、\(x^\ast\notin Z\)、\(\mathrm{dist}(x^\ast,Z)>0\) が一定。したがって、(20.1) の厳密下降 \(x\notin Z\Rightarrow\dot D<0\) も、(20.2) の距離収束も成り立たない。

### 補題の説明

**反例**：停留点に留まる定数軌道は、定理20の結論（目標への収束・厳密な下降）を満たしません。**仮定 (20.A)(20.B) が成り立たない場合の挙動**です。

### 証明の概略

1. `effective_gradient_xstar` で勾配が 0 なので、定数関数（導関数 0）が ODE の解。
2. `xstar_not_in_Z` で目標の外、\(\dot D=0\)（定数）。
3. 距離は定数で正、よって 0 に収束しない。

----

<a id="Tomabechi.Examples.Theorem20.caseB_no_valid_constants"></a>

## 定理 `caseB_no_valid_constants`

### 式

$$(20.A)\ \text{を満たす}\ b,c>0\ \Rightarrow\ b+c>K_B$$

### Lean のコメント（日本語訳）

> (20.A)(20.B) を同時に満たす \(b,c>0\) は存在しない（\(x^\ast\) で (20.A) は \(b\ge4/3\)、(20.B) は \(b+c\le4/3\)）。

### 補題の説明

**ケース B では (20.A) と (20.B) を同時に満たす定数がない**ことの確認：(20.A) は \(b\ge\frac43\) を要求し、(20.B) は \(b+c\le\frac43\)（\(c>0\)）を要求するので矛盾します。

### 証明の概略

1. `gradD_xstar` と `xstar - vB = (1,0)` から、(20.A) の左辺 \(-\langle\nabla D,x^\ast-v\rangle=\frac34\)、右辺 \(b\|\nabla D\|^2=\frac9{16}b\)。
2. よって \(b\ge\frac43\)。\(c>0\) と合わせて \(b+c>\frac43=K_B\)。

----

<a id="Tomabechi.Examples.Theorem20.uA"></a>

## 定義 `uA`

### 式

$$u_A=(2,0)$$

### Lean のコメント（日本語訳）

> Python のケース A：\(u=(2,0)\)、\(v=0\)、\(R=5/2\)、\(K=4/3\)（一般定理の定数は \(b=1/3\)、\(c=1\)）。

### 定義の説明

ケース A の目標球の中心（半径は \(5/2\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem20.caseA_python_instance"></a>

## 定理 `caseA_python_instance`

### 式

$$u=(2,0),\ v=0,\ R=\tfrac52,\ K=\tfrac43\text{ で }\texttt{caseA}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**Python のケース A のパラメータでの `caseA` の具体化**：\(\|u-v\|=2\le\frac52=R\)、\(b=\frac13\)、\(c=1\)（\(b+c=\frac43=K\)）。

### 証明の概略

1. `caseA` に \(R=\frac52\)、\(K=\frac43\)、\(b=\frac13\)、\(c=1\) を渡し、\(\|u_A-v_B\|=2\le\frac52\) を `normSq_vec` で確認。

----


## コメント修正記録

（なし）
