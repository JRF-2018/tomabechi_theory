# Tomabechi/Examples/Theorem3_LubConsensus.lean 解説

> 対象: [`Tomabechi/Examples/Theorem3_LubConsensus.lean`](../Tomabechi/Examples/Theorem3_LubConsensus.lean)（定理3の Python 例（LUB 合意）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理3（LUB 合意）の Python 例（`examples/theorem03_lub_consensus.py`）の Lean 根拠で、**連続時間では証明済み**です。3 主体 \(i\in\mathrm{Fin}\,3\)、各主体の状態 \(x_i\in\mathbb R^3\)、概念束 \(\mathbb L=\mathrm{Fin}\,3\to[0,1]\)（ファジー集合、各点順序）、順序埋め込み \(\iota=\)座標の実数値、\(\varphi_i(x)=\mathrm{clamp}(x)\)、世界 \(W_i=e_i\)（\(i\) 番目の概念だけ 1）。\(L^\ast=\bigvee W_i=\top=(1,1,1)\)（**平均 \((\tfrac13,\tfrac13,\tfrac13)\) ではない**）。
$$\Phi_3=\gamma\sum_{i<j}S_{ij}+\eta\sum_iA_i,\quad A_i=\|\iota(\varphi_i(x_i))-\iota(L^\ast)\|^2,\quad S_{ij}=\|x_i-x_j\|^2.$$
勾配流 \(\dot x_i=-2\nabla_{x_i}\Phi_3\)（Python の `x ← x-dt·2·g`）、初期値 \(x_i(0)=e_i\)。

- **厳密解** \(x_{ik}(t)=1+y_{ik}(t)\)、\(y_{ik}=-\tfrac23a(t)+(\delta_{ik}-\tfrac13)b(t)\)、\(a=e^{-4\eta t}\)、\(b=e^{-4(\eta+3\gamma)t}\) を求め、**勾配流であること**、\([0,1]\) に留まることを証明。
- \(\Phi_3(t)=4\eta a^2+2(\eta+3\gamma)b^2\)（閉形式）、したがって \(\Phi_3'\le-8\eta\Phi_3\)（\(c=4\eta\)）。
- 一般定理 `AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent` の**全前提**を満たし、共有零集合への距離と \(\|\iota(\varphi_i(x_i))-\iota(L^\ast)\|\) が 0 に収束。誤差境界は \(C=1/\eta\)。

### 0.2 このファイルが証明していないこと

- 束の型 \(\mathrm{Fin}\,3\to[0,1]\) は**ファジー集合**（Python の連続状態に合わせた）で、2 値の集合束 \(\mathrm{Finset}(\mathrm{Fin}\,3)\) ではありません。\(\iota(\varphi_i(x))\) は \([0,1]\) への射影（clamp）を介します。
- **Python の Euler 離散化と厳密解の一致は未検証**です（連続時間の厳密解だけを証明）。
- 特殊例（3 主体、対称な初期値）であり、一般の定理3の代替ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理3の Python 例（`examples/theorem03_lub_consensus.py`）の Lean 根拠
>
> 3 主体 \(i\in\mathrm{Fin}\,3\)、各主体の状態 \(x_i\in\mathbb R^3\)、概念束 \(\mathbb L=\mathrm{Fin}\,3\to[0,1]\)（ファジー集合、各点順序）、順序埋め込み \(\iota=\)座標の実数値、\(\varphi_i(x)=\mathrm{clamp}(x)\)、世界 \(W_i=e_i\)（\(i\) 番目の概念だけ 1）。\(L^\ast=\bigvee W_i=\top=(1,1,1)\)（平均 \((\frac13,\frac13,\frac13)\) ではない）。\(\Phi_3=\gamma\sum_{i<j}S_{ij}+\eta\sum A_i\)、\(A_i=\|\iota(\varphi_i(x_i))-\iota(L^\ast)\|^2\)、\(S_{ij}=\|x_i-x_j\|^2\)。勾配流 \(\dot x_i=-2\nabla_{x_i}\Phi_3\)（Python の `x ← x-dt·2·g`）、初期値 \(x_i(0)=e_i\)。
>
> * 厳密解 \(x_{ik}(t)=1+y_{ik}(t)\)、\(y_{ik}=-(2/3)a(t)+(\delta_{ik}-1/3)b(t)\)、\(a=e^{-4\eta t}\)、\(b=e^{-4(\eta+3\gamma)t}\) を求め、勾配流であること、\([0,1]\) に留まることを証明する。
> * \(\Phi_3(t)=4\eta a^2+2(\eta+3\gamma)b^2\)（閉形式）、したがって \(\Phi_3'\le-8\eta\Phi_3\)（\(c=4\eta\)）。
> * 一般定理 `AbstractSharedSystem.theorem3_two_distances_tendsto_of_ac_ae_descent` の全前提を満たし、共有零集合への距離と \(\|\iota(\varphi_i(x_i))-\iota(L^\ast)\|\) が 0 に収束する。誤差境界は \(C=1/\eta\)。
>
> 注意：束の型 \(\mathrm{Fin}\,3\to[0,1]\) はファジー集合（Python の連続状態に合わせた）で、2 値集合束 `Finset (Fin 3)` ではない。\(\iota(\varphi_i(x))\) は \([0,1]\) への射影（clamp）を介する。

### 0.4 節見出しのコメント（日本語訳）

> ## 厳密解と勾配流
>
> ## 総残差 \(\Phi_3\) の閉形式
>
> ## 一般定理 3 の前提

名前空間は `Tomabechi.Examples.Theorem3`（`open Tomabechi.Theorem3`）。ファイル内に `section Solution`（厳密解、パラメータ \(\eta,\gamma\) を変数として使う）と `section Main`（主結果）があり、各補題の署名にある `η γ` はその節の変数です。

---

<a id="Tomabechi.Examples.Theorem3.Concept"></a>

## 定義 `Concept`

### 式

$$\mathbb L=\mathrm{Fin}\,3\to[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

概念束：3 つの概念それぞれに \([0,1]\) の度合いを与える**ファジー集合**。各点ごとの順序で束をなす。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.iota"></a>

## 定義 `iota`

### 式

$$\iota:\mathbb L\hookrightarrow\mathbb R^3,\ \ \iota(f)=(f(0),f(1),f(2))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

順序埋め込み：概念を実数ベクトルに写す（座標の実数値）。

### 証明の概略

1. `OrderEmbedding` の構成（単射性と順序の保存は座標ごとの比較）。

----

<a id="Tomabechi.Examples.Theorem3.world"></a>

## 定義 `world`

### 式

$$W_i=e_i\quad(W_i(k)=1\ (k=i),\ 0\ (k\ne i))$$

### Lean のコメント（日本語訳）

> 世界 \(W_i=e_i\)。

### 定義の説明

主体 \(i\) の世界：\(i\) 番目の概念だけが 1。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.Dsys"></a>

## 定義 `Dsys`

### 式

$$\mathcal D=\text{（3 主体の抽象的な共有系：状態}\ \mathbb R^3,\ \text{表象 clamp},\ \text{世界 }W_i)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

3 主体の**抽象共有系** `AbstractSharedSystem`：状態は \(\mathbb R^3\)、抽象化は \([0,1]\) への射影（clamp）、世界は `world`、埋め込みは `iota`。

### 証明の概略

1. `AbstractSharedSystem` のフィールドを具体的に与える。

----

<a id="Tomabechi.Examples.Theorem3.iota_apply"></a>

## 定理 `iota_apply`

### 式

$$\iota(f)_k=f(k)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みの座標が、ファジー集合の値そのもの。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Examples.Theorem3.Dsys_abstraction"></a>

## 定理 `Dsys_abstraction`

### 式

$$\mathrm{abstraction}_i(x)_k=\mathrm{clamp}_{[0,1]}(x_k)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

抽象化が各座標の clamp であること。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Examples.Theorem3.lub_apply"></a>

## 定理 `lub_apply`

### 式

$$L^\ast(k)=1$$

### Lean のコメント（日本語訳）

> \(L^\ast=\bigvee W_i=\top=(1,1,1)\)（平均ではない）。

### 補題の説明

**LUB（最小上界）は全概念が 1 の \(\top\)**。世界 \(W_0,W_1,W_2\) を和（各点の最大値）にするので、平均 \((\frac13,\frac13,\frac13)\) にはなりません（**LUB は平均ではない**）。

### 証明の概略

1. 各 \(k\) で \(\sup_iW_i(k)=W_k(k)=1\)。

----

<a id="Tomabechi.Examples.Theorem3.iota_lub"></a>

## 定理 `iota_lub`

### 式

$$\iota(L^\ast)_k=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

LUB の埋め込みが \((1,1,1)\)。

### 証明の概略

1. `iota_apply` と `lub_apply`。

----

<a id="Tomabechi.Examples.Theorem3.abstractResidual_eq"></a>

## 定理 `abstractResidual_eq`

### 式

$$A_i(x)=\sum_k\bigl(\mathrm{clamp}(x_k)-1\bigr)^2$$

### Lean のコメント（日本語訳）

> 抽象化の残差は \(A_i(x)=\sum_k(\mathrm{clamp}(x_k)-1)^2\)。

### 補題の説明

抽象化の残差（LUB \((1,1,1)\) との距離の二乗）の具体形。

### 証明の概略

1. 定義の展開と `iota_lub`。

----

<a id="Tomabechi.Examples.Theorem3.aF"></a>

## 定義 `aF`

### 式

$$a(t)=e^{-4\eta t}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

厳密解の「平均方向」の減衰因子。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.bF"></a>

## 定義 `bF`

### 式

$$b(t)=e^{-4(\eta+3\gamma)t}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

厳密解の「差の方向」の減衰因子（結合 \(\gamma\) のぶん速い）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.coef"></a>

## 定義 `coef`

### 式

$$\delta_{ik}-\tfrac13=\begin{cases}2/3&(i=k)\\-1/3&(i\ne k)\end{cases}$$

### Lean のコメント（日本語訳）

> 係数 \(\delta_{ik}-1/3\)。

### 定義の説明

主体 \(i\) の概念 \(k\) の、平均からのずれの係数。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.xt"></a>

## 定義 `xt`

### 式

$$x_{ik}(t)=1-\tfrac23a(t)+(\delta_{ik}-\tfrac13)\,b(t)$$

### Lean のコメント（日本語訳）

> 厳密解 \(x_{ik}(t)=1-(2/3)a+(\delta_{ik}-1/3)b\)（初期値 \(x_i(0)=e_i\)）。

### 定義の説明

勾配流の**閉じた形の解**。\(t\to\infty\) で \(x_{ik}\to1\)（LUB に収束）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.xt_zero"></a>

## 定理 `xt_zero`

### 式

$$x_{ik}(0)=\begin{cases}1&(k=i)\\0&(k\ne i)\end{cases}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**初期条件** \(x_i(0)=e_i\) を満たす（\(1-\frac23+\frac23=1\)、\(1-\frac23-\frac13=0\)）。

### 証明の概略

1. `coef` の場合分けで計算。

----

<a id="Tomabechi.Examples.Theorem3.coef_sum"></a>

## 定理 `coef_sum`

### 式

$$\sum_j(\delta_{jk}-\tfrac13)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

係数の和が 0（主体について足すと平均方向が消える）。

### 証明の概略

1. \(\frac23-\frac13-\frac13=0\)。

----

<a id="Tomabechi.Examples.Theorem3.hasDerivAt_aF"></a>

## 定理 `hasDerivAt_aF`

### 式

$$a'=-4\eta\,a$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`aF` の微分。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成。

----

<a id="Tomabechi.Examples.Theorem3.hasDerivAt_bF"></a>

## 定理 `hasDerivAt_bF`

### 式

$$b'=-4(\eta+3\gamma)\,b$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`bF` の微分。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成。

----

<a id="Tomabechi.Examples.Theorem3.xt_gradient_flow"></a>

## 定理 `xt_gradient_flow`

### 式

$$\dot x_{ik}=-2\Bigl(2\eta(x_{ik}-1)+2\gamma\sum_j(x_{ik}-x_{jk})\Bigr)$$

### Lean のコメント（日本語訳）

> 勾配流：\(\dot x_{ik}=-2(2\eta(x_{ik}-1)+2\gamma\sum_j(x_{ik}-x_{jk}))\)（Python の `x←x-dt·2·g`）。

### 補題の説明

**厳密解が勾配流の方程式を満たす**：右辺の第 1 項が LUB への引力（\(\eta\)）、第 2 項が主体間の結合（\(\gamma\)）。

### 証明の概略

1. `hasDerivAt_aF`・`hasDerivAt_bF` から \(\dot x_{ik}=\frac83\eta a-(\delta_{ik}-\frac13)4(\eta+3\gamma)b\)。
2. 右辺を `coef_sum` を使って展開（\(\sum_j(x_{ik}-x_{jk})=3x_{ik}-\sum_jx_{jk}\)、\(\sum_jx_{jk}=3-2a\)）して一致を確認（`ring`）。

----

<a id="Tomabechi.Examples.Theorem3.xt_mem"></a>

## 定理 `xt_mem`

### 式

$$\eta,\gamma>0,\ t\ge0\Rightarrow0\le x_{ik}(t)\le1$$

### Lean のコメント（日本語訳）

> \(t\ge0\) で \(x_{ik}\in[0,1]\)（\(\eta,\gamma>0\)）。

### 補題の説明

**clamp が効かない**：解は \([0,1]^3\) に留まるので、clamp を使った抽象化 \(\varphi_i\) は恒等になります。

### 証明の概略

1. \(a,b\in(0,1]\)（\(t\ge0\)）、\(b\le a\)（\(\eta+3\gamma>\eta\)）。
2. \(x_{ik}=1-\frac23a+(\delta_{ik}-\frac13)b\) を、\(i=k\) と \(i\ne k\) で評価（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem3.sharedAtF"></a>

## 定義 `sharedAtF`

### 式

$$\Phi_{\rm sh}(x)=\frac\gamma2\sum_{i,j}\|x_i-x_j\|^2\quad(=\gamma\sum_{i<j}S_{ij})$$

### Lean のコメント（日本語訳）

> 共有残差 \(\Phi_2=\gamma\sum_{i<j}S_{ij}=\frac\gamma2\sum_{i,j}\|x_i-x_j\|^2\)（時間不変）。

### 定義の説明

主体間の不整合の総量（結合の項）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.traj"></a>

## 定義 `traj`

### 式

$$x_i(t)=(x_{ik}(t))_k$$

### Lean のコメント（日本語訳）

> 軌道 \(x_i(t)\)。

### 定義の説明

厳密解を、主体 \(i\) の状態ベクトルの軌道として束ねたもの。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.sharedT"></a>

## 定義 `sharedT`

### 式

$$\Phi_{\rm sh}(x(t))$$

### Lean のコメント（日本語訳）

> 共有残差の軌道上の値。

### 定義の説明

軌道に沿った共有残差。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.PhiF"></a>

## 定義 `PhiF`

### 式

$$\Phi_F(t)=4\eta\,a^2+2(\eta+3\gamma)\,b^2$$

### Lean のコメント（日本語訳）

> 閉形式 \(\Phi_3(t)=4\eta a^2+2(\eta+3\gamma)b^2\)。

### 定義の説明

総残差の**閉じた形**。\(a^2\) の項が LUB への収束、\(b^2\) の項が主体間の合意に対応。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.potential_eq"></a>

## 定理 `potential_eq`

### 式

$$\eta,\gamma>0,\ t\ge0\Rightarrow\Phi_3(x(t))=\Phi_F(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**総残差が閉形式に一致**：`Dsys.potential` を軌道に沿って評価した値が `PhiF`。

### 証明の概略

1. 共有残差 \(\frac\gamma2\sum_{i,j}\|x_i-x_j\|^2\) と抽象化の残差 \(\eta\sum_iA_i\) を、厳密解（`xt`）と `xt_mem`（clamp が恒等）で具体的に計算。
2. \(\sum_iA_i=\sum_{i,k}\bigl(-\frac23a+(\delta_{ik}-\frac13)b\bigr)^2\)、共有項は \(b^2\) の定数倍。展開して `PhiF` に一致（`ring`）。

----

<a id="Tomabechi.Examples.Theorem3.TCZ"></a>

## 定義 `TCZ`

### 式

$$\mathrm{TCZ}(s)=\{x\mid\Phi_3(x)=0\}$$

### Lean のコメント（日本語訳）

> 共有 TCZ（\(\Phi_3=0\) の零集合、時間不変）。

### 定義の説明

**共有 TCZ**：全主体が合意し（\(x_i\) がすべて同じ）、かつ LUB（\(x_{ik}\ge1\)）にある状態の集合。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem3.Lcfg_mem"></a>

## 定理 `Lcfg_mem`

### 式

$$x_{ik}\equiv1\in\mathrm{TCZ}$$

### Lean のコメント（日本語訳）

> LUB 配置 \(x_{ik}\equiv1\) は TCZ に属す（非空性）。

### 補題の説明

LUB の配置自体が TCZ に入る（TCZ が非空）。

### 証明の概略

1. \(\Phi_3(x)=0\)：不整合 0、抽象化の残差 \((1-1)^2=0\)。

----

<a id="Tomabechi.Examples.Theorem3.sharedT_nonneg"></a>

## 定理 `sharedT_nonneg`

### 式

$$\gamma>0\Rightarrow\Phi_{\rm sh}(x(t))\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差の非負性。

### 証明の概略

1. 二乗和の非負性。

----

<a id="Tomabechi.Examples.Theorem3.hasDerivAt_PhiF"></a>

## 定理 `hasDerivAt_PhiF`

### 式

$$\Phi_F'(t)=-32\eta^2a^2-16(\eta+3\gamma)^2b^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉形式の微分。

### 証明の概略

1. `hasDerivAt_aF`・`hasDerivAt_bF` と積の微分。

----

<a id="Tomabechi.Examples.Theorem3.contDiff_PhiF"></a>

## 定理 `contDiff_PhiF`

### 式

$$\Phi_F\ \text{は }C^1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`PhiF` が \(C^1\)（絶対連続の前提）。

### 証明の概略

1. `fun_prop`（指数関数の合成）。

----

<a id="Tomabechi.Examples.Theorem3.PhiF_decay"></a>

## 定理 `PhiF_decay`

### 式

$$\Phi_F'(t)\le-2(4\eta)\,\Phi_F(t)$$

### Lean のコメント（日本語訳）

> 総残差の下降 \(\Phi_3'\le-8\eta\Phi_3\)（\(c=4\eta\)）。

### 補題の説明

**補題0の下降条件**：\(\Phi_F'=-8\eta\cdot4\eta a^2-16(\eta+3\gamma)^2b^2\)、\(-8\eta\Phi_F=-32\eta^2a^2-16\eta(\eta+3\gamma)b^2\)。差は \(-16(\eta+3\gamma)\cdot3\gamma\,b^2\le0\)。

### 証明の概略

1. `hasDerivAt_PhiF` の式と \(-8\eta\Phi_F\) を比べる。差が \(\le0\)（\(\gamma>0\)、\(b^2\ge0\)）なので `nlinarith`。

----

<a id="Tomabechi.Examples.Theorem3.error_bound"></a>

## 定理 `error_bound`

### 式

$$\mathrm{dist}\bigl(x(s),\mathrm{TCZ}\bigr)^2\le\frac1\eta\,\Phi_3(x(s))$$

### Lean のコメント（日本語訳）

> 誤差境界 \(\mathrm{dist}(x(s),\mathrm{TCZ})^2\le\Phi_3/\eta\)（\(C=1/\eta\)）。

### 補題の説明

**誤差境界**：共有 TCZ までの距離の二乗が、総残差の \(1/\eta\) 倍で抑えられる。

### 証明の概略

1. TCZ の元として LUB 配置 \(x_{ik}\equiv1\) を取る。
2. \(\mathrm{dist}\le\sqrt{D_2}\)（\(D_2=\sum_{i,k}(x_{ik}-1)^2\)）。
3. \(\Phi_3\ge\eta\sum_iA_i=\eta D_2\)（clamp が恒等な範囲で）から \(D_2\le\Phi_3/\eta\)。

----

<a id="Tomabechi.Examples.Theorem3.python_instance"></a>

## 定理 `python_instance`

### 式

$$\mathrm{dist}\bigl(x(s),\mathrm{TCZ}\bigr)\to0\ \wedge\ \bigl\|\iota(\varphi_i(x_i(s)))-\iota(L^\ast)\bigr\|\to0$$

### Lean のコメント（日本語訳）

> 定理3の結論：共有零集合への距離と、LUB 表象への距離が 0 に収束する。

### 補題の説明

**定理3の結論をこの 3 主体の例で取り出した**もの：共有零集合（合意）への距離と、各主体の表象の LUB への距離がともに 0 に収束します（**平均ではなく LUB に収束**）。

### 証明の概略

1. `theorem3_two_distances_tendsto_of_ac_ae_descent`（Theorem3）を \(c=4\eta\)、\(C=1/\eta\)、\(t_0=0\)、重み \(\eta_j=\eta\) で適用する。
2. 前提：共有残差の非負性 `sharedT_nonneg`、各項の非負性、TCZ の非空 `Lcfg_mem`、誤差境界 `error_bound`。
3. AC：区間 \([0,T]\) 上で \(\Phi_3=\Phi_F\)（`potential_eq`）、\(\Phi_F\) は \(C^1\)（`contDiff_PhiF`）なので絶対連続。
4. a.e. 下降：\(t>0\)（\(t=0\) は測度 0 なので除く。`potential_eq` は \(t\ge0\) でだけ成り立つので、\(t>0\) の近傍で \(\Phi_3=\Phi_F\)）で、`hasDerivAt_PhiF` と `PhiF_decay` から \(\Phi_3'\le-8\eta\Phi_3\)。（`xt_gradient_flow` はこの定理では使わず、軌道が勾配流であることの別の確認。）

----


## コメント修正記録

（なし）
