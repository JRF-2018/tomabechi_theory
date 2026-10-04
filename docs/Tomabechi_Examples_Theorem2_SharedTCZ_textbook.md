# Tomabechi/Examples/Theorem2_SharedTCZ.lean 解説

> 対象: [`Tomabechi/Examples/Theorem2_SharedTCZ.lean`](../Tomabechi/Examples/Theorem2_SharedTCZ.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

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
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理2（共有 TCZ）の Python 例（`examples/theorem02_shared_tcz.py`）のうち、共有 TCZ の部分の Lean 根拠です。2 主体 \(i\in\mathrm{Fin}\,2\)、状態 \(x_i\in\mathbb R\)、\(h_i(x)=x\)、基礎評価 \(V_{0,i}=(x-c_i)^2\)、閾値 \(\theta=1/10\)、不整合 \(S=(x_0-x_1)^2\)（有向辺 2 本、各重み \(\gamma/2\)、\(\gamma=2\)）。**共有残差**
$$\Phi_2=\sum_i\bigl[(x_i-c_i)^2-\theta\bigr]_++\gamma(x_0-x_1)^2\qquad(\texttt{StatePairResidualSystem.potential})$$

- **ケース A（谷が一致 \(c=(0,0)\)）**：共有零集合 \(\Omega_2=\{(z,z):|z|\le\sqrt\theta\}\) は非空。共同方策 \(\dot x_i=-x_i\)（\(\Omega_2\) 内の点 \(0\) への合意方策）、\(x(0)=(2,-2)\) について、定理2の一般結論 `theorem2_state_pair_conditional_conclusion` の**全前提**（絶対連続、a.e. 下降 \(\Phi'\le-2c\Phi\)（\(c=1\)）、誤差境界 \(\mathrm{dist}^2\le2\Phi\)、\(\Omega_2\) が非空、連結性）を証明します。
- **ケース B（谷が遠い \(c=(0,3)\)）**：すべての \(x\) で \(\Phi_2\ge3\)。共有零集合は空で、補題0の下降条件と誤差境界は満たされえず、不整合または個人残差が正のまま残ります（原文 §4「必要な追加条件」）。

### 0.2 このファイルが証明していないこと

- このファイルのケース A は、解析的に扱える**合意方策** \(\dot x_i=-x_i\) の軌道 `trajA` で定理2の前提を確かめるものです。Python が実際に使う \(\Phi_2\) の**劣勾配流**（Euler 更新）の軌道を表すものではありません。劣勾配流の連続時間版から定理2へつなぐ部分は、別ファイル `Tomabechi/Examples/Theorem2_SubgradientFlow.lean` にあります。
- Euler 離散化の誤差や Python の数値出力は証明の対象外です。
- ケース B は「共有零集合が空のとき結論が出ない」例で、原文の定理2の反例ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理2の Python 例（`examples/theorem02_shared_tcz.py`）の共有 TCZ 根拠
>
> 2 主体 \(i\in\mathrm{Fin}\,2\)、状態 \(x_i\in\mathbb R\)、\(h_i(x)=x\)、基礎評価 \(V_{0,i}=(x-c_i)^2\)、閾値 \(\theta=1/10\)、不整合 \(S=(x_0-x_1)^2\)（有向辺 2 本、各重み \(\gamma/2\)、\(\gamma=2\)）。共有残差 \(\Phi_2=\sum_i[(x_i-c_i)^2-\theta]_++\gamma(x_0-x_1)^2\)（`StatePairResidualSystem.potential`）。
>
> * **ケース A（谷が一致 \(c=(0,0)\)）：** 共有零集合 \(\Omega_2=\{(z,z):|z|\le\sqrt\theta\}\) は非空。このファイルでは共同方策 \(\dot x_i=-x_i\) の定理2への適用を示す。Python の劣勾配流に対応する解析軌道と定理2への接続は `Theorem2_SubgradientFlow.lean` で別途証明する。
> * **ケース B（谷が遠い \(c=(0,3)\)）：** すべての \(x\) で \(\Phi_2\ge3\)。共有零集合は空で、補題0の下降条件と誤差境界は満たされえず、不整合または個人残差が正のまま残る（原文 §4「必要な追加条件」）。
>
> 注意：`trajA` は追加の合意方策であり、Python の Euler 更新を表す軌道ではない。


### 0.4 節見出しのコメント（日本語訳）

> ## ケース B（反例）：すべての \(x\) で \(\Phi_2\ge3\)
>
> ## ケース A：誤差境界
>
> ## ケース A：合意方策 \(\dot x_i=-x_i\) の軌道

名前空間は `Tomabechi.Examples.Theorem2`（`open Tomabechi.Theorem2`、後半で `open MeasureTheory`）。

---

<a id="Tomabechi.Examples.Theorem2.θ"></a>

----

<a id="Tomabechi.Examples.Theorem2.θ"></a>

## 定義 `θ`

### 式

$$\theta=\tfrac1{10}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

個人残差の閾値（許容誤差）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.γ"></a>

## 定義 `γ`

### 式

$$\gamma=2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

不整合の重み。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.endpointF"></a>

## 定義 `endpointF`

### 式

$$e_0=(0,1),\ e_1=(1,0)$$

### Lean のコメント（日本語訳）

> 有向辺 \(e_0=(0,1)\)、\(e_1=(1,0)\)。

### 定義の説明

2 主体を結ぶ 2 本の有向辺（両向き）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.Dsys"></a>

## 定義 `Dsys`

### 式

$$\mathcal D_c=\text{（共有残差系：谷の中心 }c\text{）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

谷の中心 \(c=(c_0,c_1)\) をパラメータにもつ共有残差系 `StatePairResidualSystem`：各主体の評価 \((x-c_i)^2\)、閾値 \(\theta\)、辺 `endpointF`、不整合 \((x_0-x_1)^2\)（重み \(\gamma/2\) ずつ）。

### 証明の概略

1. `StatePairResidualSystem` の各フィールドを具体的に与える。

----

<a id="Tomabechi.Examples.Theorem2.DA"></a>

## 定義 `DA`

### 式

$$\mathcal D_A=\mathcal D_{(0,0)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース A（谷が一致）の系。

### 証明の概略

1. `Dsys ![0, 0]`。

----

<a id="Tomabechi.Examples.Theorem2.DB"></a>

## 定義 `DB`

### 式

$$\mathcal D_B=\mathcal D_{(0,3)}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B（谷が遠い）の系。

### 証明の概略

1. `Dsys ![0, 3]`。

----

<a id="Tomabechi.Examples.Theorem2.potential_eq"></a>

## 補題 `potential_eq`

### 式

$$\Phi_2(x)=\bigl[(x_0-c_0)^2-\theta\bigr]_++\bigl[(x_1-c_1)^2-\theta\bigr]_++\gamma(x_0-x_1)^2$$

### Lean のコメント（日本語訳）

> 共有残差の具体形（\(\Phi_2=\sum_i[(x_i-c_i)^2-\theta]_++\gamma(x_0-x_1)^2\)）。

### 補題の説明

一般の共有残差の定義を、このモデルで具体的な式に直したもの。

### 証明の概略

1. `StatePairResidualSystem.potential` の定義を展開し、`Fin 2` の和を展開（`Fin.sum_univ_two`）。辺の重み \(\gamma/2\) が 2 本で \(\gamma\) になる。

----

<a id="Tomabechi.Examples.Theorem2.caseB_potential_ge"></a>

## 補題 `caseB_potential_ge`

### 式

$$\Phi_2(x)\ge3\quad(\forall x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**ケース B の下界**：谷が遠い（\(c=(0,3)\)）ので、どんな \(x\) でも共有残差が 3 以上。

### 証明の概略

1. `potential_eq` で \(\Phi_2=[x_0^2-\theta]_++[(x_1-3)^2-\theta]_++2(x_0-x_1)^2\)。
2. `le_max_left` で \([a]_+\ge a\) とし、\(x_0^2-\frac1{10}+(x_1-3)^2-\frac1{10}+2(x_0-x_1)^2\ge3\) を示す。これは \(x_0,x_1\) の凸な 2 次式の下界で、平方の項（\((x_0-\frac65)^2,(x_1-\frac95)^2,(x_0-x_1+\frac35)^2\)）を使った `nlinarith`。

----

<a id="Tomabechi.Examples.Theorem2.caseB_sharedTCZ_empty"></a>

## 補題 `caseB_sharedTCZ_empty`

### 式

$$\Omega_2^B=\emptyset$$

### Lean のコメント（日本語訳）

> 共有零集合は空：どの点でも \(\Phi_2\ne0\)、したがって下降条件・誤差境界の前提が満たされえない。

### 補題の説明

**共有零集合が空**：どんな \(x\) でも共有残差が正なので、「全主体が同時に目標を満たす点」が存在しません。

### 証明の概略

1. `caseB_potential_ge` で \(\Phi_2\ge3>0\)。零集合の元は \(\Phi_2=0\) を満たすはずなので矛盾。

----

<a id="Tomabechi.Examples.Theorem2.sqrtθ_sq"></a>

## 補題 `sqrtθ_sq`

### 式

$$(\sqrt\theta)^2=\theta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\sqrt\theta\) の二乗が \(\theta\)。

### 証明の概略

1. `Real.sq_sqrt`（\(\theta\ge0\)）。

----

<a id="Tomabechi.Examples.Theorem2.sqrtθ_pos"></a>

## 補題 `sqrtθ_pos`

### 式

$$\sqrt\theta>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\sqrt\theta\) が正。

### 証明の概略

1. `Real.sqrt_pos`。

----

<a id="Tomabechi.Examples.Theorem2.zstar"></a>

## 定義 `zstar`

### 式

$$z^\ast(s)=\mathrm{clamp}\bigl(s,-\sqrt\theta,\sqrt\theta\bigr)$$

### Lean のコメント（日本語訳）

> 平均 \(s\) の合意点への射影 \(z^\ast=\mathrm{clamp}(s,-\sqrt\theta,\sqrt\theta)\)。

### 定義の説明

2 主体の平均 \(s\) を、共有零集合の上の点 \((z,z)\)（\(|z|\le\sqrt\theta\)）へ射影した値。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.zstar_sq_le"></a>

## 補題 `zstar_sq_le`

### 式

$$z^\ast(s)^2\le\theta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影した点が共有零集合の条件を満たす。

### 証明の概略

1. clamp の定義で場合分け（\(|z^\ast|\le\sqrt\theta\)）。

----

<a id="Tomabechi.Examples.Theorem2.clamp_sq_le_hinge"></a>

## 補題 `clamp_sq_le_hinge`

### 式

$$\Bigl(\tfrac{a+b}2-z^\ast\Bigr)^2\le\bigl[a^2-\theta\bigr]_++\bigl[b^2-\theta\bigr]_+$$

### Lean のコメント（日本語訳）

> 目標外の平均 \(s\)：\((s-z^\ast)^2\le\) 個人残差の和。

### 補題の説明

**誤差境界の核**：平均が目標の外にあるとき、その超過分の二乗は個人残差の和で抑えられる。

### 証明の概略

1. 平均が \([-\sqrt\theta,\sqrt\theta]\) の内なら左辺 0。外なら \(s-z^\ast=|s|-\sqrt\theta\)。
2. \(|a|,|b|\) の少なくとも一方が \(|s|\) 以上であることから、個人残差 \([a^2-\theta]_+\) の評価に帰着（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem2.caseA_error_bound"></a>

## 補題 `caseA_error_bound`

### 式

$$\mathrm{dist}(x,\Omega_2)^2\le2\,\Phi_2(x)\quad(\forall x)$$

### Lean のコメント（日本語訳）

> 誤差境界 \(\mathrm{dist}(x,\Omega_2)^2\le2\Phi_2\)（全ての \(x\) で。\(\Omega_2=\mathrm{sharedTCZ}\ \mathrm{univ}\)）。

### 補題の説明

**ケース A の誤差境界**（\(C=2\)）：共有零集合までの距離の二乗が、共有残差の 2 倍で抑えられる。

### 証明の概略

1. TCZ の元の候補として、平均 \(s=\frac{x_0+x_1}2\) を clamp した合意点 \((z^\ast,z^\ast)\)（\(z^\ast=\mathrm{clamp}(s,-\sqrt\theta,\sqrt\theta)\)）を取る（`zstar_sq_le` で共有零集合に属する）。
2. 状態空間は `Fin 2 → ℝ`（sup 距離）なので、\(\mathrm{dist}(x,q)\le|s-z^\ast|+\frac{|x_0-x_1|}2\)。
3. 二乗して \(\le2(s-z^\ast)^2+\frac{(x_0-x_1)^2}2\)（`nlinarith`）。
4. `clamp_sq_le_hinge` で \((s-z^\ast)^2\le\) 個人残差の和。不整合項は \(\gamma(x_0-x_1)^2=2(x_0-x_1)^2\) で \(\frac12(x_0-x_1)^2\) を抑える。合わせて \(\le2\Phi_2\)。

----

<a id="Tomabechi.Examples.Theorem2.x0"></a>

## 定義 `x0`

### 式

$$x_0=(2,-2)$$

### Lean のコメント（日本語訳）

> 初期点 \((2,-2)\)。

### 定義の説明

2 主体の初期状態（互いに逆向きに離れている）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.trajA"></a>

## 定義 `trajA`

### 式

$$x_i(t)=x_{0,i}\,e^{-t}$$

### Lean のコメント（日本語訳）

> 共同方策（\(\Omega_2\) 内の点 \(0\) への合意）\(\dot x_i=-x_i\) の解。

### 定義の説明

両主体が原点（合意点）へ指数的に近づく軌道。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.PhiA"></a>

## 定義 `PhiA`

### 式

$$\Phi_A(t)=2\bigl[4e^{-2t}-\theta\bigr]_++16\gamma\,e^{-2t}$$

### Lean のコメント（日本語訳）

> 軌道上の \(\Phi_2\)：\(2[4e^{-2t}-\theta]_++16\gamma e^{-2t}\)。

### 定義の説明

軌道に沿った共有残差の閉じた式（個人残差 2 つ＋不整合 \(\gamma\cdot16e^{-2t}\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem2.potential_trajA"></a>

## 補題 `potential_trajA`

### 式

$$\Phi_2(x(t))=\Phi_A(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道上の共有残差が `PhiA` に一致。

### 証明の概略

1. `potential_eq` を軌道に適用：\(x_0=2e^{-t}\)、\(x_1=-2e^{-t}\)、\((x_0-x_1)^2=16e^{-2t}\)。

----

<a id="Tomabechi.Examples.Theorem2.hasDerivAt_rsq"></a>

## 補題 `hasDerivAt_rsq`

### 式

$$\frac{d}{dt}e^{-2t}=-2\,e^{-2t}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\bigl(e^{-t}\bigr)^2\) の導関数。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成。

----

<a id="Tomabechi.Examples.Theorem2.contDiff_rsq"></a>

## 補題 `contDiff_rsq`

### 式

$$t\mapsto e^{-2t}\ \text{は }C^1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(C^1\) であること。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem2.PhiA_ac"></a>

## 補題 `PhiA_ac`

### 式

$$\Phi_A\ \text{は絶対連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**補題0の前提 (AC)**：軌道上の共有残差が絶対連続（\(C^1\) 関数と `max · 0` の合成）。

### 証明の概略

1. `contDiff_rsq` と、`max · 0` の 1-Lipschitz 性から絶対連続。

----

<a id="Tomabechi.Examples.Theorem2.zero_set_subsingleton"></a>

## 補題 `zero_set_subsingleton`

### 式

$$\{t\mid4e^{-2t}-\theta=0\}\ \text{は高々1点}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ヒンジ \([4e^{-2t}-\theta]_+\) の折れ曲がり点が高々 1 点（\(e^{-2t}\) は狭義単調）。a.e. 微分で測度 0 の例外集合として使います。

### 証明の概略

1. `e^{-2t}` の単射性。

----

<a id="Tomabechi.Examples.Theorem2.PhiA_decay"></a>

## 補題 `PhiA_decay`

### 式

$$\Phi_A'(s)\le-2\cdot1\cdot\Phi_A(s)\ \text{ a.e.}$$

### Lean のコメント（日本語訳）

> a.e. 下降 \(\Phi'\le-2\Phi\)（\(c=1\)）。

### 補題の説明

**補題0の前提（a.e. 下降）**。

### 証明の概略

1. 折れ曲がり点（高々 1 点）を除いて、ヒンジが正なら \(\Phi_A'=2\cdot4\cdot(-2)e^{-2t}+16\gamma(-2)e^{-2t}=-2\Phi_A\)、ヒンジが 0 なら \(\Phi_A=16\gamma e^{-2t}\) で \(\Phi_A'=-2\Phi_A\)。どちらでも \(\le-2\Phi_A\)。

----

<a id="Tomabechi.Examples.Theorem2.connectedA"></a>

## 補題 `connectedA`

### 式

$$\forall i,j,\ i\leadsto j\ \text{（辺の無向経路）}$$

### Lean のコメント（日本語訳）

> 連結性。

### 補題の説明

2 主体の関係グラフが連結（辺 \(e_0=(0,1)\) で結ばれる）。

### 証明の概略

1. `decide`（有限グラフ）。

----

<a id="Tomabechi.Examples.Theorem2.sharedTCZ_nonempty"></a>

## 補題 `sharedTCZ_nonempty`

### 式

$$\Omega_2^A\ne\emptyset$$

### Lean のコメント（日本語訳）

> 共有零集合は非空（原点）。

### 補題の説明

原点 \((0,0)\) が共有零集合に属する。

### 証明の概略

1. \(\Phi_2(0,0)=0\)（\(0\le\theta\) で個人残差 0、不整合 0）。

----

<a id="Tomabechi.Examples.Theorem2.caseA_conclusion"></a>

## 補題 `caseA_conclusion`

### 式

$$\text{軌道}\in K\ \wedge\ \mathrm{dist}\le\sqrt{2\Phi(0)}\,e^{-t}\ \wedge\ \text{個人残差・不整合の指数減衰}\ \wedge\ \text{共有零集合上で表象が一致}$$

### Lean のコメント（日本語訳）

> 定理2の一般結論（ケース A）。

### 補題の説明

**定理2の一般結論をケース A で取り出した**もの：(i) 共有零集合までの距離が \(\sqrt{2\Phi(0)}e^{-t}\) で減衰、(ii) 個人残差が \(\frac{\Phi(0)}{w_i}e^{-2t}\) で減衰、(iii) 不整合も同様、(iv) 共有零集合の上では全主体の表象が一致。

### 証明の概略

1. 一般定理 `theorem2_state_pair_conditional_conclusion`（Theorem2）の前提を、`PhiA_ac`・`PhiA_decay`・`caseA_error_bound`・`sharedTCZ_nonempty`・`connectedA` で満たして適用。

----

## コメント修正記録

- 冒頭コメントの「すべての `x` で `Φ2≥1`」を、実際に証明されている下界（`caseB_potential_ge`）に合わせて「`Φ2≥3`」に修正した（コメントのみの変更。宣言は不変）。
- 2026-10-04: 冒頭コメントが、ケース A を合意方策の適用に限定し、劣勾配流は `Theorem2_SubgradientFlow.lean` に譲る記述へ変更された（`.lean` 側の変更）。本書の 0.1–0.3 をそれに合わせて書き直した。
