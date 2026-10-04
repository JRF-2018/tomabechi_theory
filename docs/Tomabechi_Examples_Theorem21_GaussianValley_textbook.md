# Tomabechi/Examples/Theorem21_GaussianValley.lean 解説

> 対象: [`Tomabechi/Examples/Theorem21_GaussianValley.lean`](../Tomabechi/Examples/Theorem21_GaussianValley.lean)（定理21の Python 例（局所谷）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21（局所谷）の Python 例（`examples/theorem21_local_well.py`）の Lean 根拠です。目標 \(x_t=4\) への浅い引力 \(V_0(x)=0.05(x-4)^2\) と、偏った中心 \(x_b=6\) の**ガウス臨場感** \(S(x)=\exp(-(x-6)^2/2)\)（円環の局所チャート。\(U_b=[5.5,6.5]\) は対蹠点 \(0\ (\mathrm{mod}\,8)\) から遠く、`wrap` の特異点を踏まない）。\(\tilde V=V_0-\kappa\,p\,S\)（\(\kappa=1\)）。

**結論**：\(p>1\) で \(U_b\) の内部に**唯一の最小点** \(x^\ast\) があり、勾配流は \(x^\ast\) へ**指数収束**する（一般定理 `theorem21_identity_mobility_global_exponential_case`）。

**監査の結果（Python の旧パラメータは前提を満たさなかった）**：旧 Python は \(m=1,\ r=1.5,\ \beta=0.1,\ B=0.3\) を使い \(p_{\rm crit}\approx0.2\) としましたが、ガウス核の \(-S''=(1-d^2)e^{-d^2/2}\) は \(|d|<1\) でしか正でなく、(21.2) \(-\nabla^2S\succeq mI\)（\(m=1\)）は \(d=0\) 以外で破れます。Lean が認める定数は \(r=\tfrac12\)、\(m=\tfrac12\)（\(-S''\ge\tfrac34e^{-1/8}\ge\tfrac{21}{32}\ge\tfrac12\)）、\(\beta=0\)（\(V_0''=0.1>0\)）、\(B=\tfrac14\)（\(|V_0'|=|x-4|/10\le\tfrac14\)）、したがって \(p_{\rm crit}=\max(\beta,B/r)/(\kappa m)=1\)。**Python 側を \(r=0.5,\ m=0.5,\ B=0.25,\ p_{\rm crit}=1\) に直しました。**

### 0.2 このファイルが証明していないこと

- **局所結果**です。\(U_b\)（閉球 \(\bar B(6,1/2)\)）の中の初期点についての結論で、大域的な結論ではありません。
- 1 次元の特殊例（恒等移動度）であり、一般の定理21の代替ではありません。
- 旧パラメータが前提を満たさなかった、という監査結果は、Python 側の修正の根拠で、原文の定理21の反例ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理21の Python 例（`examples/theorem21_local_well.py`）の Lean 根拠
>
> 目標 \(x_t=4\) への浅い引力 \(V_0(x)=0.05(x-4)^2\) と、偏った中心 \(x_b=6\) のガウス臨場感 \(S(x)=\exp(-(x-6)^2/2)\)（円環の局所チャート。\(U_b=[5.5,6.5]\) は対蹠点 \(0\ (\mathrm{mod}\,8)\) から遠く、`wrap` の特異点を踏まない）。\(\tilde V=V_0-\kappa pS\)、\(\kappa=1\)。
>
> **監査の結果（Python の旧パラメータは前提を満たさない）：** 旧 Python は \(m=1\)、\(r=1.5\)、\(\beta=0.1\)、\(B=0.3\) を使い \(p_{\rm crit}\approx0.2\) としたが、ガウス核の \(-S''=(1-d^2)e^{-d^2/2}\) は \(|d|<1\) でしか正でなく、(21.2) \(-\nabla^2S\succeq mI\)（\(m=1\)）は \(d=0\) 以外で破れる。Lean が認める定数は \(r=1/2\)、\(m=1/2\)（\(-S''\ge(3/4)e^{-1/8}\ge21/32\ge1/2\)）、\(\beta=0\)（\(V_0''=0.1>0\)）、\(B=1/4\)（\(|V_0'|=|x-4|/10\le1/4\)）、したがって \(p_{\rm crit}=\max(\beta,B/r)/(\kappa m)=1\)。Python 側を \(r=0.5\)、\(m=0.5\)、\(B=0.25\)、\(p_{\rm crit}=1\) に直した。
>
> 結論：\(p>1\) で \(U_b\) 内部に唯一の最小点 \(x^\ast\) があり、勾配流は \(x^\ast\) へ指数収束（一般定理 `theorem21_identity_mobility_global_exponential_case`）。

名前空間は `Tomabechi.Examples.Theorem21`（`open Tomabechi.Examples.Gaussian`）。

---

<a id="Tomabechi.Examples.Theorem21.V"></a>

## 定義 `V`

### 式

$$V_0(x)=\tfrac1{20}(x-4)^2$$

### Lean のコメント（日本語訳）

> 目標への引力の基礎ポテンシャル \(V_0(x)=0.05(x-4)^2\)。

### 定義の説明

目標 \(x=4\) への浅い（弱い）引力のポテンシャル。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem21.gradV"></a>

## 定義 `gradV`

### 式

$$V_0'(x)=\tfrac1{10}(x-4)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(V_0\) の勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem21.S"></a>

## 定義 `S`

### 式

$$S(x)=-\mathrm{well}_{1,1,6}(x)=e^{-(x-6)^2/2}$$

### Lean のコメント（日本語訳）

> ガウス臨場感 \(S(x)=\exp(-(x-6)^2/2)\)。

### 定義の説明

偏った中心 \(x_b=6\) の臨場感（`Gaussian.well` の符号を反転したもの）。

### 証明の概略

1. 定義：`-well 1 1 6 x`。

----

<a id="Tomabechi.Examples.Theorem21.gradS"></a>

## 定義 `gradS`

### 式

$$S'(x)=-\mathrm{dwell}_{1,1,6}(x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(S\) の勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem21.HS"></a>

## 定義 `HS`

### 式

$$H_S(x)=\langle-\mathrm{ddwell}_{1,1,6}(x),\cdot\rangle$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(S\) のヘッセ行列（1 次元なので内積で表す連続線形写像）。

### 証明の概略

1. 定義：`innerSL ℝ (-ddwell 1 1 6 x)`。

----

<a id="Tomabechi.Examples.Theorem21.HV"></a>

## 定義 `HV`

### 式

$$H_V=\langle\tfrac1{10},\cdot\rangle$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(V_0\) のヘッセ行列（定数 \(1/10\)）。

### 証明の概略

1. 定義：`innerSL ℝ (1/10)`。

----

<a id="Tomabechi.Examples.Theorem21.S_eq"></a>

## 定理 `S_eq`

### 式

$$S(x)=e^{-(x-6)^2/2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`S` の閉じた式を確認する（`well` の定義の展開）。

### 証明の概略

1. `well` の定義を展開し、符号を整理（`ring_nf`）。

----

<a id="Tomabechi.Examples.Theorem21.hasDerivAt_V"></a>

## 定理 `hasDerivAt_V`

### 式

$$\frac{d}{dx}V_0=\mathrm{gradV}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gradV` が `V` の導関数。

### 証明の概略

1. べき乗・定数倍の微分。

----

<a id="Tomabechi.Examples.Theorem21.hasDerivAt_gradV"></a>

## 定理 `hasDerivAt_gradV`

### 式

$$\frac{d}{dx}V_0'=\tfrac1{10}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gradV` の導関数は定数 \(1/10\)（\(\beta=0\) の根拠：\(V_0''=0.1>0\)）。

### 証明の概略

1. 線形関数の微分。

----

<a id="Tomabechi.Examples.Theorem21.hasDerivAt_S"></a>

## 定理 `hasDerivAt_S`

### 式

$$\frac{d}{dx}S=\mathrm{gradS}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gradS` が `S` の導関数。

### 証明の概略

1. `Gaussian.hasDerivAt_well` の符号反転。

----

<a id="Tomabechi.Examples.Theorem21.hasDerivAt_gradS"></a>

## 定理 `hasDerivAt_gradS`

### 式

$$\frac{d}{dx}S'=-\mathrm{ddwell}_{1,1,6}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gradS` の導関数が `-ddwell`。

### 証明の概略

1. `Gaussian.hasDerivAt_dwell` の符号反転。

----

<a id="Tomabechi.Examples.Theorem21.ddwell_ge"></a>

## 定理 `ddwell_ge`

### 式

$$|x-6|\le\tfrac12\Rightarrow\mathrm{ddwell}_{1,1,6}(x)\ge\tfrac12$$

### Lean のコメント（日本語訳）

> \(|x-6|\le1/2\) で \(\mathrm{ddwell}\ge1/2\)（\(-S''\le-1/2\)）。

### 補題の説明

**(21.2) の定数 \(m=1/2\) の根拠**：球の中で \(-S''=(1-d^2)e^{-d^2/2}\ge\frac34e^{-1/8}\ge\frac{21}{32}\ge\frac12\)。

### 証明の概略

1. \(d=|x-6|\le\frac12\) で \(1-d^2\ge\frac34\)。
2. \(e^{-d^2/2}\ge e^{-1/8}\)、\(e^{-1/8}\ge\frac78\)（\(e^{-t}\ge1-t\)）なので \(\frac34\cdot\frac78=\frac{21}{32}\ge\frac12\)。

----

<a id="Tomabechi.Examples.Theorem21.python_valley"></a>

## 定理 `python_valley`

### 式

$$p>1,\ x_0\in\bar B(6,\tfrac12)\Rightarrow\exists x^\ast\in\mathrm{int}\bar B,\ \text{最小点}\ \wedge\ \exists\text{軌道},\ \tilde V\text{ の差と距離が指数減衰}$$

### Lean のコメント（日本語訳）

> Python のパラメータ（\(r=1/2\)、\(m=1/2\)、\(\beta=0\)、\(B=1/4\)、\(\kappa=1\)）の下で、\(p>1=p_{\rm crit}\) なら \(U_b=[5.5,6.5]\) 内部に唯一…（一般定理の結論）：最小点の存在と、勾配流の指数収束。

### 補題の説明

**定理21の一般結論をこの 1 次元ガウス谷で取り出した**もの：\(p>1\) なら、\(U_b\) の内部に最小点 \(x^\ast\) があり、\(U_b\) 内の初期点からの勾配流が、ポテンシャル差 \(\tilde V-\tilde V(x^\ast)\) について \(e^{-2(\kappa pm-\beta)(t-a)}\)、距離について \(\sqrt{2\Delta/(\kappa pm-\beta)}\,e^{-(\kappa pm-\beta)(t-a)}\) で指数収束します。

### 証明の概略

1. `ddwell_ge` で (21.2)（\(m=\frac12\)）、\(V_0''=\frac1{10}\) から \(\beta=0\)、\(|V_0'|\le\frac14\) から \(B=\frac14\)、球 \(r=\frac12\) を確認。
2. 臨場感の閾値 \(p>\max(\beta,B/r)/(\kappa m)=1\) を仮定 `hp` として、一般定理 `theorem21_identity_mobility_global_exponential_case` を適用。

----


## コメント修正記録

（なし）
