# Tomabechi/Consistency/ConsistencyR123_DomainTheorems.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_DomainTheorems.lean`](../Tomabechi/Consistency/ConsistencyR123_DomainTheorems.lean)（定理1・2・4 を共通領域 X 全体で共有評価 commonV0X について）。
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
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 1・2・4 を、共通領域 \(X\) の全体で、共有評価 \(V_0^X(x)=1+2(x_0-x_1)^2\) について**述べるファイルです。以前の段階では、定理 20・24 が全域で \(V_0^X\) を使うこと、全段 \(U_n\subset X\) は示しましたが、定理 1・2・4 を、箱の外の初期点を含む \(X\) の全体で述べ直すことが残っていました。理由は、定理 2 の個人の閾値の残差 \([(x_i)^2-\theta]_+\)（\(\theta=1/10\) 固定、`DA`）で、箱の外では \(\Phi_2\ne V_0^X-1\) だったことです。

**閾値 \(\theta\) は、原文の定理 2 の自由なパラメータ**なので、\(\theta\) を大きく取り直した並列の残差系 `DX`（\(\theta_X=10\)）を置きます。\(X_3:=\{x\mid\forall i,\ |x_i|\le3\}\)（段の閉球 \(\bar B_3(0)\) を含む）の上では、個人の残差の項は消え、\(\Phi_2^X(x)=2(x_0-x_1)^2=V_0^X(x)-1\) となります。したがって、

* **定理 2：** `DX`・\(X_3\) の全初期点・全非負開始時刻で、定理 2 の定量的な結論（共有 TCZ までの距離・個人残差・辺の不整合の指数減衰と極限）。
* **定理 1：** 閾値 1 の残差 \(\mathrm{residual}_1(V_0^X(y),1)=2(y_0-y_1)^2\)。**\(\mathbb R^2\) の全初期点**で成り立つ。
* **定理 4：** 臨場感 \(P=e^{-(V_0^X-1)}\)、\(Q=1\)、\(\kappa=1\)、\(\theta_P=0\)。**\(\mathbb R^2\) の全初期点**で成り立つ。

三つとも、同じ \(V_0^X\)・同じ一点 \(K\)（実際の流れの閉到達集合）・同じ共有の流れで、20 の拡張・24 の有限層の費用と同じ評価です。\(N\) の `pointAdapter` の流れ・到達集合を通して述べます。

### 0.2 このファイルが証明していないこと

* 定理 2 は \(X_3\) の上です（\(\theta_X\) を \(X_3\) の大きさに合わせて取るため）。定理 1・4 は全域です。
* 定理 3（\(\Phi_3\) は抽象残差で、零平均の箱の点に限る）は、共通状態領域の対象外です。
* 旧い `N.base.V0`・`DA`（\(\theta=1/10\)、箱）に基づく入口は、旧版として残ります（置換は最終の統合で行います）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前の段階では、定理20・24 が全域で commonV0X = 1 + 2(x₀−x₁)² を使うこと、全段 U_n ⊂ X は示したが、定理1・2・4 を箱の外の初期点を含む X 全体で述べ直すことが残っていた。理由は定理2の個人閾値残差 [(x_i)²−θ]₊（θ=1/10 固定、DA）で、箱の外では Φ₂ ≠ commonV0X − 1 だった。閾値 θ は原文の定理2の自由なパラメータなので、θ を大きく取り直した並列の残差系 DX（θX=10）を置く。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.domainX3"></a>

## 定義 `domainX3`

### 式

$$
X_3=\{x\mid\forall i,\ |x_i|\le3\}
$$

### Lean のコメント（日本語訳）

> 領域X3：各座標の絶対値≤3（段の閉球を含む）。

### 定義の説明

領域 \(X_3\) です。各座標の絶対値が 3 以下（段の閉球を含みます）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.θX"></a>

## 定義 `θX`

### 式

$$
\theta_X=10
$$

### Lean のコメント（日本語訳）

> X3に合わせて大きく取った個人閾値（原文の定理2のパラメータ）。

### 定義の説明

\(X_3\) に合わせて大きく取った、個人の閾値 \(\theta_X=10\) です（原文の定理 2 のパラメータ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.DX"></a>

## 定義 `DX`

### 式

$$
\text{定理 2 の並列の共有残差系（閾値だけ }\theta_X\text{）}
$$

### Lean のコメント（日本語訳）

> 定理2の並列の共有残差系：DAと同じ構造で閾値だけθX。

### 定義の説明

定理 2 の**並列の共有残差系**です。`DA` と同じ構造で、閾値だけが \(\theta_X\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.DX_potential_eq"></a>

## 補題 `DX_potential_eq`

### 式

$$
\Phi_2^X(x)=[x_0^2-\theta_X]_++[x_1^2-\theta_X]_++\gamma(x_0-x_1)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

並列の残差系のポテンシャルは、個人の残差二項と、辺の不整合の項の和です。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.DX_potential_eq_on_X3"></a>

## 補題 `DX_potential_eq_on_X3`

### 式

$$
x\in X_3\ \Rightarrow\ \Phi_2^X(x)=V_0^X(x)-1
$$

### Lean のコメント（日本語訳）

> X3の上でDX.potential=commonV0X−1。

### 補題の説明

\(X_3\) の上で、並列の残差系のポテンシャルは、\(V_0^X-1\) に等しいです。

### 証明の概略

1. \(|x_i|\le3\) なので \(x_i^2\le9<10=\theta_X\)、個人の残差は 0。残りは辺の不整合の項。

----

<a id="Tomabechi.Consistency.R123.Fg"></a>

## 定義 `Fg`

### 式

$$
F(y)=V_0^X(y)-1=2(y_0-y_1)^2
$$

### Lean のコメント（日本語訳）

> 全域の共有残差F y=commonV0X y−1=2(y₀−y₁)²。

### 定義の説明

**全域の共有残差** \(F(y)=V_0^X(y)-1=2(y_0-y_1)^2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.Fg_eq"></a>

## 補題 `Fg_eq`

### 式

$$
F(y)=2(y_0-y_1)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差は \(2(y_0-y_1)^2\) です。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.Fg_nonneg"></a>

## 補題 `Fg_nonneg`

### 式

$$
F\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差は非負です。

### 証明の概略

1. 二乗の非負性。

----

<a id="Tomabechi.Consistency.R123.Fg_flow"></a>

## 補題 `Fg_flow`

### 式

$$
F(\varphi_t(x))=F(x)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 共有flow上でFは率6で減衰（全初期点）。

### 補題の説明

共有の流れの上で、\(F\) は**率 6 で減衰**します（全初期点）。

### 証明の概略

1. 流れの下での差の式（`consensusOptimalFlow_gap`）と、指数の計算。

----

<a id="Tomabechi.Consistency.R123.agreementPoint_mem_K"></a>

## 補題 `agreementPoint_mem_K`

### 式

$$
\text{合意点}\in K
$$

### Lean のコメント（日本語訳）

> 合意点は一点Kに属する。

### 補題の説明

合意点は、一点 \(K\) に属します。

### 証明の概略

1. \(K\) が軌道の線分であること。線分の端点（パラメータ 0）が合意点。

----

<a id="Tomabechi.Consistency.R123.Fg_agreement"></a>

## 補題 `Fg_agreement`

### 式

$$
F(\text{合意点})=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点で共有残差は 0 です。

### 証明の概略

1. 合意点の座標は等しい。

----

<a id="Tomabechi.Consistency.R123.flow_mem_X3"></a>

## 補題 `flow_mem_X3`

### 式

$$
x\in X_3,\ t_0\le t\ \Rightarrow\ \varphi_t(x)\in X_3
$$

### Lean のコメント（日本語訳）

> 共有flowはX3を保つ（開始時刻以降）。

### 補題の説明

共有の流れは、\(X_3\) を保ちます（開始時刻以降）。

### 証明の概略

1. 流れの式 \(\varphi_t(x)_i=\text{平均}+(x_i-\text{平均})e^{-3(t-t_0)}\) と、\(0<e^{-3(t-t_0)}\le1\)。各座標が \([-3,3]\) 内にある。

----

<a id="Tomabechi.Consistency.R123.agreementPoint_mem_X3"></a>

## 補題 `agreementPoint_mem_X3`

### 式

$$
x\in X_3\Rightarrow\text{合意点}\in X_3
$$

### Lean のコメント（日本語訳）

> 合意点・一点K（線分）はX3に入る。

### 補題の説明

合意点は \(X_3\) に入ります（一点 \(K\) の線分も）。

### 証明の概略

1. 平均の絶対値が 3 以下。

----

<a id="Tomabechi.Consistency.R123.dist_flow_agreement_sq_le"></a>

## 補題 `dist_flow_agreement_sq_le`

### 式

$$
\mathrm{dist}(\varphi_t(x),\text{合意点})^2\le F(\varphi_t(x))
$$

### Lean のコメント（日本語訳）

> 共有flowの合意点への距離の二乗は、その点の共有残差以下（全初期点）。

### 補題の説明

共有の流れの、合意点への距離の二乗は、その点の共有残差以下です（全初期点）。

### 証明の概略

1. 流れの合意点への距離の評価（`consensusOptimalFlow_dist_agreementPoint_le`）を二乗する。

----

<a id="Tomabechi.Consistency.R123.hasDerivAt_Fexp"></a>

## 補題 `hasDerivAt_Fexp`

### 式

$$
\tfrac{d}{ds}\bigl(Fe^{-6(s-t_0)}\bigr)=-6\,Fe^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 率6の指数F e^{-6(t−t₀)}の微分。

### 補題の説明

率 6 の指数 \(Fe^{-6(t-t_0)}\) の微分です。

### 証明の概略

1. 合成関数の微分（`hasDerivAt_exp` と一次関数）。

----

<a id="Tomabechi.Consistency.R123.Fexp_ac"></a>

## 補題 `Fexp_ac`

### 式

$$
Fe^{-6(s-t_0)}\text{ は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

率 6 の指数は、絶対連続です。

### 証明の概略

1. \(C^1\) なので絶対連続（`contDiffOn.absolutelyContinuousOnInterval`）。

----

<a id="Tomabechi.Consistency.R123.point1TargetX"></a>

## 定義 `point1TargetX`

### 式

$$
\{y\in K\mid V_0^X(y)\le1\}
$$

### Lean のコメント（日本語訳）

> 一点K内の閾値1のTCZ（commonV0Xについて）。

### 定義の説明

一点 \(K\) の内部の、閾値 1 の TCZ です（\(V_0^X\) について）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.residual1_commonV0X"></a>

## 補題 `residual1_commonV0X`

### 式

$$
\mathrm{residual}_1(V_0^X(y),1)=F(y)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閾値 1 の残差は、共有残差 \(F\) に等しいです。

### 証明の概略

1. \(F\ge0\) から、最大値の取り方（`max_eq_left`）。

----

<a id="Tomabechi.Consistency.R123.agreement_mem_target1"></a>

## 補題 `agreement_mem_target1`

### 式

$$
\text{合意点}\in\text{目標}_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点は、定理 1 の目標に入ります。

### 証明の概略

1. \(K\) に属し、\(F=0\) なので \(V_0^X=1\le1\)。

----

<a id="Tomabechi.Consistency.R123.theorem1_commonDomainX"></a>

## 定理 `theorem1_commonDomainX`

### 式

$$
\text{定理 1：}\mathrm{infDist}\le\sqrt{F(x)}\,e^{-3(t-t_0)}\ \wedge\ \to0\ \ (\text{全初期点})
$$

### Lean のコメント（日本語訳）

> 定理1（commonV0X、ℝ²の全初期点・全非負開始時刻）。

### 補題の説明

**定理 1**（\(V_0^X\)、\(\mathbb R^2\) の全初期点・全非負開始時刻）です。流れが \(K\) に留まり、TCZ への距離が \(\sqrt{F(x)}\,e^{-3(t-t_0)}\) 以下で、0 に収束します。

### 証明の概略

1. 定理 1 の一般の補題（`theorem1_reachable_tcz_distance_tendsto_zero`）に、共有残差の減衰（`Fg_flow`）・距離の評価（`dist_flow_agreement_sq_le`）・絶対連続性（`Fexp_ac`）を渡す。

----

<a id="Tomabechi.Consistency.R123.effX"></a>

## 定義 `effX`

### 式

$$
\tilde V=V_0^X-\kappa PQ\ \ (\kappa=1,\ P=e^{-F},\ Q=1)
$$

### Lean のコメント（日本語訳）

> 実効評価Ṽ=V₀−κPQ（κ=1）。

### 定義の説明

**実効評価** \(\tilde V=V_0^X-\kappa PQ\) です（\(\kappa=1\)、\(P=e^{-F}\)、\(Q=1\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.effX_eq"></a>

## 補題 `effX_eq`

### 式

$$
\tilde V=1+F-e^{-F}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効評価は \(1+F-e^{-F}\) です。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.effX_bounds"></a>

## 補題 `effX_bounds`

### 式

$$
F\le\tilde V\le2F
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効評価は、\(F\) 以上、\(2F\) 以下です。

### 証明の概略

1. \(e^{-F}\le1\)、\(1-F\le e^{-F}\)（`add_one_le_exp`）から。

----

<a id="Tomabechi.Consistency.R123.effX_nonneg"></a>

## 補題 `effX_nonneg`

### 式

$$
\tilde V\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効評価は非負です。

### 証明の概略

1. \(\tilde V\ge F\ge0\)。

----

<a id="Tomabechi.Consistency.R123.point4TargetX"></a>

## 定義 `point4TargetX`

### 式

$$
\text{閾値 0 の臨場感加重 TCZ（一点 }K\text{ 内）}
$$

### Lean のコメント（日本語訳）

> 閾値0の臨場感加重TCZ（一点K内）。

### 定義の説明

閾値 0 の、臨場感で重みづけた TCZ です（一点 \(K\) の内部）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.agreement_mem_target4"></a>

## 補題 `agreement_mem_target4`

### 式

$$
\text{合意点}\in\text{目標}_4
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

合意点は、定理 4 の目標に入ります。

### 証明の概略

1. \(K\) に属し、\(F=0\) なので \(\tilde V=0\)。

----

<a id="Tomabechi.Consistency.R123.residual4_X"></a>

## 補題 `residual4_X`

### 式

$$
\mathrm{residual}_4=\tilde V
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 4 の残差は、実効評価 \(\tilde V\) に等しいです。

### 証明の概略

1. \(\tilde V\ge0\) なので `max` が外れる。

----

<a id="Tomabechi.Consistency.R123.effX_flow"></a>

## 補題 `effX_flow`

### 式

$$
\tilde V(\varphi_t(x))=\text{明示式}(F(x),t_0,t)
$$

### Lean のコメント（日本語訳）

> 共有flowに沿った実効残差の明示式。

### 補題の説明

共有の流れに沿った、実効残差の**明示式**です。

### 証明の概略

1. `effX_eq` と `Fg_flow`。

----

<a id="Tomabechi.Consistency.R123.theorem4_commonDomainX"></a>

## 定理 `theorem4_commonDomainX`

### 式

$$
\text{定理 4：}\mathrm{infDist}\le\sqrt{\tilde V(x)}\,e^{-\frac32(t-t_0)}\ \wedge\ \to0\ \ (\text{全初期点})
$$

### Lean のコメント（日本語訳）

> 定理4（commonV0X、ℝ²の全初期点・全非負開始時刻）。

### 補題の説明

**定理 4**（\(V_0^X\)、\(\mathbb R^2\) の全初期点・全非負開始時刻）です。流れが \(K\) に留まり、臨場感加重 TCZ への距離が \(\sqrt{\tilde V(x)}\,e^{-\frac32(t-t_0)}\) 以下で、0 に収束します。

### 証明の概略

1. 定理 4 の一般の補題に、実効残差の明示式（`effX_flow`）・上下界（`effX_bounds`）・絶対連続性を渡す。

----

<a id="Tomabechi.Consistency.R123.DX_connected"></a>

## 補題 `DX_connected`

### 式

$$
\text{グラフ }(\mathrm{Fin}\,2)\text{ は連結}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二点のグラフは連結です。

### 証明の概略

1. 二点の場合分け。辺 0 が二点をつなぐ。

----

<a id="Tomabechi.Consistency.R123.theorem2_commonDomainX"></a>

## 定理 `theorem2_commonDomainX`

### 式

$$
\text{定理 2：}X_3\text{ の全初期点で、共有 TCZ までの距離・個人残差・辺不整合の指数減衰と極限}
$$

### Lean のコメント（日本語訳）

> 定理2（DX、X3の全初期点・全非負開始時刻）。

### 補題の説明

**定理 2**（`DX`、\(X_3\) の全初期点・全非負開始時刻）です。定理 2 の定量的な結論（共有 TCZ までの距離・個人残差・辺の不整合の指数減衰と極限）が成り立ちます。

### 証明の概略

1. 並列の残差系の連結性（`DX_connected`）、ポテンシャルが \(F(x)e^{-6(s-t_0)}\) であること（`DX_potential_eq_on_X3` と `Fg_flow`）を、定理 2 の一般の結論に渡す。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.pointAdapter_is_consensus"></a>

## 補題 `SharedDataPreservation.pointAdapter_is_consensus`

### 式

$$
N.\mathrm{pointAdapter}.\mathrm{flow}=\text{共有 flow}\ \wedge\ \mathrm{reachable}=K
$$

### Lean のコメント（日本語訳）

> Nのpointadapterのflow・到達集合は、任意の初期点・開始時刻で共有flow・一点Kと一致する。

### 補題の説明

\(N\) の一点アダプターの流れ・到達集合は、任意の初期点・開始時刻で、共有の流れ・一点 \(K\) と一致します。

### 証明の概略

1. 流れの保存式（`point_flow`）と、選ばれた流れが率 3 の流れであること、到達集合の保存式。

----

<a id="Tomabechi.Consistency.R123.SharedDomainTheorems"></a>

## 構造体 `SharedDomainTheorems`

### 式

$$
\text{定理 1・2・4 を、同じ }V_0^X\text{・同じ共有 flow・同じ一点 }K\text{ で}
$$

### Lean のコメント（日本語訳）

> 定理1・2・4を、同じcommonV0X・同じ共有flow・同じ一点Kで、共通領域の上で述べた受入型。定理1・4はℝ²全体、定理2はX3（θX=10）。

### 定義の説明

定理 1・2・4 を、同じ \(V_0^X\)・同じ共有の流れ・同じ一点 \(K\) で、共通領域の上で述べた**受入の型**です。定理 1・4 は \(\mathbb R^2\) 全体、定理 2 は \(X_3\)（\(\theta_X=10\)）。フィールドは、\(N\) の流れ・到達集合が共有の流れ・一点 \(K\)（全初期点）、評価（\(\Phi_2^X=V_0^X-1\)（\(X_3\) の上）、\(\mathrm{residual}_1=V_0^X-1\)）、定理 1・2・4、20 の拡張と 24 の有限層の費用が同じ \(V_0^X\) を全域で使う、段の閉球が同じ領域 \(X\) に入る・座標の上で \(X_3\) に入る、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.stageHull_subset_X3"></a>

## 補題 `stageHull_subset_X3`

### 式

$$
\bar B_3(0)\subset X_3\ (\text{座標の上で})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉球 \(\bar B_3(0)\) は、座標の上で \(X_3\) に入ります。

### 証明の概略

1. ノルムが 3 以下なら、各座標の絶対値も 3 以下（`PiLp.norm_apply_le`）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_domainTheorems"></a>

## 定理 `sharedModel_domainTheorems`

### 式

$$
\mathrm{SharedDomainTheorems}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、共通領域の上の定理 1・2・4 の入力を満たします。

### 証明の概略

1. 各フィールドは、上の補題・定理と、共通状態領域の補題。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v10"></a>

## 定理 `final_consistency_v10`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedDomainTheorems}(N)
$$

### Lean のコメント（日本語訳）

> v10：v9に、定理1・2・4を共通領域・共有評価で述べた受入型を加えた存在宣言。

### 補題の説明

第 10 版です。第 9 版に、定理 1・2・4 を共通領域・共有評価で述べた受入の型を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
