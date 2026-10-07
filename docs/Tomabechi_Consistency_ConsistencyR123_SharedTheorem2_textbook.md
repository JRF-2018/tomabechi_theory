# Tomabechi/Consistency/ConsistencyR123_SharedTheorem2.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem2.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem2.lean)（共有署名の一点到達集合に対する定理2）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**一点の到達集合**に対する、**定理2**を作るファイルです。箱の中のすべての初期点・非負の開始時刻について、\(N\) の実際の流れから、絶対連続性・散逸・誤差境界を作り、定理2の一般の状態対の入口から、全主体・全辺の残差と距離の定量的な評価と、極限を得ます。状態対の残差系 `DA` は、二主体の具体モデルです。

### 0.2 このファイルが証明していないこと

* 二主体の具体モデル（箱の中）に限ります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 箱内全初期点・非負開始時刻について、N の実 flow から AC・散逸・誤差境界を作る。定理2の一般状態対入口から、全主体・全辺の残差と距離の定量評価および極限を保つ。状態対残差系 DA は二主体の具体モデルである。

---

<a id="Tomabechi.Consistency.R123.sharedResidual_connected"></a>

## 補題 `sharedResidual_connected`

### 式

$$
\text{二主体・二向きの辺のグラフは連結}
$$

### Lean のコメント（日本語訳）

> 二主体・二向き辺の接続性。主体・辺の量化を省略しない。

### 補題の説明

二主体・二向きの辺のグラフの**連結性**です（任意の二人の主体が、辺でつながっている）。主体と辺の量化を省略しません。

### 証明の概略

1. 主体 0・1 の組を場合分け（`fin_cases`）。同じ主体は反射、異なる主体は辺 0（\(0\to1\)）で結ぶ。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem2PointTarget"></a>

## 定義 `SharedModelSignature.theorem2PointTarget`

### 式

$$
\mathrm{sharedTCZ}(N.\mathrm{reachable},t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有署名 \(N\) の、定理2の目標集合です。\(N\) の一点の到達集合の中の共有 TCZ です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem2PointPotential"></a>

## 定義 `SharedModelSignature.theorem2PointPotential`

### 式

$$
t\mapsto\Phi_2(N.\mathrm{flow}(t),t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(N\) の流れに沿った、定理2の共有残差です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem2PointInputs"></a>

## 構造体 `SharedTheorem2PointInputs`

### 式

$$
\text{一点初期状態の実到達集合と、同じ実 flow の解析前件}
$$

### Lean のコメント（日本語訳）

> 一点初期状態の実到達集合と、同じ実flowの解析前件。

### 定義の説明

一点の初期状態の**実際の到達集合**と、同じ実際の流れの**解析的な前件**です。フィールドは、到達集合は流れから作った閉到達集合、目標は空でない、残差は絶対連続、散逸（\(\dot\Phi\le-2\cdot3\,\Phi\)）、誤差境界（距離の二乗 \(\le\Phi\)）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem2Inputs"></a>

## 定理 `SharedKernelInputs.theorem2Inputs`

### 式

$$
\forall x\in\mathrm{box},t_0\ge0,\ \mathrm{SharedTheorem2PointInputs}(N,x,t_0)
$$

### Lean のコメント（日本語訳）

> 一点Kの目標は平均保存の合意点。実残差との誤差境界を各時刻で証明する。

### 補題の説明

一点 K の目標は、**平均が保存される合意点**です。実際の残差との誤差境界を、各時刻で証明します。

### 証明の概略

1. 保存式から、\(N\) の流れ・到達集合が、率 3 の流れ・一点 K（`pointReachableClosure`）に等しい。
2. 目標は合意点だけ（`pointSharedTCZ_eq_singleton`）。
3. 残差の絶対連続性・散逸・誤差境界は、前のファイル（`consensusPotentialAlong_*` など、率 3 の版）の補題から。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem2PointInputs.conclusion"></a>

## 定理 `SharedTheorem2PointInputs.conclusion`

### 式

$$
\mathrm{ReachableStatePairConclusion}
$$

### Lean のコメント（日本語訳）

> 一般定理2をNのflowと一点初期到達集合へ直接適用する。距離率3、全主体・全辺の残差率6、表象一致、三種類の極限を返す。

### 補題の説明

一般の定理2を、\(N\) の流れと一点の初期到達集合に**直接適用**します。距離は率 3、全主体・全辺の残差は率 6 で減衰し、表象が一致し、三種類の極限が得られます。

### 証明の概略

1. 定理2の到達可能な状態対の定量的な結論（`theorem2_reachable_state_pair_quantitative_conclusion`）に、グラフの連結性・率・到達（流れが到達集合に入る）・目標の非空・絶対連続・散逸・誤差境界を渡す。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
