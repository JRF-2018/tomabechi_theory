# Tomabechi/Consistency/ConsistencyR123_ReadingClosures.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_ReadingClosures.lean`](../Tomabechi/Consistency/ConsistencyR123_ReadingClosures.lean)（定理4の値域条件と sup／Euclid 距離の比較）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

二つのことを扱います。

* **定理 4 の値域の条件（M6.1）：** \(P=\exp(-F)\in(0,1]\)、\(Q=1\in[-1,1]\)、\(\kappa=1\) で、\(\tilde V=V_0-\kappa PQ\ge-\kappa\)（実際は \(\tilde V\ge0\)）。
* **定理 1–4 と 20 の距離の統一：** 1–4 は状態空間 `AgentState`（\(\mathbb R^2\) の sup 距離）で、20 は同じ状態の Euclid 座標の距離で、誤差を述べていました。\(\mathbb R^2\) では \(\|\cdot\|_\infty\le\|\cdot\|_2\le\sqrt2\,\|\cdot\|_\infty\) なので、集合への距離は \(\mathrm{infDist}_\infty\le\mathrm{infDist}_2\le\sqrt2\cdot\mathrm{infDist}_\infty\)。1–4 の二乗の誤差の境界を、Euclid 距離で述べ直すと、**定数が 2 倍**になります（`SharedNormUnification`）。

### 0.2 このファイルが証明していないこと

* 距離の統一は、誤差の境界の**定数を 2 倍に緩める**ものです。sup 距離での元の境界が、そのまま Euclid 距離で成り立つとは主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理4の値域（M6.1）：P = exp(−F) ∈ (0,1]、Q = 1 ∈ [−1,1]、κ = 1 で Ṽ = V₀ − κPQ ≥ −κ（実際は Ṽ ≥ 0）。定理1–4と20の距離の統一：1–4 は状態空間 AgentState（ℝ² の sup 距離）で、20 は同じ状態の Euclid 座標（c1EuclideanCoordinates）の距離で誤差を述べていた。ℝ² では ‖·‖_∞ ≤ ‖·‖₂ ≤ √2 ‖·‖_∞ なので、集合への距離は infDist_sup ≤ infDist_Euclid ≤ √2 · infDist_sup。1–4 の二乗誤差境界を Euclid 距離で述べ直すと定数が 2 倍になる（SharedNormUnification）。

---

<a id="Tomabechi.Consistency.R123.commonBasePresenceP_mem"></a>

## 補題 `commonBasePresenceP_mem`

### 式

$$
P=\exp(-F)\in(0,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

臨場感 \(P=\exp(-F)\) は \((0,1]\) に入ります。

### 証明の概略

1. \(\exp>0\)。\(F\ge0\)（潜在の非負性）から \(\exp(-F)\le 1\)。

----

<a id="Tomabechi.Consistency.R123.commonBasePresenceQ_mem"></a>

## 補題 `commonBasePresenceQ_mem`

### 式

$$
Q=1\in[-1,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(Q=1\) は \([-1,1]\) に入ります。

### 証明の概略

1. 定義を展開して計算。

----

<a id="Tomabechi.Consistency.R123.commonBase_tildeV_ge"></a>

## 補題 `commonBase_tildeV_ge`

### 式

$$
\tilde V=V_0-\kappa PQ\ \ge -\kappa\ (\kappa=1)
$$

### Lean のコメント（日本語訳）

> κ=1でṼ=V₀−κPQ≥−κ（実際は0以上）。

### 補題の説明

\(\kappa=1\) で、\(\tilde V=V_0-\kappa PQ\ge-\kappa\) です（実際は 0 以上です）。

### 証明の概略

1. \(P\le 1\)、\(V_0>0\)、\(Q=1\) を使い、`nlinarith`。

----

<a id="Tomabechi.Consistency.R123.c1EuclideanCoordinates_symm_eq"></a>

## 補題 `c1EuclideanCoordinates_symm_eq`

### 式

$$
\text{座標の逆写像}=\text{そのまま }L^2\text{ の型へ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 座標の逆写像は、座標をそのまま \(L^2\) 型の点と見たものです。

### 証明の概略

1. 連続線形同値の逆写像の等式（`symm_apply_eq`）と、座標の補題。

----

<a id="Tomabechi.Consistency.R123.dist_sup_le_dist_euclid"></a>

## 補題 `dist_sup_le_dist_euclid`

### 式

$$
\|y-a\|_\infty\le\|y-a\|_2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

sup 距離は Euclid 距離以下です。

### 証明の概略

1. 各座標について、\(|y_i-a_i|^2\) は二乗和以下（`Finset.single_le_sum`）なので、平方根を取る。

----

<a id="Tomabechi.Consistency.R123.dist_euclid_le_sqrt_two_mul_dist_sup"></a>

## 補題 `dist_euclid_le_sqrt_two_mul_dist_sup`

### 式

$$
\|y-a\|_2\le\sqrt2\,\|y-a\|_\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 距離は \(\sqrt2\) 倍の sup 距離以下です。

### 証明の概略

1. 二乗して、二座標の二乗和が各座標の二乗の \(2\) 倍以下であること（各座標の距離は sup 距離以下）。

----

<a id="Tomabechi.Consistency.R123.infDist_euclid_le"></a>

## 補題 `infDist_euclid_le`

### 式

$$
\mathrm{infDist}_{\infty}\le\mathrm{infDist}_{2}\le\sqrt2\,\mathrm{infDist}_\infty
$$

### Lean のコメント（日本語訳）

> 集合への距離：infDist_sup≤infDist_Euclid≤√2·infDist_sup。

### 補題の説明

集合への距離の比較です。\(\mathrm{infDist}_\infty\le\mathrm{infDist}_2\le\sqrt2\,\mathrm{infDist}_\infty\)。このうち、右の不等式です。

### 証明の概略

1. 空集合でないときは、各点への距離の比較（前の補題）から下限を比べる。空集合のときは距離が 0 で自明。

----

<a id="Tomabechi.Consistency.R123.infDist_sup_le"></a>

## 補題 `infDist_sup_le`

### 式

$$
\mathrm{infDist}_\infty\le\mathrm{infDist}_2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

集合への距離の比較の、左の不等式です。

### 証明の概略

1. 各点への距離の比較（`dist_sup_le_dist_euclid`）から、下限を比べる。空集合のときは自明。

----

<a id="Tomabechi.Consistency.R123.euclid_sq_error_of_sup"></a>

## 補題 `euclid_sq_error_of_sup`

### 式

$$
\mathrm{infDist}_\infty^2\le B\ \Rightarrow\ \mathrm{infDist}_2^2\le 2B
$$

### Lean のコメント（日本語訳）

> 二乗誤差境界をEuclid距離で述べ直すと定数が2倍になる。

### 補題の説明

二乗の誤差の境界を、Euclid 距離で述べ直すと、**定数が 2 倍**になります。

### 証明の概略

1. 像の集合を `L^2` 型の像に書き換える。
2. 前の補題（右の不等式）で距離を \(\sqrt2\) 倍し、二乗する。

----

<a id="Tomabechi.Consistency.R123.SharedNormUnification"></a>

## 構造体 `SharedNormUnification`

### 式

$$
\mathrm{infDist}_2^2\le 2\cdot(\text{定理 }1,2,3,4\text{ の誤差})
$$

### Lean のコメント（日本語訳）

> 1–4の誤差境界を、定理20と同じEuclid座標の距離で述べた版（定数2倍）。

### 定義の説明

定理 1–4 の誤差の境界を、**定理 20 と同じ Euclid 座標の距離**で述べた版です（定数が 2 倍）。フィールドは、定理 1・2・3・4 の誤差の境界です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedPointDomainInputs.normUnification"></a>

## 定理 `SharedPointDomainInputs.normUnification`

### 式

$$
\mathrm{SharedNormUnification}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点 \(K\) の全域の入力から、距離の統一が従います。

### 証明の概略

1. 各フィールドは、sup 距離の誤差の境界（`SharedPointDomainInputs` の `error1`–`error4`）に、前の補題（定数が 2 倍）を適用する。

----

<a id="Tomabechi.Consistency.R123.sharedModel_normUnification"></a>

## 定理 `sharedModel_normUnification`

### 式

$$
\mathrm{SharedNormUnification}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、距離の統一を満たします。

### 証明の概略

1. 前の定理を、`sharedModel_pointDomainInputs` に適用する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
