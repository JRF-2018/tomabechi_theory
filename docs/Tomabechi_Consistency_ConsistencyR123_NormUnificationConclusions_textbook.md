# Tomabechi/Consistency/ConsistencyR123_NormUnificationConclusions.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_NormUnificationConclusions.lean`](../Tomabechi/Consistency/ConsistencyR123_NormUnificationConclusions.lean)（定理1・3・4の距離の結論を Euclid 距離で（H-flow″））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理 1・3・4 の**結論**（状態の TCZ への距離の指数評価と極限）も、定理 20 と同じ Euclid 距離で述べるファイルです（H-flow″）。以前は、定理 1–4 の**誤差の境界**（二乗誤差の前件）を Euclid 距離で述べ直しました（`SharedNormUnification`）。ここでは結論の側を扱います。\(\|\cdot\|_\infty\le\|\cdot\|_2\le\sqrt2\|\cdot\|_\infty\) から、集合への距離は \(\mathrm{infDist}_2\le\sqrt2\cdot\mathrm{infDist}_\infty\) なので、指数評価の定数は \(\sqrt2\) 倍になり、極限は 0 のまま保たれます。

### 0.2 このファイルが証明していないこと

* 定理 2 の結論は、一般定理側の抽象記録（`ReachableStatePairConclusion`）で返るので、ここでは Euclid 版を作りません（定理 1 の結論が、定理 2 の解析入力から導かれる形で含みます）。
* 距離の比較は、\(\mathbb R^2\) の二つのノルムの同値性によります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前は 1–4 の誤差境界（二乗誤差の前件）を Euclid 距離で述べ直した（SharedNormUnification）。ここでは、1・3・4 の結論（状態の TCZ への距離の指数評価と極限）も、定理20と同じ Euclid 距離（c1EuclideanCoordinates）で述べる。‖·‖∞ ≤ ‖·‖₂ ≤ √2‖·‖∞ から、集合への距離は infDist_E ≤ √2 · infDist_sup なので、指数評価の定数は √2 倍になり、極限は 0 のまま保たれる。範囲：定理2の結論は一般定理側の抽象記録（ReachableStatePairConclusion）で返るためここでは Euclid 版を作らない。…

---

<a id="Tomabechi.Consistency.R123.euclid_infDist_le_of_sup"></a>

## 補題 `euclid_infDist_le_of_sup`

### 式

$$
\mathrm{infDist}_\infty\le b\ \Rightarrow\ \mathrm{infDist}_2\le\sqrt2\,b
$$

### Lean のコメント（日本語訳）

> 距離の評価のEuclid版（定数√2倍）。

### 補題の説明

距離の評価の Euclid 版です（定数が \(\sqrt2\) 倍）。

### 証明の概略

1. 像の集合を `L^2` 型の像に書き換える。
2. 集合への距離の比較（`infDist_euclid_le`）と、仮定の \(\mathrm{infDist}_\infty\le b\) を合わせる。

----

<a id="Tomabechi.Consistency.R123.euclid_tendsto_of_sup"></a>

## 補題 `euclid_tendsto_of_sup`

### 式

$$
\mathrm{infDist}_\infty\to0\ \Rightarrow\ \mathrm{infDist}_2\to0
$$

### Lean のコメント（日本語訳）

> 距離の極限0はEuclid距離でも保たれる。

### 補題の説明

距離の極限 0 は、Euclid 距離でも保たれます。

### 証明の概略

1. 挟み撃ち（`squeeze_zero`）。下は非負、上は \(\sqrt2\) 倍の sup 距離。

----

<a id="Tomabechi.Consistency.R123.SharedNormUnificationConclusions"></a>

## 構造体 `SharedNormUnificationConclusions`

### 式

$$
\mathrm{infDist}_2(\cdot,\mathrm{TCZ})\le\sqrt2\cdot(\text{指数評価})\ \wedge\ \to0
$$

### Lean のコメント（日本語訳）

> 定理1・3・4の距離の結論（指数評価と極限）を、定理20と同じEuclid距離で述べた版。

### 定義の説明

定理 1・3・4 の**距離の結論**（指数評価と極限）を、定理 20 と同じ Euclid 距離で述べた版です。フィールドは、定理 1・3・4 のそれぞれの結論です（指数評価の定数は \(\sqrt2\) 倍、極限は 0 のまま）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.normUnificationConclusions"></a>

## 定理 `SharedKernelInputs.normUnificationConclusions`

### 式

$$
\mathrm{SharedNormUnificationConclusions}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有の核の入力から、定理 1・3・4 の結論の Euclid 版が従います。

### 証明の概略

1. 各定理の sup 距離の結論（`theorem2Inputs` などから）に、前の二つの補題（定数 \(\sqrt2\) 倍・極限 0 の保存）を適用する。

----

<a id="Tomabechi.Consistency.R123.sharedModel_normUnificationConclusions"></a>

## 定理 `sharedModel_normUnificationConclusions`

### 式

$$
\mathrm{SharedNormUnificationConclusions}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、距離の結論の統一を満たします。

### 証明の概略

1. 前の定理を `sharedModel_kernelInputs` に適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_norm_conclusions"></a>

## 定理 `final_consistency_v2_with_norm_conclusions`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedNormUnificationConclusions}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 2 版の存在宣言に、距離の結論の統一を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。前の版から \(N\) を取り、新しい部品を加える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
