# Tomabechi/Consistency/ConsistencyR123_SharedTheorem1.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem1.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem1.lean)（共有署名の基礎評価・一点 K による定理1）。
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
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**基礎評価**と**一点 K**から、**定理1**を適用するファイルです。閾値 1 の残差は、定理2の共有残差 \(\Phi_2\) と一致します。定理2と**同じ実際の流れ・一点 K・絶対連続性・散逸・誤差境界**を、一般の定理1に渡します。

### 0.2 このファイルが証明していないこと

* 箱の中の二主体の具体モデルに限ります。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 閾値1の残差は DA の共有残差と一致する。定理2と同じ実 flow・一点 K・AC・散逸・誤差境界を一般定理1へ渡す。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem1PointTarget"></a>

## 定義 `SharedModelSignature.theorem1PointTarget`

### 式

$$
\{y\in N.\mathrm{reachable}\mid N.\mathrm{base}.V_0(y,t)\le1\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共有署名 \(N\) の、定理1の目標集合です。\(N\) の一点の到達集合のうち、基礎評価が閾値 1 以下の点の集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedBase_residual"></a>

## 補題 `sharedBase_residual`

### 式

$$
\mathrm{residual}_1(V_0,1)=\Phi_2(y,t)
$$

### Lean のコメント（日本語訳）

> 共有基礎評価の閾値1残差を、時間依存の共有残差へ同定する。

### 補題の説明

共有基礎評価の、閾値 1 の残差を、時間に依存する**共有残差 \(\Phi_2\)** に同定します。

### 証明の概略

1. 基礎評価は \(1+\Phi_2(\cdot,0)\)（`V0_eq_shared`）。共有残差は時刻に依らない（`potential_eq`）。
2. \(\Phi_2\ge0\)（`consensusPresence_potential_nonneg`）なので、\([1+\Phi_2-1]_+=\Phi_2\)。

----

<a id="Tomabechi.Consistency.R123.sharedBase_pointTargets"></a>

## 補題 `sharedBase_pointTargets`

### 式

$$
N.\mathrm{theorem1PointTarget}=N.\mathrm{theorem2PointTarget}
$$

### Lean のコメント（日本語訳）

> Nの基礎評価のTCZと定理2の共有TCZは、同じ一点K上で一致する。

### 補題の説明

\(N\) の基礎評価の TCZ（定理1の目標）と、定理2の共有 TCZ は、**同じ一点 K の上で一致**します。

### 証明の概略

1. 両方向。基礎評価 \(\le1\) は、残差（前の補題）\(\Phi_2=0\) と同値（残差は非負）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem2PointInputs.theorem1"></a>

## 定理 `SharedTheorem2PointInputs.theorem1`

### 式

$$
\operatorname{dist}\le\sqrt{\mathrm{residual}_1(V_0(x,t_0),1)}\,e^{-3(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> 定理2の解析入力を共有し、一般定理1の到達性・率3距離・極限を得る。評価はN.baseそのもの、目標はNの実一点到達閉包上の閾値集合である。

### 補題の説明

定理2の解析入力を**共有**して、一般の定理1の、到達性・率 3 の距離評価・極限を得ます。評価は `N.base` そのもの、目標は \(N\) の実際の一点の到達閉包の上の閾値集合です。

### 証明の概略

1. 定理1の残差が共有残差（`sharedBase_residual`）に等しいので、定理2の入力（絶対連続・散逸・誤差境界）がそのまま定理1の入力になる。
2. 定理1の一般形に渡し、率 3 の評価と極限を得る。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
