# Tomabechi/Consistency/ConsistencyC1_Theorem4.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_Theorem4.lean`](../Tomabechi/Consistency/ConsistencyC1_Theorem4.lean)（非定数の臨場感を持つ、定理4の一次元モデル）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**非定数の臨場感**を持つ、定理4の一次元モデルです。流れは `linearFlow 3 0`（目標 0、ゲイン 3）。臨場感 \(P(x)=e^{-x^2}\)（定数でなく、0〜1 に入る）、\(Q=1\)、基礎評価 \(V_0(x)=1+x^2+P(x)\) とすると、実効ポテンシャル \(V_0-\kappa PQ\) は \(1+x^2\) になり、残差は \(x^2\)、加重 TCZ は原点だけです。このモデルで、**任意の初期値**・**任意の非負開始時刻**からの全未来について、定理4の定量結論（率 3 の指数収束）が成り立ちます。

### 0.2 このファイルが証明していないこと

* 状態は一次元です。二主体の二次元の定理4は、別のファイル（`ConsistencyC1_ConsensusControl`）にあります。
* 臨場感は、具体的な関数 \(e^{-x^2}\) です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理1/H-flow のスカラー閉ループ `linearFlow 3 0` を使い、`P(x)=exp(-x²)`、`Q=1`、`V₀(x)=1+x²+P(x)` とする。臨場感は非定数で `[0,1]` に入り、実効ポテンシャルは `1+x²` となる。この具体モデルでは、任意の初期値と非負開始時刻からの全未来について定理4の定量結論を得る。

---

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.presenceP4"></a>

## 定義 `presenceP4`

### 式

$$
P(x)=e^{-x^2}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理4の臨場感 \(P\) です。\(e^{-x^2}\)。定数でなく、状態によって値が変わります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.presenceQ4"></a>

## 定義 `presenceQ4`

### 式

$$
Q\equiv1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

第二の臨場感 \(Q\) は定数 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.presenceV04"></a>

## 定義 `presenceV04`

### 式

$$
V_0(x)=1+x^2+P(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

基礎評価です。\(P\) を足してあるので、実効ポテンシャル \(V_0-\kappa PQ\) では \(P\) が打ち消されます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.effectivePotential_eq"></a>

## 補題 `effectivePotential_eq`

### 式

$$
V_0-\kappa PQ=1+x^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効ポテンシャル（\(\kappa=1\)）は \(1+x^2\) です。

### 証明の概略

1. 定義を展開し、\(P\) を打ち消す（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.presenceP4_bounds"></a>

## 補題 `presenceP4_bounds`

### 式

$$
0<P\le1
$$

### Lean のコメント（日本語訳）

> 臨場感は `[0,1]` の範囲にあり、状態によって値が変化する。

### 補題の説明

臨場感は 0 より大きく 1 以下です（定理4の値域条件）。

### 証明の概略

1. \(\exp>0\)。\(-x^2\le0\) から \(\exp\le1\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.presenceP4_nonconstant"></a>

## 補題 `presenceP4_nonconstant`

### 式

$$
P(0)\ne P(1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

臨場感は定数でありません（\(P(0)=1\)、\(P(1)=e^{-1}<1\)）。

### 証明の概略

1. \(e^{-1}<1\)（`exp_lt_one_iff`）。\(P(0)=1\)、\(P(1)=e^{-1}\) を代入して比べる。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.residual4_eq_sq"></a>

## 補題 `residual4_eq_sq`

### 式

$$
\text{residual}_4=x^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の残差は \(x^2\) です。

### 証明の概略

1. 実効ポテンシャルが \(1+x^2\)。\(\max(x^2,0)=x^2\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.weightedTCZ_univ_eq_zero"></a>

## 補題 `weightedTCZ_univ_eq_zero`

### 式

$$
\mathrm{weightedTCZ}=\{0\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全空間での加重 TCZ は、原点だけです。

### 証明の概略

1. 実効ポテンシャル \(1+x^2\le1\iff x=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4ResidualPath"></a>

## 定義 `t4ResidualPath`

### 式

$$
s\mapsto\text{residual}_4\bigl(\Phi_{t_0\to s}(x)\bigr)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

流れに沿った定理4の残差の関数です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4ResidualPath_eq"></a>

## 補題 `t4ResidualPath_eq`

### 式

$$
\text{residual path}(s)=\bigl(x\,e^{-3(s-t_0)}\bigr)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

残差は \((x\,e^{-3(s-t_0)})^2\) です。

### 証明の概略

1. 残差 \(=x^2\)（前の補題）に、流れの式（`linearFlow`）を代入する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4ResidualPath_ac"></a>

## 補題 `t4ResidualPath_ac`

### 式

$$
\text{絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

残差は絶対連続です。

### 証明の概略

1. 閉形式は C¹（`fun_prop`）なので絶対連続。実残差と一致する（前の補題）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4ResidualPath_deriv"></a>

## 補題 `t4ResidualPath_deriv`

### 式

$$
\frac{d}{ds}\text{resid}=-6\,\text{resid}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

残差の微分は \(-6\) 倍の残差です。

### 証明の概略

1. 指数の引数の微分は \(-3\)。\(\exp\)・定数倍・二乗の合成の微分（連鎖律）を整理する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4ResidualPath_decay_ae"></a>

## 補題 `t4ResidualPath_decay_ae`

### 式

$$
\frac{d}{ds}\text{resid}\le-2\cdot3\,\text{resid}\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の入口が要求する下降条件（率 3）を、ほとんど至る所で満たします（実際は等式）。

### 証明の概略

1. 前の補題の導関数の式から。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.t4_error_bound"></a>

## 補題 `t4_error_bound`

### 式

$$
\operatorname{dist}(x(s),\mathrm{TCZ})^2\le\text{residual}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標 TCZ までの距離の二乗は、残差以下です（誤差境界）。

### 証明の概略

1. TCZ は原点のみ（`weightedTCZ_univ_eq_zero`）。一点集合への距離は \(\lvert\cdot\rvert\)。残差は \(x^2\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem4.linearFlow_theorem4"></a>

## 定理 `linearFlow_theorem4`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{weightedTCZ}\bigr)\le\sqrt{\text{resid}(t_0)}\,e^{-3(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> 同じ `linearFlow 3 0` が作る閉到達集合を用いた定理4の全時間結論。Pは非定数、Qは非零で、任意の実初期値から全ての未来時刻で定量評価する。

### 補題の説明

一次元の流れ `linearFlow 3 0` に定理4を適用した、全時間の結論です。\(P\) は定数でなく、\(Q\) は 0 でなく、**任意の実数の初期値**から、すべての未来時刻で、加重 TCZ までの距離が \(\sqrt{\text{残差}(t_0)}\,e^{-3(t-t_0)}\) 以下で、0 に収束します。

### 証明の概略

1. 閉到達集合は全体（`linearFlow_closedReachable_univ`）。
2. 残差の絶対連続・下降（率 3）・誤差境界（前の補題）を、定理4の一般入口に渡す。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
