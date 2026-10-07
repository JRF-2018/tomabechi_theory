# Tomabechi/Consistency/ConsistencyR3_Theorem4Entry.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR3_Theorem4Entry.lean`](../Tomabechi/Consistency/ConsistencyR3_Theorem4Entry.lean)（共通基礎評価の、定理4の一般入口（一点 K））。
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
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**共通基礎評価**（定理1と同じ \(1+F\)、臨場感 \(e^{-F}\)）を使う、**定理4の一般の入口**を、**一点の初期状態の閉到達集合 K** で実際に適用するファイルです。実効残差の絶対連続性・微分の散逸・誤差境界を供給し、一般定理4を適用して、距離の評価（率 \(3/2\)）と 0 への収束を得ます。箱の中の二主体の率 3 の具体モデルに限ります。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通基礎評価」（R3）の部品です。

### 0.2 このファイルが証明していないこと

* 箱の中の二主体の具体モデルに限ります。
* 一般の入口から得る率は \(3/2\) です（より強い率 3 の評価は、共有署名のファイルで、具体的な幾何から別に得ます）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 基礎評価は定理1と同じ `1+F`、臨場感は `exp(-F)` である。一点初期状態の閉到達 K に対し、実効残差の AC・微分散逸・誤差境界を供給し、一般定理4を適用する。箱内の二主体 rate-3 具体モデルに限る。

---

<a id="Tomabechi.Consistency.R3.sharedT4Explicit"></a>

## 定義 `sharedT4Explicit`

### 式

$$
1+Fe^{-6(t-t_0)}-\exp\bigl(-Fe^{-6(t-t_0)}\bigr)
$$

### Lean のコメント（日本語訳）

> 共有実効残差の明示式。箱内軌道に沿うFの率6減衰を代入する。

### 定義の説明

共有の実効残差の**明示的な式**です。箱の中の軌道に沿って、基礎残差 \(F\) が率 6 で減衰する（\(F\to Fe^{-6(t-t_0)}\)）ことを代入したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT4Residual"></a>

## 定義 `sharedT4Residual`

### 式

$$
\mathrm{residual}_4(V_0,P,Q,\kappa=1,\theta=0)\ \text{（流れの上）}
$$

### Lean のコメント（日本語訳）

> 一般入口へ渡す、実際の共有評価から読んだ残差。

### 定義の説明

一般の入口へ渡す、**実際の共有評価から読んだ残差**です（共通基礎評価 \(V_0\)・臨場感 \(P,Q\)・\(\kappa=1\)・閾値 0）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT4Residual_eq_effective"></a>

## 補題 `sharedT4Residual_eq_effective`

### 式

$$
\mathrm{residual}=V_{\text{eff}}
$$

### Lean のコメント（日本語訳）

> 閾値0の共有実効評価は非負なので、正部分を取っても値は変わらない。

### 補題の説明

閾値 0 の共有の実効評価は非負なので、正の部分を取っても値は変わりません（残差 \(=\) 実効評価）。

### 証明の概略

1. 実効評価は \(F\) 以上（`commonBaseTheorem4_bounds`）で、\(F\ge0\)。非負なので \(\max(\cdot,0)\) は値を変えない。

----

<a id="Tomabechi.Consistency.R3.sharedBasePotential_rate3"></a>

## 補題 `sharedBasePotential_rate3`

### 式

$$
F(\Phi(x,t))=F(x)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 同じrate-3軌道上の基礎残差Fの厳密な時間表示。

### 補題の説明

同じ率 3 の軌道の上の、基礎残差 \(F=\Phi_2\) の**厳密な時間の表示**です。

### 証明の概略

1. 軌道は箱に留まる。箱の上で \(F=2(x_0-x_1)^2\)。差が \(e^{-3(t-t_0)}\) 倍。二乗して \(e^{-6(t-t_0)}\)。

----

<a id="Tomabechi.Consistency.R3.sharedT4Residual_eq_explicit"></a>

## 補題 `sharedT4Residual_eq_explicit`

### 式

$$
\mathrm{residual}=\mathrm{sharedT4Explicit}(F_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実際の残差は、明示式に \(F_0=\Phi_2(x,0)\) を入れたものに一致します。

### 証明の概略

1. 残差 \(=\) 実効評価、実効評価の式 \(1+F-e^{-F}\)、\(F\) の時間表示（前の補題）。

----

<a id="Tomabechi.Consistency.R3.sharedT4Explicit_hasDerivAt"></a>

## 補題 `sharedT4Explicit_hasDerivAt`

### 式

$$
\frac{d}{dt}\mathrm{explicit}=-6\,Fe^{-6(t-t_0)}\bigl(1+e^{-Fe^{-6(t-t_0)}}\bigr)
$$

### Lean のコメント（日本語訳）

> 明示残差へ連鎖律を適用する。

### 補題の説明

明示的な残差に、連鎖律を適用して、微分を求めます。

### 証明の概略

1. 指数の引数の微分、定数倍、\(\exp\) との合成、差の微分を組み合わせ、式を整理する。

----

<a id="Tomabechi.Consistency.R3.sharedT4Residual_ac"></a>

## 補題 `sharedT4Residual_ac`

### 式

$$
\text{残差は絶対連続}
$$

### Lean のコメント（日本語訳）

> 全有限前向き区間で実残差はAC。閉区間上の一致で明示式から移す。

### 補題の説明

すべての有限の前向きの区間で、実際の残差は絶対連続です。閉区間の上で明示式と一致することから移します。

### 証明の概略

1. 明示式は C¹（`fun_prop`）なので絶対連続。実残差は閉区間上で明示式と一致（前の補題）。

----

<a id="Tomabechi.Consistency.R3.sharedT4Residual_decay_ae"></a>

## 補題 `sharedT4Residual_decay_ae`

### 式

$$
\frac{d}{dt}\mathrm{residual}\le-3\,\mathrm{residual}\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 一般入口のa.e.散逸。開始点だけは零測度集合として除く。単なる値の減衰から微分不等式を推測していない。

### 補題の説明

一般の入口が要求する、ほとんど至る所の**散逸の不等式**です（開始点だけは測度 0 の集合として除きます）。単なる値の減衰から微分の不等式を推測してはいません。

### 証明の概略

1. 開始点以外の時刻で、近傍では実残差が明示式に一致するので、導関数も一致する。
2. 明示式の導関数（前の補題）と、実効評価の上界・下界（`commonBaseTheorem4_bounds`、`commonBaseTheorem4_rate3_dissipation_rhs_bound`）から \(-3\times\) 残差以下を示す。

----

<a id="Tomabechi.Consistency.R3.sharedT4PointTarget"></a>

## 定義 `sharedT4PointTarget`

### 式

$$
\mathrm{weightedTCZ}(K,\ V_0,P,Q,\kappa=1,\theta=0)
$$

### Lean のコメント（日本語訳）

> 共通基礎評価の閾値0目標を一点K内で選ぶ。

### 定義の説明

共通基礎評価の、閾値 0 の目標を、**一点 K の中で**選んだものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R3.sharedT4PointTarget_eq"></a>

## 補題 `sharedT4PointTarget_eq`

### 式

$$
\mathrm{Tgt}_4=K\cap\mathrm{sharedTCZ}
$$

### Lean のコメント（日本語訳）

> 新評価の一点目標は同じ一点Kの共有TCZと一致する。

### 補題の説明

新しい評価の一点の目標は、同じ一点 K の共有 TCZ（\(K\cap\mathrm{sharedTCZ}\)）に一致します。

### 証明の概略

1. K は箱に含まれる（`pointReachableClosure_subset_box`）。
2. 箱の中の加重 TCZ は共有 TCZ（`commonBaseTheorem4_weightedTCZ_eq_shared`）。両方向を示す。

----

<a id="Tomabechi.Consistency.R3.sharedT4PointTarget_error"></a>

## 補題 `sharedT4PointTarget_error`

### 式

$$
\operatorname{dist}(x(t),\mathrm{Tgt})^2\le1\cdot\mathrm{residual}
$$

### Lean のコメント（日本語訳）

> 同じ一点初期目標への全前向き時刻の誤差境界。集合包含による逆向き距離評価を使わず、合意点までの距離から証明する。

### 補題の説明

同じ一点の初期目標への、全前向きの時刻の**誤差境界**です。集合の包含による逆向きの距離評価を使わず、**合意点までの距離**から証明します。

### 証明の概略

1. 目標は合意点だけ（`pointSharedTCZ_eq_singleton`）。一点集合への距離は合意点までの距離。
2. 合意点までの距離は \(|d|e^{-3(t-t_0)}\) 以下（`consensusOptimalFlow_dist_agreementPoint_le`）。二乗は \(d^2e^{-6(t-t_0)}\)。
3. \(F_0=8d^2\)。実効評価は \(F\) 以上（`commonBaseTheorem4_bounds`）。\(d^2e^{-6}\le F\)。

----

<a id="Tomabechi.Consistency.R3.sharedBase_theorem4_point_entry"></a>

## 定理 `sharedBase_theorem4_point_entry`

### 式

$$
\operatorname{dist}(x(t),\mathrm{Tgt}_4)\le\sqrt{\mathrm{residual}(t_0)}\,e^{-\frac32(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> 定理4の一般入口を共有V₀・一点初期集合で実際に適用する。距離評価と極限の両方を得る。率は散逸から得る3/2。

### 補題の説明

定理4の一般の入口を、**共有の \(V_0\)・一点の初期集合**で実際に適用します。距離評価と極限の両方を得ます。率は、散逸の不等式から得る \(3/2\) です。

### 証明の概略

1. 到達（流れが一点 K に入る）、目標の非空性、残差の絶対連続性・散逸・誤差境界（前の補題）を、定理4の一般形（`weighted_reachable_tcz_distance_tendsto_zero`）に渡す。
2. 散逸の率 \(2c=3\)（\(c=3/2\)）、誤差境界の定数 1。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
