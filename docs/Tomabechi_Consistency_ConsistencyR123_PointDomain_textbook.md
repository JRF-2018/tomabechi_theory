# Tomabechi/Consistency/ConsistencyR123_PointDomain.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_PointDomain.lean`](../Tomabechi/Consistency/ConsistencyR123_PointDomain.lean)（一点 K の全状態に対する原文誤差境界）。
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
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

選んだ軌道の上だけでなく、**一点 \(K\) の全状態・全評価時刻**で、定理 1・2・3・4 の誤差の境界を証明するファイルです。同じ \(N\) の流れでの、**任意の再始動**に対する前向きの不変性も保ちます。\(K\) は、初期点 \(x\) からの**閉到達集合**で、具体的には一本の線分です。

### 0.2 このファイルが証明していないこと

* 定理 3 は、**零平均の初期点の \(K\)** に限ります。
* \(K\) は一点の初期状態から出る線分です。初期状態が集合の場合は別です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 選んだ軌道上だけでなく、K の全状態と全評価時刻で 1/2/3/4 の誤差を証明する。同じ N の flow での任意の再始動に対する前向き不変性も保持する。定理 3 は零平均初期点の K に限る。

---

<a id="Tomabechi.Consistency.R123.pointK_mean"></a>

## 補題 `pointK_mean`

### 式

$$
y\in K\ \Rightarrow\ \mathrm{mean}(y)=\mathrm{mean}(x)
$$

### Lean のコメント（日本語訳）

> K線分上では初期平均が保存される。零平均スライスも同じK全体で保つ。

### 補題の説明

一点 \(K\)（初期点 \(x\) からの閉到達集合）は線分で、その上では**初期の平均が保存**されます。したがって、零平均のスライスも、同じ \(K\) の全体で保たれます。

### 証明の概略

1. \(K\) が軌道の線分であること（`pointReachableClosure_eq_orbitSegment`）を使い、線分上の点 \(r\) で平均が初期値に等しいことを示す。

----

<a id="Tomabechi.Consistency.R123.pointK_error2"></a>

## 補題 `pointK_error2`

### 式

$$
\mathrm{dist}(y,\ \text{合意点})^2\le \mathrm{potential}(y,t)
$$

### Lean のコメント（日本語訳）

> 線分内の任意点の合意点への距離二乗は、その点の共有残差以下。

### 補題の説明

線分の内部の任意の点 \(y\) について、合意点への距離の二乗は、その点の**共有の残差**以下です。

### 証明の概略

1. 平均が保存されること（前の補題）と、箱に入っていること。
2. 合意点との距離が半差の絶対値以下であることを、座標ごとに調べる（`dist_pi_le_iff`）。これと残差の定義を比べる。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointK"></a>

## 補題 `SharedKernelInputs.pointK`

### 式

$$
(N.\mathrm{pointAdapter}\ x\ t_0).\mathrm{reachable}=K(x,t_0)
$$

### Lean のコメント（日本語訳）

> 同じNの実一点Kを具体線分へ同定する保存式。

### 補題の説明

同じ \(N\) の**実際の一点 \(K\)** を、具体的な線分に同定する保存の式です。

### 証明の概略

1. 到達集合の保存式（`point_reachable`）と、流れの保存式（`point_flow`）、選ばれた流れが率3の流れであること。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointTarget2"></a>

## 補題 `SharedKernelInputs.pointTarget2`

### 式

$$
\text{定理2の一点の目標}=\{\text{合意点}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中の初期点について、定理2の一点の目標が、合意点だけの集合に等しいです。

### 証明の概略

1. 定義を展開して \(K\) を具体線分で置き換える。
2. 共有 TCZ の集合が、一点のものと一致すること（集合の外延性）を、両方向で示す。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_error2"></a>

## 補題 `SharedKernelInputs.pointDomain_error2`

### 式

$$
\mathrm{infDist}(y,\ \text{目標})^2\le \mathrm{potential}(y,t)
$$

### Lean のコメント（日本語訳）

> 一点Kの全状態での原文定理2誤差。時刻tを軌道時刻に固定しない。

### 補題の説明

**一点 \(K\) の全状態**での、原文の定理 2 の誤差の境界です。時刻 \(t\) を軌道の時刻に固定せず、すべての時刻で成り立ちます。

### 証明の概略

1. 目標が合意点だけであること（`pointTarget2`）、\(K\) の具体化（`pointK`）で、`pointK_error2` に帰着する。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_error1"></a>

## 補題 `SharedKernelInputs.pointDomain_error1`

### 式

$$
\mathrm{infDist}(y,\ \text{目標})^2\le \mathrm{residual}_1(V_0(y,t),1)
$$

### Lean のコメント（日本語訳）

> 同じKの全状態での定理1誤差。基礎評価はN.baseそのもの。

### 補題の説明

同じ \(K\) の全状態での、定理 1 の誤差の境界です。基礎評価は `N.base` **そのもの**です。

### 証明の概略

1. 定理 1 の目標と定理 2 の目標が同じ（共有 TCZ）ことと、残差の比較。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_error4"></a>

## 補題 `SharedKernelInputs.pointDomain_error4`

### 式

$$
\mathrm{infDist}(y,\ \text{目標})^2\le \mathrm{residual}_4(\cdots)
$$

### Lean のコメント（日本語訳）

> 共有実効評価の零集合は同じKの共有TCZ。全K点で定理4誤差を得る。

### 補題の説明

共有の実効評価の零集合は、同じ \(K\) の共有 TCZ です。そこから、\(K\) の全点で、**定理 4 の誤差**を得ます。

### 証明の概略

1. `N.base.V0` が共有の `commonBaseV0` に等しいこと（`V0_eq_shared`）。
2. 定理 4 の目標が、定理 2 の目標に等しいこと。そのうえで定理 2 の誤差から比べる。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointTarget3"></a>

## 補題 `SharedKernelInputs.pointTarget3`

### 式

$$
\text{零平均のとき、定理3の目標}=\text{定理2の目標}
$$

### Lean のコメント（日本語訳）

> 零平均K全体で、完全Φ₃の目標と共有TCZの目標が一致する。

### 補題の説明

**零平均の \(K\)** の全体で、完全な \(\Phi_3\) の目標と、共有 TCZ の目標が一致します。

### 証明の概略

1. 定理 2 の目標が合意点だけであること。
2. 定理 3 の目標が、零平均の箱の点で一点集合になること（`pointTheorem3Target_eq_singleton`）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_error3"></a>

## 補題 `SharedKernelInputs.pointDomain_error3`

### 式

$$
\mathrm{infDist}(y,\ \text{目標})^2\le \Phi_3(y,t)
$$

### Lean のコメント（日本語訳）

> 完全Φ₃を使った全K点の誤差。Φ₂だけを完全残差と呼ばない。

### 補題の説明

**完全な \(\Phi_3\)** を使った、\(K\) の全点での誤差です。\(\Phi_2\) だけを「完全な残差」とは呼びません。

### 証明の概略

1. 目標の一致（前の補題）で定理 2 の誤差に帰着し、\(\Phi_3\) が \(\Phi_2\) に非負の項を足したものであることから比べる。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_distance20"></a>

## 補題 `SharedKernelInputs.pointDomain_distance20`

### 式

$$
\mathrm{infDist}(y,\ \text{一点制限目標})=\mathrm{infDist}(y,\ \text{全域象徴目標})
$$

### Lean のコメント（日本語訳）

> K内の全点で、一点制限目標距離と全域象徴目標距離が一致する。

### 補題の説明

\(K\) の内部の全点で、**一点に制限した目標への距離**と、**全域の象徴の目標への距離**が一致します。

### 証明の概略

1. 平均が保存されること、合意点が同じであること。
2. 距離の座標を取り替えて、同じ式を比べる。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_error20"></a>

## 補題 `SharedKernelInputs.pointDomain_error20`

### 式

$$
\mathrm{infDist}(y,\ \text{全域象徴目標})\le C\ \cdots
$$

### Lean のコメント（日本語訳）

> 同じ一点K全体で、原文20の全域誤差定数をそのまま使用できる。

### 補題の説明

同じ \(K\) の全体で、原文の定理 20 の**全域の誤差の定数**を、そのまま使えます。

### 証明の概略

1. 前の補題（距離の一致）と、定理 20 の全域の誤差（共通の入口）の合成。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_invariant"></a>

## 補題 `SharedKernelInputs.pointDomain_invariant`

### 式

$$
y\in K\ \Rightarrow\ \varphi_{s,t}(y)\in K\ (s\le t)
$$

### Lean のコメント（日本語訳）

> 同じNの一点Kは、任意の内部状態・任意再始動時刻で前向き不変。

### 補題の説明

同じ \(N\) の一点 \(K\) は、任意の内部の状態・任意の再始動の時刻で、**前向きに不変**です。

### 証明の概略

1. \(K\) の具体化（`pointK`）と、線分の前向き不変性。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointFlow_same"></a>

## 補題 `SharedKernelInputs.pointFlow_same`

### 式

$$
(N.\mathrm{pointAdapter}\ y\ s).\mathrm{flow}=(N.\mathrm{pointAdapter}\ x\ t_0).\mathrm{flow}
$$

### Lean のコメント（日本語訳）

> 全一点adapterのflowは同じ保存された選択flowである。初期集合と到達Kを変えても、再始動の動力学を別のflowへ置き換えない。

### 補題の説明

どの一点アダプターの流れも、**同じ保存された選択の流れ**です。初期集合と到達集合 \(K\) を変えても、再始動の動力学を、別の流れに置き換えることはしません。

### 証明の概略

1. 流れの保存式（`point_flow`）を両辺に使う。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_restart2"></a>

## 補題 `SharedKernelInputs.pointDomain_restart2`

### 式

$$
\text{AC}\ \wedge\ \tfrac{d}{dr}\Phi_2\le -6\,\Phi_2\ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> K内部の任意点・非負再始動時刻の全有限区間で定理2のACと率6散逸。

### 補題の説明

\(K\) の内部の任意の点・非負の再始動の時刻の、すべての有限区間で、定理 2 の**絶対連続性と、率 6 の散逸**が成り立ちます。

### 証明の概略

1. \(K\) の点は箱の中にある（`pointReachableClosure_subset_box`）。
2. 同じ \(N\) の定理 2 の入力（`theorem2Inputs`）を、再始動の点 \(y\)・時刻 \(s\) で適用する。
3. ポテンシャルの定義の同一視で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_restart1"></a>

## 補題 `SharedKernelInputs.pointDomain_restart1`

### 式

$$
\text{AC}\ \wedge\ \tfrac{d}{dr}\mathrm{residual}_1\le -6\,\mathrm{residual}_1\ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 同じ共有基礎評価を使う定理1のAC・率6散逸も全K内部再始動で成立。

### 補題の説明

同じ共有の基礎評価を使う定理 1 の、**絶対連続性と率 6 の散逸**も、\(K\) 内部の全再始動で成り立ちます。

### 証明の概略

1. 前の補題と同じ手順。定理 1 の入力（`theorem1Inputs`）を使う。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_restart3"></a>

## 補題 `SharedKernelInputs.pointDomain_restart3`

### 式

$$
\text{AC}\ \wedge\ \tfrac{d}{dr}\Phi_3\le -6\,\Phi_3\ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 零平均Kの任意点から、完全Φ₃のAC・散逸条件を再始動する。

### 補題の説明

**零平均の \(K\)** の任意の点から、完全な \(\Phi_3\) の絶対連続性・散逸の条件が、再始動できます。

### 証明の概略

1. \(K\) の平均の保存で、再始動の点も零平均。
2. 定理 3 の入力を適用する。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.pointDomain_restart4"></a>

## 補題 `SharedKernelInputs.pointDomain_restart4`

### 式

$$
\text{AC}\ \wedge\ \tfrac{d}{dr}R\le -3\,R\ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 同じ実効評価の定理4も、K内部の任意点から率3の残差散逸で再始動する。

### 補題の説明

同じ実効評価の**定理 4**も、\(K\) の内部の任意の点から、**率 3 の残差の散逸**で再始動します。

### 証明の概略

1. \(K\) の点は箱の中。定理 4 の入力を適用し、残差の式を書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedPointDomainInputs"></a>

## 構造体 `SharedPointDomainInputs`

### 式

$$
\text{閉・不変・誤差}_{1,2,3,4,20}
$$

### Lean のコメント（日本語訳）

> 全K点の誤差と不変性を同じ署名の受入に追加する。再始動解析条件は同じ受入のSharedKernelInputsから上の一般量化補題で得る。

### 定義の説明

全 \(K\) 点の誤差と不変性を、同じ署名の受入に追加する構造体です（`SharedFullExperimentInputs` を拡張）。フィールドは、\(K\) の閉性、前向きの不変性、定理 1・2・3・4・20 の誤差の境界、です。再始動の解析条件は、同じ受入の `SharedKernelInputs` から、上の一般の量化補題で得ます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_pointDomainInputs"></a>

## 定理 `sharedModel_pointDomainInputs`

### 式

$$
\mathrm{SharedPointDomainInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、一点 \(K\) の全域の入力を満たします。

### 証明の概略

1. 閉性は、到達集合が閉包であること。不変性・各誤差は、上の補題。

----

<a id="Tomabechi.Consistency.R123.shared_point_domain_model_exists"></a>

## 定理 `shared_point_domain_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedPointDomainInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一点 \(K\) の全域の入力を満たす共有署名が存在します。

### 証明の概略

1. `sharedModel` を取る。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
