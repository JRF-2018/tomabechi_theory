# Tomabechi/Consistency/ConsistencyR123_CurrentPremises.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_CurrentPremises.lean`](../Tomabechi/Consistency/ConsistencyR123_CurrentPremises.lean)（現行評価 commonV0X に対する原文前件）。
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
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**現行の評価 \(V_0^X=1+2(x_0-x_1)^2\) に対する、原文の前件**を述べるファイルです。これまでの `SharedR3Inputs.theorem4_argmin` / `theorem20_argmin` と旧 `error1/2/3/4` は、旧い `N.base.V0`（\(1+\)`DA.potential`、箱 \(|x_i|\le1/4\)）に結ばれていました。以前に、結論の側は \(V_0^X\)（\(\mathbb R^2\) 全域）へ移しましたが、**原文の前件**（反復地平の費用の最適性、補題 0 の「\(K\) の全点・全時刻」の誤差境界、「任意の内部点・任意の非負開始時刻からの再始動」の絶対連続性・散逸）は、現行評価について型に入っていませんでした。

ここでは、旧い `N.base.V0` を変更せず（\(x=(1,1)\) で、旧い値 \(14/5\ne\)新しい値 \(1\) なので、同一視は不可能）、現行評価について次を証明して、`FullOriginalPremisesCurrent N` にまとめます。

* **有限地平の argmin**（定理 1・4・20）：選択ゲイン（定数 3）が、\(N\) の実際の軌道・全競合の可測ゲインに対して \(\int\mathrm{ofReal}(V)\) を最小化する。\(V=V_0^X\)／実効評価／\(V_0^X-\mathrm{slope}\)。箱の仮定なし、\(\mathbb R^2\) 全域。
* **補題 0（\(K\) の全点・再始動）**（定理 1・2・3・4）：\(K\) の**全点** \(y\) で \(\mathrm{dist}(y,\mathrm{TCZ})^2\le C\cdot\Phi(y)\)（\(C=1\)）、\(K\) は前向き不変、\(\Phi\ge0\)、目標は非空。さらに、\(K\) の**任意の点 \(y\)・任意の非負開始時刻 \(s\)** から出発した共有の流れに沿って、\(\Phi\) は絶対連続で、ほとんど至る所で \(D^+\Phi\le-\mathrm{rate}\cdot\Phi\)（定理 1・2・3 は率 6、定理 4 は率 3）。再始動の目標は、元の \(K\) の上の同じ目標集合（\(K\) を固定したまま）。

### 0.2 このファイルが証明していないこと

* 定理 1・4・20 は \(\mathbb R^2\) 全域、定理 2 は \(X_3\)、定理 3 は \(X_1\) の零平均の点です（目標集合が空でなくなる初期点は、このモデルでは零平均の点に限ります）。
* 定理 24 の割引つき無限地平の最適性とは区別した、**有限地平の費用の比較**です。
* 誤差の距離は、状態の sup 距離（`AgentState = Fin 2 → ℝ`）です。
* 旧い `N.base` は補助のフィールドのまま残り、ここでは現行評価の前件だけを述べます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> これまでの SharedR3Inputs.theorem4_argmin / theorem20_argmin と旧 error1/2/3/4 は、旧 N.base.V0（1 + DA.potential、箱 |x_i| ≤ 1/4）に結ばれていた。以前に結論側は commonV0X = 1 + 2(x₀−x₁)²（ℝ² 全域）へ移したが、原文の前件（反復地平の費用最適性、補題0の「K の全点・全時刻」の誤差境界、「任意の内部点・任意の非負開始時刻からの再始動」の絶対連続性・散逸）は現行評価について型に入っていなかった。ここでは旧 N.base.V0 を変更せず（…x=![1,1] で旧 14/5 ≠ 新 1 なので、同一視は不可能）、現行評価について次を証明して FullOriginalPremisesCurrent N にまとめる。…（以下、上の二点と範囲）。

---

<a id="Tomabechi.Consistency.R123.Fg_eq_two_D"></a>

## 補題 `Fg_eq_two_D`

### 式

$$
F(y)=2\,D(y)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差 \(F\) は、半差の二乗 \(D\) の 2 倍です。

### 証明の概略

1. \(F=2(y_0-y_1)^2\) と、\(D\) の定義。

----

<a id="Tomabechi.Consistency.R123.commonBaseD_maxGain_le"></a>

## 補題 `commonBaseD_maxGain_le`

### 式

$$
D(\text{最大ゲインの閉ループ})\le D(\text{任意の可測ゲインの閉ループ})
$$

### Lean のコメント（日本語訳）

> 最大ゲインの閉ループの半差の二乗は、任意の可測ゲインのそれ以下。

### 補題の説明

最大ゲインの閉ループの半差の二乗は、任意の可測ゲインのそれ以下です。

### 証明の概略

1. 最大ゲインの軌道の二乗の比較（`c1MaxGain_orbit_sq_le`）と、最大ゲインの軌道が \(h\,e^{-3(s-t_0)}\) であること。

----

<a id="Tomabechi.Consistency.R123.eff20X"></a>

## 定義 `eff20X`

### 式

$$
\tilde V_{20}=V_0^X-\kappa\cdot\mathrm{slope}\ \ (\kappa=1,\ \mathrm{slope}=-D)
$$

### Lean のコメント（日本語訳）

> 定理20の現行実効評価：commonV0X−κ·slope（κ=1、slope=−D）。

### 定義の説明

定理 20 の現行の**実効評価**です。\(V_0^X-\kappa\cdot\mathrm{slope}\)（\(\kappa=1\)、slope \(=-D\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.eff20X_eq"></a>

## 補題 `eff20X_eq`

### 式

$$
\tilde V_{20}=1+3D
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 20 の実効評価は、\(1+3D\) です。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.currentCost"></a>

## 定義 `SharedModelSignature.currentCost`

### 式

$$
\int_{t_0}^{t_0+T}V(\text{実軌道}(s))\,ds
$$

### Lean のコメント（日本語訳）

> 同じNの実軌道（正有限層・可測ゲイン）でVを積分した有限地平費用。

### 定義の説明

同じ \(N\) の実際の軌道（正の有限層・可測ゲイン）で、\(V\) を積分した、**有限地平の費用**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.currentCost_eq"></a>

## 補題 `SharedKernelInputs.currentCost_eq`

### 式

$$
\text{実軌道での費用}=\text{閉ループの軌道での費用}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実際の軌道での費用は、閉ループの軌道（`controlledConsensusState`）での費用に等しいです。

### 証明の概略

1. 軌道の保存式（`finite_trajectory`）で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.currentArgmin_of_monotone"></a>

## 補題 `SharedKernelInputs.currentArgmin_of_monotone`

### 式

$$
V\text{ が }D\text{ の単調関数}\Rightarrow\text{最大ゲインが有限地平費用を最小化}
$$

### Lean のコメント（日本語訳）

> 残差がDの単調関数なら、最大ゲインが有限地平費用を最小化する（箱の仮定なし）。

### 補題の説明

残差が \(D\) の**単調関数**なら、最大ゲインが有限地平費用を最小化します（箱の仮定なし）。

### 証明の概略

1. 選択ゲインが最大ゲインであること（`selectedGain_eq_maximum`）。各時刻で、最大ゲインの閉ループの \(D\) が最小（`commonBaseD_maxGain_le`）なので、\(V\) の単調性から被積分関数が小さく、積分も小さい（`lintegral_mono_ae`）。

----

<a id="Tomabechi.Consistency.R123.commonV0X_mono_D"></a>

## 補題 `commonV0X_mono_D`

### 式

$$
D(a)\le D(b)\Rightarrow V_0^X(a)\le V_0^X(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全域の共有評価は、\(D\) の単調関数です。

### 証明の概略

1. \(F=2D\)。

----

<a id="Tomabechi.Consistency.R123.effX_mono_D"></a>

## 補題 `effX_mono_D`

### 式

$$
D(a)\le D(b)\Rightarrow\tilde V(a)\le\tilde V(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 4 の実効評価は、\(D\) の単調関数です。

### 証明の概略

1. \(F\) の単調性と、定理 4 の実効評価の単調性の補題（`commonBaseTheorem4Effective_monotone`）。

----

<a id="Tomabechi.Consistency.R123.eff20X_mono_D"></a>

## 補題 `eff20X_mono_D`

### 式

$$
D(a)\le D(b)\Rightarrow\tilde V_{20}(a)\le\tilde V_{20}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 20 の実効評価は、\(D\) の単調関数です。

### 証明の概略

1. \(\tilde V_{20}=1+3D\)。

----

<a id="Tomabechi.Consistency.R123.agreementPoint_segmentPoint"></a>

## 補題 `agreementPoint_segmentPoint`

### 式

$$
\text{線分上の点：平均は保存}
$$

### Lean のコメント（日本語訳）

> 線分上の点：平均は保存、座標はmean ± h·r。

### 補題の説明

線分上の点では、**平均は保存**されます（座標は \(\mathrm{mean}\pm h\cdot r\)）。

### 証明の概略

1. 定義を展開。

----

<a id="Tomabechi.Consistency.R123.Fg_segmentPoint"></a>

## 補題 `Fg_segmentPoint`

### 式

$$
F(\mathrm{seg}(x,r))=8(h\,r)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

線分上の点での共有残差は、\(8(h\,r)^2\) です（\(h\) は半差）。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.dist_segmentPoint_agreement_sq_le"></a>

## 補題 `dist_segmentPoint_agreement_sq_le`

### 式

$$
\mathrm{dist}(\mathrm{seg}(x,r),\text{合意点})^2\le F(\mathrm{seg}(x,r))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

線分上の点の、合意点への距離の二乗は、その点の共有残差以下です。

### 証明の概略

1. 距離が \(|h\,r|\) 以下（座標ごとに計算）。二乗して、\(F=8(hr)^2\) と比べる。

----

<a id="Tomabechi.Consistency.R123.mem_K_segment"></a>

## 補題 `mem_K_segment`

### 式

$$
y\in K\Rightarrow\exists r\in[0,1],\ y=\mathrm{seg}(x,r)
$$

### Lean のコメント（日本語訳）

> Kの点は線分上の点。

### 補題の説明

一点 \(K\) の点は、線分上の点です。

### 証明の概略

1. \(K\) が軌道の線分であること。

----

<a id="Tomabechi.Consistency.R123.segmentPoint_bound"></a>

## 補題 `segmentPoint_bound`

### 式

$$
|x_i|\le B\Rightarrow|\mathrm{seg}(x,r)_i|\le B
$$

### Lean のコメント（日本語訳）

> 座標の大きさの一様な上界は線分上でも保たれる。

### 補題の説明

座標の大きさの一様な上界は、線分の上でも保たれます。

### 証明の概略

1. 線分の点は、両端の凸結合。座標ごとに評価。

----

<a id="Tomabechi.Consistency.R123.Fexp_restart"></a>

## 補題 `Fexp_restart`

### 式

$$
\Psi=Ge^{-6(r-s)}\Rightarrow\text{AC}\wedge\Psi'\le-6\Psi
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

率 6 の指数に従う関数は、絶対連続で、ほとんど至る所 \(\Psi'\le-6\Psi\) を満たします。

### 証明の概略

1. 指数関数の絶対連続性（`Fexp_ac`）と、導関数の式（`hasDerivAt_Fexp`）。

----

<a id="Tomabechi.Consistency.R123.T4_restart"></a>

## 補題 `T4_restart`

### 式

$$
\text{定理 4 の明示式は絶対連続で }\Psi'\le-3\Psi
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 4 の明示式は、絶対連続で、ほとんど至る所 \(\Psi'\le-3\Psi\) を満たします。

### 証明の概略

1. 明示式が \(C^1\)（`fun_prop`）で絶対連続。導関数の評価は、明示式を微分して比べる。

----

<a id="Tomabechi.Consistency.R123.instance@L192"></a>

## インスタンス `instance@L192`

### 式

$$
\text{定理 3 の抽象系の各状態は擬距離空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 3 の抽象系の各状態が擬距離空間であるという局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L196"></a>

## インスタンス `instance@L196`

### 式

$$
\text{抽象系の状態の積はノルム付き可換群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象系の状態の積が、ノルム付きの可換群であるという局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L200"></a>

## インスタンス `instance@L200`

### 式

$$
\text{抽象系の状態の積は実ノルム空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象系の状態の積が、実ノルム空間であるという局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.RestartLemma0"></a>

## 構造体 `RestartLemma0`

### 式

$$
\text{原文補題 0 の前件：K の全点・任意の再始動}
$$

### Lean のコメント（日本語訳）

> 原文補題0の前件：定義域Dの初期点x、全非負開始時刻t₀について、K（pointReachableClosure）が前向き不変・Φ≥0・目標が非空、Kの全点でdist(y,TCZ)²≤1·Φ(y)、Kの任意の点y・任意の非負開始時刻sから出発した共有flowに沿ってΦが絶対連続でa.e.にD⁺Φ≤−rate·Φ。目標集合は元のK上の同じTgt x t₀。

### 定義の説明

**原文の補題 0 の前件**です。定義域 \(D\) の初期点 \(x\)、全非負開始時刻 \(t_0\) について、(1) \(K\)（`pointReachableClosure`）が前向き不変、(2) \(\Phi\ge0\)、(3) 目標が非空、(4) \(K\) の**全点**で \(\mathrm{dist}(y,\mathrm{TCZ})^2\le1\cdot\Phi(y)\)、(5) \(K\) の**任意の点 \(y\)・任意の非負開始時刻 \(s\)** から出発した共有の流れに沿って、\(\Phi\) が絶対連続で、ほとんど至る所で \(D^+\Phi\le-\mathrm{rate}\cdot\Phi\)、です。目標集合は、元の \(K\) の上の同じ目標です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.phi1X"></a>

## 定義 `phi1X`

### 式

$$
\Phi_1(y)=[V_0^X(y)-1]_+
$$

### Lean のコメント（日本語訳）

> 定理1の残差[V₀−1]₊（V₀=commonV0X）。

### 定義の説明

定理 1 の残差 \([V_0-1]_+\) です（\(V_0=V_0^X\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.phi1X_eq"></a>

## 補題 `phi1X_eq`

### 式

$$
\Phi_1=F
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 1 の残差は、共有残差 \(F\) に等しいです。

### 証明の概略

1. `residual1_commonV0X`。

----

<a id="Tomabechi.Consistency.R123.phi4X"></a>

## 定義 `phi4X`

### 式

$$
\Phi_4(y)=\mathrm{residual}_4(V_0^X,\ e^{-F},\ 1,\ 1,\ 0)
$$

### Lean のコメント（日本語訳）

> 定理4の実効残差（P=exp(−F)、Q=1、κ=1、閾値0）。

### 定義の説明

定理 4 の実効残差です（\(P=\exp(-F)\)、\(Q=1\)、\(\kappa=1\)、閾値 0）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.phi4X_eq"></a>

## 補題 `phi4X_eq`

### 式

$$
\Phi_4=\tilde V
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 4 の実効残差は、実効評価 \(\tilde V\) に等しいです。

### 証明の概略

1. `residual4_X`。

----

<a id="Tomabechi.Consistency.R123.target1X"></a>

## 定義 `target1X`

### 式

$$
\text{定理 1 の目標（時刻によらない）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 1 の目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.target4X"></a>

## 定義 `target4X`

### 式

$$
\text{定理 4 の目標（時刻によらない）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 4 の目標集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.target2X"></a>

## 定義 `target2X`

### 式

$$
\text{定理 2 の目標（DX の共有 TCZ）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 2 の目標集合です（`DX` の共有 TCZ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.target3X"></a>

## 定義 `target3X`

### 式

$$
\text{定理 3 の目標（状態の TCZ）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 3 の目標集合です（状態の TCZ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.domain3"></a>

## 定義 `domain3`

### 式

$$
X_1\cap\{x_0+x_1=0\}
$$

### Lean のコメント（日本語訳）

> 定理3の定義域：X1の零平均点。

### 定義の説明

定理 3 の定義域です。\(X_1\) の零平均の点。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.restartLemma0_theorem1"></a>

## 定理 `restartLemma0_theorem1`

### 式

$$
\text{補題 0（定理 1、率 6）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 1 について、補題 0 の前件が成り立ちます（率 6、全域）。

### 証明の概略

1. 前向き不変性は一点 \(K\) の補題。非負性は `Fg_nonneg`。目標は合意点。\(K\) の全点の誤差は、線分上の点の補題（`dist_segmentPoint_agreement_sq_le`）。再始動の絶対連続性・散逸は、`Fexp_restart` と、共有の流れの減衰（`Fg_flow`）。

----

<a id="Tomabechi.Consistency.R123.restartLemma0_theorem4"></a>

## 定理 `restartLemma0_theorem4`

### 式

$$
\text{補題 0（定理 4、率 3）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 4 について、補題 0 の前件が成り立ちます（率 3、全域）。

### 証明の概略

1. 定理 1 と同様。再始動の散逸は、`T4_restart`（定理 4 の明示式）。

----

<a id="Tomabechi.Consistency.R123.K_subset_X3"></a>

## 補題 `K_subset_X3`

### 式

$$
x\in X_3\Rightarrow K\subset X_3
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(X_3\) の初期点の \(K\) は、\(X_3\) に含まれます。

### 証明の概略

1. `mem_K_segment` と `segmentPoint_bound`。

----

<a id="Tomabechi.Consistency.R123.K_subset_X1"></a>

## 補題 `K_subset_X1`

### 式

$$
x\in X_1\Rightarrow K\subset X_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(X_1\) の初期点の \(K\) は、\(X_1\) に含まれます。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Consistency.R123.K_zero_mean"></a>

## 補題 `K_zero_mean`

### 式

$$
\text{零平均}\Rightarrow K\text{ の全点が零平均}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零平均の初期点の \(K\) の全点は、零平均です（平均が保存されるため）。

### 証明の概略

1. 線分上の点の座標を展開して `linarith`。

----

<a id="Tomabechi.Consistency.R123.restartLemma0_theorem2"></a>

## 定理 `restartLemma0_theorem2`

### 式

$$
\text{補題 0（定理 2、率 6、}X_3\text{）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 2 について、補題 0 の前件が成り立ちます（率 6、\(X_3\) 上）。

### 証明の概略

1. `DX` のポテンシャルが \(X_3\) の上で \(V_0^X-1\)（`DX_potential_eq_on_X3`）。\(K\subset X_3\)（`K_subset_X3`）。その他は定理 1 と同様。

----

<a id="Tomabechi.Consistency.R123.restartLemma0_theorem3"></a>

## 定理 `restartLemma0_theorem3`

### 式

$$
\text{補題 0（定理 3、率 6、}X_1\text{ の零平均点）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 3 について、補題 0 の前件が成り立ちます（率 6、\(X_1\) の零平均の点）。

### 証明の概略

1. \(K\subset X_1\)・零平均（`K_subset_X1`・`K_zero_mean`）。非負性は `phi3X_nonneg`、目標は合意点、再始動の散逸は `phi3X_flow` から。

----

<a id="Tomabechi.Consistency.R123.theorem3_target_nonempty_iff_zero_mean"></a>

## 補題 `theorem3_target_nonempty_iff_zero_mean`

### 式

$$
x\in X_1:\ \text{目標が非空}\iff x_0+x_1=0
$$

### Lean のコメント（日本語訳）

> 定理3の目標集合が非空になるX1の初期点は、ちょうど零平均点（このモデルでの帰結で、原文の仮定ではない）。

### 補題の説明

定理 3 の目標集合が空でなくなる \(X_1\) の初期点は、ちょうど**零平均の点**です（このモデルでの帰結で、原文の仮定ではありません）。

### 証明の概略

1. \(\Rightarrow\)：目標の点 \(y\) が \(K\) に入り、\(\Phi_3(y)=0\)、明示式から \(y_0=y_1=0\)。平均が保存されるので、\(x_0+x_1=0\)。\(\Leftarrow\)：合意点が目標に入る。

----

<a id="Tomabechi.Consistency.R123.FullOriginalPremisesCurrent"></a>

## 構造体 `FullOriginalPremisesCurrent`

### 式

$$
\text{現行評価 }V_0^X\text{ について、原文の前件（argmin・補題 0）}
$$

### Lean のコメント（日本語訳）

> 現行評価commonV0Xについて、原文の前件（有限地平argmin、補題0のK全点・再始動）を同じNで述べた受入型。旧N.baseは補助fieldのままで、ここでは使わない。

### 定義の説明

現行評価 \(V_0^X\) について、**原文の前件**（有限地平の argmin、補題 0 の \(K\) 全点・再始動）を、同じ \(N\) で述べた受入の型です。旧い `N.base` は補助のフィールドのままで、ここでは使いません。フィールドは、\(N\) の流れ・到達集合が共有の流れ・一点 \(K\)（全初期点）、選択ゲインが最大ゲイン、\(V_0^X\ge0\)、\(V_0^X\) が有限層の実走行費、定理 1・4・20 の有限地平 argmin、定理 1・2・3・4 の補題 0、定理 3 の目標が空でない、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_fullOriginalPremisesCurrent"></a>

## 定理 `sharedModel_fullOriginalPremisesCurrent`

### 式

$$
\mathrm{FullOriginalPremisesCurrent}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、現行評価の原文の前件を満たします。

### 証明の概略

1. アダプター・選択ゲインは前のファイルの補題。argmin は `currentArgmin_of_monotone` に、各評価の単調性（`commonV0X_mono_D`・`effX_mono_D`・`eff20X_mono_D`）を渡す。補題 0 は、上の四つの定理。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_current_premises"></a>

## 定理 `final_consistency_with_current_premises`

### 式

$$
\exists N,\mathrm{sig},\ \cdots\wedge\mathrm{FullOriginalPremisesCurrent}(N)
$$

### Lean のコメント（日本語訳）

> 現行評価の原文前件を、最終整合（v11のSharedFinalConsistency・層制御系・担体全体の自己過程）と同じNで。

### 補題の説明

現行評価の原文の前件を、最終の整合（第 11 版の `SharedFinalConsistency`・層の制御系・担体全体の自己過程）と**同じ \(N\) で**述べる存在宣言です。

### 証明の概略

1. `sharedModel`、速度制御の署名、各部品の定理を組み合わせる。

----


## コメント修正記録

冒頭コメントにあった存在しない名前 `audit_base_differs_inside_X3` を、実在する `SharedCommonDomainX` の `base_ne_outside_box` に直しました（コメントのみ）。
