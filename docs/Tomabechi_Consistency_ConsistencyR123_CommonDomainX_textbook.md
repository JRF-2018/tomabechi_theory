# Tomabechi/Consistency/ConsistencyR123_CommonDomainX.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_CommonDomainX.lean`](../Tomabechi/Consistency/ConsistencyR123_CommonDomainX.lean)（共通状態領域 X の部分的な統合）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**共通の状態領域 \(X\) の部分的な統合**のファイルです。

**問題：** `SharedBaseDomain` は \(X:=\mathrm{box}\)（各座標の絶対値 \(\le1/4\)）を採りますが、`sharedModel.stages 0` の中心は座標 \(1/(2\sqrt2)>1/4\) で箱の外にあり、原文 §11 の \(U_n\subset X\) が、共通の箱では成り立ちません。

**観察：** 有限層の実走行費（定理 24）は \(1+8(\text{半差})^2=1+2(x_0-x_1)^2\) で、**全域で**この二次式です。定理 20 の拡張 \(1+8\cdot\mathrm{symbolDistance}\) も、全域で同じ二次式です。箱でだけ一致が要るのは、定理 1・2・4 の `N.base.V0` \(=1+\) 定理 2 の `potential`（個人の閾値の残差 \([(x_i)^2-\theta]_+\)、\(\theta=1/10\) を含む）だけです。

**ここで証明すること：** 明示的な共通の領域 \(X:=\mathbb R^2\)（Euclid 平面の全体）と、全域の共有評価 \(V_0^X(x):=1+2(x_0-x_1)^2\) を置き、

1. \(V_0^X\) は、定理 20 の拡張・有限層 24 の実走行費（共通束の層を通しても）と**全域で一致**する。
2. \(V_0^X\) は全域で滑らかで、勾配場 \(G(z)=H(z)\)（\(\|G(z)\|\le8\|z\|\)）、\(\nabla^2\succeq0\)（\(\beta=0\)）。
3. すべての実際の段 `sharedModel.stages n` の閉球 \(U_n\) は \(\bar B_3(0)\) に含まれ、したがって \(X\) に含まれる。各 \(U_n\) の上で、\(V_0^X\) は (21.3) の型の条件（\(C^2\)・\(\|\nabla V_0\|\le24\)・\(\nabla^2V_0\succeq0\)）を満たす。
4. `N.base.V0` は箱の上で \(V_0^X\) に一致し、定理 1・2・4 の一点到達集合は箱の中に留まる。
5. 箱の外では、`N.base.V0` と \(V_0^X\) が異なる（記録）。

### 0.2 このファイルが証明していないこと

* 定理 1・2・4 を、箱の外の初期点を含む \(X\) の全体で、\(V_0^X\) について述べ直すこと。これらは、定理 2 の個人の閾値の残差を含む `DA`（\(\theta=1/10\) 固定）に結んで構成されており、箱の外では \(\Phi_2\ne V_0^X-1\) です。\(\theta\) を大きく取り直した並列の `DA`、共有基礎契約・入口・受入の型の再構成が要り、既存の宣言を変えない方針では、本ファイルの範囲を超えます。
* したがって、「同じ \(V_0\) が 1/4/20/24 で \(X\) の全体で一致する」とは主張しません（20 と 24 については全域で一致、1・2・4 は箱の上でだけ）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 問題：SharedBaseDomain は X := box（各座標の絶対値 ≤ 1/4）を採るが、sharedModel.stages 0 の中心は座標 1/(2√2) > 1/4 で箱の外にあり、§11 の U_n ⊂ X が共通箱では成り立たない。観察：有限層の実走行費（定理24）は 1 + 8(halfDifference x)² = 1 + 2(x₀−x₁)² で、全域でこの二次式であり、定理20の拡張 1 + 8·symbolDistance も全域で同じ二次式である。箱でだけ一致が要るのは、定理1・2・4の N.base.V0 = 1 + DA.potential（…θ = 1/10 を含む）だけである。ここで証明すること：…（上の五点）。証明していないこと：…（上の二点）。

---

<a id="Tomabechi.Consistency.R123.commonDomainX"></a>

## 定義 `commonDomainX`

### 式

$$
X=\mathbb R^2
$$

### Lean のコメント（日本語訳）

> 共通状態領域X：Euclid平面全体（座標写像はc1EuclideanCoordinates）。

### 定義の説明

**共通の状態領域** \(X\) です。Euclid 平面の全体（座標写像は `c1EuclideanCoordinates`）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.stageHull"></a>

## 定義 `stageHull`

### 式

$$
\bar B_3(0)
$$

### Lean のコメント（日本語訳）

> 段の閉球をすべて含む有界な部分領域。

### 定義の説明

段の閉球をすべて含む、有界な部分領域 \(\bar B_3(0)\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.commonV0X"></a>

## 定義 `commonV0X`

### 式

$$
V_0^X(x)=1+2(x_0-x_1)^2
$$

### Lean のコメント（日本語訳）

> 全域の共有評価。

### 定義の説明

**全域の共有評価** \(V_0^X(x)=1+2(x_0-x_1)^2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.commonV0XE"></a>

## 定義 `commonV0XE`

### 式

$$
V_0^X(\mathrm{coords}(z))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

全域の共有評価の、Euclid 座標での表示です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.commonV0X_eq_halfDifference"></a>

## 補題 `commonV0X_eq_halfDifference`

### 式

$$
V_0^X(x)=1+8\,(\text{半差})^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全域の共有評価は、半差の二乗の 8 倍に 1 を足したものです。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.commonV0XE_eq_theorem20_extension"></a>

## 補題 `commonV0XE_eq_theorem20_extension`

### 式

$$
V_0^X=\text{定理 20 の拡張}
$$

### Lean のコメント（日本語訳）

> 定理20の拡張と全域で一致。

### 補題の説明

全域の共有評価は、定理 20 の拡張と、**全域で一致**します。

### 証明の概略

1. 象徴の距離の座標表示を展開して `ring`。

----

<a id="Tomabechi.Consistency.R123.sharedModel_finiteCost_eq_commonV0X"></a>

## 補題 `sharedModel_finiteCost_eq_commonV0X`

### 式

$$
\text{有限層の実走行費}=V_0^X
$$

### Lean のコメント（日本語訳）

> 有限層の実走行費（定理24）は全域でcommonV0X。

### 補題の説明

有限層の実走行費（定理 24）は、**全域で** \(V_0^X\) に等しいです。

### 証明の概略

1. 費用の定義を展開し、`commonV0X_eq_halfDifference`。

----

<a id="Tomabechi.Consistency.R123.sharedModel_commonLayerCost_eq_commonV0X"></a>

## 補題 `sharedModel_commonLayerCost_eq_commonV0X`

### 式

$$
\text{共通束の層 }\mathrm{index}_{16}(i)\text{ を通しても、実走行費}=V_0^X
$$

### Lean のコメント（日本語訳）

> 共通束の層index16 iを通しても、実走行費は全域でcommonV0X。

### 補題の説明

共通束の層 `index16 i` を通しても、実走行費は、全域で \(V_0^X\) です。

### 証明の概略

1. 層の費用の保存式（`layerCost_eq`）で有限層の費用に直し、前の補題。

----

<a id="Tomabechi.Consistency.R123.commonV0X_ge_one"></a>

## 補題 `commonV0X_ge_one`

### 式

$$
V_0^X\ge1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全域の共有評価は 1 以上です。

### 証明の概略

1. \((x_0-x_1)^2\ge0\)。

----

<a id="Tomabechi.Consistency.R123.commonV0XE_contDiff"></a>

## 補題 `commonV0XE_contDiff`

### 式

$$
V_0^X\in C^\infty
$$

### Lean のコメント（日本語訳）

> 全域でC^∞、勾配場baseHessian21。

### 補題の説明

全域の共有評価は、全域で滑らかです（\(C^2\) 以上）。

### 証明の概略

1. 定理 20 の拡張と一致（前の補題）。内積の線形写像の \(C^2\) 性から、二次式として。

----

<a id="Tomabechi.Consistency.R123.commonV0XE_hasGradientAt"></a>

## 補題 `commonV0XE_hasGradientAt`

### 式

$$
\nabla V_0^X(z)=H(z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全域の共有評価の勾配は、\(H(z)=4\langle d,z\rangle d\) です。

### 証明の概略

1. 定理 20 の拡張と一致（前の補題）。勾配の式（`baseGradient21_eq`）。

----

<a id="Tomabechi.Consistency.R123.liftedStageCenter_norm"></a>

## 補題 `liftedStageCenter_norm`

### 式

$$
\|\mathrm{center}(c)\|=|c|
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた段の中心の大きさは、\(|c|\) です。

### 証明の概略

1. 中心 0 との差のノルムの補題（`liftedStageCenter_difference_norm`）で、0 を代入。

----

<a id="Tomabechi.Consistency.R123.stage_center_eq"></a>

## 補題 `stage_center_eq`

### 式

$$
\text{段 }n\text{ の中心}=\mathrm{center}(\text{表象 }n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実際の段 \(n\) の中心は、層 \(n+1\) の表象の持ち上げに等しいです。

### 証明の概略

1. 持ち上げた段の入力の中心の補題と、段列の中心の補題。

----

<a id="Tomabechi.Consistency.R123.stage_center_norm_lt_one"></a>

## 補題 `stage_center_norm_lt_one`

### 式

$$
\|\mathrm{center}_n\|<1
$$

### Lean のコメント（日本語訳）

> 球U_n⊂closedBall 0 3の評価。

### 補題の説明

段の中心の大きさは 1 未満です（球 \(U_n\subset\bar B_3(0)\) の評価のため）。

### 証明の概略

1. 中心の等式と、表象が非負で、\(\top\) 未満であること。

----

<a id="Tomabechi.Consistency.R123.stage_radius_le_two"></a>

## 補題 `stage_radius_le_two`

### 式

$$
\mathrm{radius}_n\le2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の半径は 2 以下です。

### 証明の概略

1. 持ち上げた段の入力の半径の補題と、段列の仕様から。

----

<a id="Tomabechi.Consistency.R123.stage_ball_subset_hull"></a>

## 補題 `stage_ball_subset_hull`

### 式

$$
U_n\subset\bar B_3(0)\subset X
$$

### Lean のコメント（日本語訳）

> 実際の段の閉球はclosedBall 0 3（したがってX）に含まれる。

### 補題の説明

実際の段の閉球は、\(\bar B_3(0)\)（したがって \(X\)）に含まれます。

### 証明の概略

1. 中心の大きさ \(<1\) と半径 \(\le2\) から、三角不等式。

----

<a id="Tomabechi.Consistency.R123.commonV0X_regular_on_stage_balls"></a>

## 補題 `commonV0X_regular_on_stage_balls`

### 式

$$
C^2\wedge\|\nabla V_0\|\le24\wedge\nabla^2V_0\succeq0\ (\text{各段の球上})
$$

### Lean のコメント（日本語訳）

> 全域の共有評価commonV0Xの、各段の球上での(21.3)型の条件：C²・‖∇V₀‖≤24・∇²V₀≽0（β=0）。

### 補題の説明

全域の共有評価 \(V_0^X\) の、各段の球の上での (21.3) 型の条件です。\(C^2\)・\(\|\nabla V_0\|\le24\)・\(\nabla^2V_0\succeq0\)（\(\beta=0\)）。

### 証明の概略

1. 滑らかさと勾配は前の補題。勾配の大きさは、\(\|H(z)\|\le8\|z\|\le24\)（球が \(\bar B_3(0)\) に入るため）。ヘシアンは半正定値（`baseHessian21_psd`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.base_eq_commonV0X_on_box"></a>

## 補題 `SharedModelSignature.base_eq_commonV0X_on_box`

### 式

$$
x\in\mathrm{box}\ \Rightarrow\ N.\mathrm{base}.V_0(x,t)=V_0^X(x)
$$

### Lean のコメント（日本語訳）

> 箱の上でN.base.V0はcommonV0X。

### 補題の説明

箱の上で、`N.base.V0` は \(V_0^X\) に等しいです。

### 証明の概略

1. `N.base.V0` が共有基礎評価であること。個人の閾値の残差 \([(x_i)^2-\theta]_+\) が、箱の内部では 0 になる（\(|x_i|\le1/4\)、\(\theta=1/10\)）ことから、二次式に一致。

----

<a id="Tomabechi.Consistency.R123.SharedCommonDomainX"></a>

## 構造体 `SharedCommonDomainX`

### 式

$$
X:=\mathbb R^2\text{、全域の共有評価 }V_0^X\text{（部分的な統合）}
$$

### Lean のコメント（日本語訳）

> 共通状態領域の統合（部分）：X:=ℝ²、全域の共有評価commonV0X。

### 定義の説明

共通の状態領域の統合（**部分的**）の受入の型です。フィールドは、段の球が \(\bar B_3(0)\subset X\) に入る、定理 20 の拡張が全域で \(V_0^X\)、有限層の実走行費（定理 24）が全域で \(V_0^X\)（共通束の層を通しても）、有限層の軌道が全域で明示解、全域で滑らか・勾配・ヘシアン・各段の球上の勾配の上界、\(V_0^X\ge1\)、`N.base.V0` が箱の上で \(V_0^X\) に一致し一点到達集合が箱の中に留まる、箱の外では `N.base.V0` と \(V_0^X\) が異なる（定理 1・2・4 は箱の上でだけ \(V_0^X\) に結ばれる）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_commonDomainX"></a>

## 定理 `sharedModel_commonDomainX`

### 式

$$
\mathrm{SharedCommonDomainX}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、共通状態領域の統合（部分）を満たします。

### 証明の概略

1. 各フィールドは、上の補題。有限層の軌道の明示解は、追加条件の保存式から。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v8"></a>

## 定理 `final_consistency_v8`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedCommonDomainX}(N)
$$

### Lean のコメント（日本語訳）

> v8：v7に共通状態領域の部分的な統合を加えた存在宣言。

### 補題の説明

第 8 版です。第 7 版に、共通の状態領域の**部分的な**統合を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
