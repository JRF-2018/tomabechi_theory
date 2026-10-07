# Tomabechi/Consistency/ConsistencyR1_C6Transport.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C6Transport.lean`](../Tomabechi/Consistency/ConsistencyR1_C6Transport.lean)（C6 の有限・頂点データを、共通束の全体へ再添字する）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

C6 の層ごとのデータ（旧 `WithTop ℕ` の上の依存型の状態・方策と、定理24のデータ）を、**共通束 `CommonConcept` の全体**に**引き戻す**（再添字する）ファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）の部品です。

* 束の点 \(x\) を、`layerProjection` で旧い層の番号に投影し、その層のデータを使う。
* **埋め込みの像**（旧い層）では、旧データを**厳密に回収**（型の変換を除いて）：最適値・走行費・許容性・最適方策・軌道。
* **頂点**では、旧 C6 の頂点のデータそのもの。
* **頂より下のすべての点**で、定理24の結論（正の価値と非恒等の零方策）が成り立つ。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、これは**定理24の入口の移送**です。定理26・27の全層の条件や、R1 全体の統合の完了を意味しません。
* 回収は、型の等式（投影で層の番号が元に戻ること）による cast を除いての一致です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> `layerProjection` を使い、旧 `WithTop ℕ` 上の依存状態・方策と定理24データを `CommonConcept` 全体へ引き戻す。埋込み像では旧データを厳密に回収し、共通束のどの真部分点にも定理24のデータを与える。これは24の入口移送であり、26/27の全層条件や R1 全体の統合完了を意味しない。

---

<a id="Tomabechi.Consistency.R1.dependentValue_cast_eq"></a>

## 補題 `dependentValue_cast_eq`

### 式

$$
f_j(\mathrm{cast}\,x)=f_i(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

依存型の値（実数値の関数）について、添字の等式 \(j=i\) に沿った型の変換（cast）を行っても、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分け（`cases h`）して、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.dependentPolicy_cast_eq"></a>

## 補題 `dependentPolicy_cast_eq`

### 式

$$
f_j(\mathrm{cast}\,x)=\mathrm{cast}(f_i(x))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

依存型の方策について、添字の等式 \(j=i\) に沿った型の変換（cast）を行っても、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.dependentTrajectory_cast_eq"></a>

## 補題 `dependentTrajectory_cast_eq`

### 式

$$
\text{軌道に対して、cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

依存型の軌道について、添字の等式 \(j=i\) に沿った型の変換（cast）を行っても、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.dependentCost_cast_eq"></a>

## 補題 `dependentCost_cast_eq`

### 式

$$
\text{費用に対して、cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

依存型の走行費について、添字の等式 \(j=i\) に沿った型の変換（cast）を行っても、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.dependentPredicate_cast_iff"></a>

## 補題 `dependentPredicate_cast_iff`

### 式

$$
\text{許容性などの述語に対して、cast は真偽を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

依存型の述語（許容性など）について、添字の等式 \(j=i\) に沿った型の変換（cast）を行っても、値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R1.commonConceptLayerState"></a>

## 定義 `commonConceptLayerState`

### 式

$$
\mathrm{C6LayeredState}(\mathrm{layerProjection}(x))
$$

### Lean のコメント（日本語訳）

> 新共通束の各点で使う、旧C6層番号に対応した状態型。

### 定義の説明

新しい共通束の各点 \(x\) で使う、**旧 C6 の層の番号に対応した状態の型**です（束の点を投影して層の番号にし、その層の状態の型を使う）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptLayerPolicy"></a>

## 定義 `commonConceptLayerPolicy`

### 式

$$
\mathrm{C6LayeredPolicy}(\mathrm{layerProjection}(x))
$$

### Lean のコメント（日本語訳）

> 新共通束の各点で使う、旧C6層番号に対応した方策型。

### 定義の説明

新しい共通束の各点で使う、旧 C6 の層の番号に対応した**方策の型**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data"></a>

## 定義 `commonConceptTheorem24Data`

### 式

$$
\text{C6 の定理24データを、単調な射影で共通束全体へ引き戻したもの}
$$

### Lean のコメント（日本語訳）

> C6の定理24データを単調射影で共通束全体へ持ち上げたもの。

### 定義の説明

C6 の定理24のデータを、単調な射影 `layerProjection` で、**共通束の全体**に引き戻したものです。束の各点 \(a\) では、その点を層の番号に投影し、その層のデータ（軌道・走行費・許容性・最適値・最適方策）を使います。定理24の条件も、旧データの条件を、投影を通して移します。

### 証明の概略

1. 各フィールドは、旧データの対応するものに投影を合成する。
2. 定理24の条件（軌道の初期・やり直し・最適性など）は、旧データの条件にそのまま対応する（`exact`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_address"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_address`

### 式

$$
\mathrm{layerProjection}(\mathrm{layerAddressEmbedding}(a))=a
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みの像の点を投影すると、元の層の番号に戻ります。

### 証明の概略

1. `layerProjection_layerAddress`（共通束のファイルの補題）。

----

<a id="Tomabechi.Consistency.R1.commonConcept_layerProjection_top"></a>

## 補題 `commonConcept_layerProjection_top`

### 式

$$
\mathrm{layerProjection}(\top)=\top
$$

### Lean のコメント（日本語訳）

> 新しい共通束の頂点は、旧データの頂添字へ射影される。

### 補題の説明

新しい共通束の頂点は、旧データの頂の添字に射影されます。

### 証明の概略

1. 頂は埋め込みの像（`layerAddress_top`）。`layerProjection_layerAddress`。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24_all_proper_points"></a>

## 定理 `commonConceptTheorem24_all_proper_points`

### 式

$$
\forall a<\top,\ \text{正の価値と非恒等の零方策}
$$

### Lean のコメント（日本語訳）

> 新束の全真部分点で、持ち上げた24データが正価値と非恒等零方策を与える。

### 補題の説明

新しい束の**頂より下のすべての点**で、引き戻した定理24のデータが、**正の価値**と**非恒等の零方策**を与えます（定理24の結論）。

### 証明の概略

1. 頂より下の点は、投影しても頂の番号にならない（`layerProjection_lt_top_of_lt_top`）。
2. 旧データの全有限層での定理24（`c6LayeredData_all_finite_theorem24`）を、投影した層に適用する。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_finite_layer"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_finite_layer`

### 式

$$
\text{旧層の軌道を、埋め込んだ点で（型の等式を除いて）回収}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

旧い層を共通束に埋め込んだ点では、引き戻したデータの軌道が、旧データの軌道に（型の同一視を除いて）一致します（`HEq`）。

### 証明の概略

1. 定義を展開し、投影が元の層に戻ること（`layerProjection_layerAddress`）による型の同一視のもとで、同じ関数であることを示す。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_optimalValue"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_optimalValue`

### 式

$$
V^*_{\text{共通束}}(\iota a)=V^*_{\text{旧}}(a)
$$

### Lean のコメント（日本語訳）

> 旧層を共通束へ埋め込んでも、最適値を保つ。

### 補題の説明

旧い層を共通束へ埋め込んでも、**最適値は保たれます**。

### 証明の概略

1. 定義を展開し、型の変換の補助補題（`dependentValue_cast_eq`）で cast を外す。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_runningCost"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_runningCost`

### 式

$$
\text{走行費の保存}
$$

### Lean のコメント（日本語訳）

> 旧層の方策・状態を型変換して埋め込んでも、瞬時費用を保つ。

### 補題の説明

旧い層の方策・状態を、型の変換をして埋め込んでも、**瞬時の費用は保たれます**。

### 証明の概略

1. 定義を展開し、`dependentCost_cast_eq`。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_admissibility"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_admissibility`

### 式

$$
\text{許容性の保存（同値）}
$$

### Lean のコメント（日本語訳）

> 旧層の許容性も、共通束上の対応層で同値に保たれる。

### 補題の説明

旧い層の**許容性**も、共通束の上の対応する層で、同値に保たれます。

### 証明の概略

1. 定義を展開し、`dependentPredicate_cast_iff`。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_optimalPolicy"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_optimalPolicy`

### 式

$$
\text{最適方策の保存（型の変換を除く）}
$$

### Lean のコメント（日本語訳）

> 旧層の最適方策も、層同値による型変換を除いてそのまま回収される。

### 補題の説明

旧い層の**最適方策**も、層の同値による型の変換を除いて、そのまま回収されます。

### 証明の概略

1. 定義を展開し、`dependentPolicy_cast_eq`。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_recovers_old_trajectory"></a>

## 補題 `commonConceptTheorem24Data_recovers_old_trajectory`

### 式

$$
\text{軌道の保存（型の変換を除く）}
$$

### Lean のコメント（日本語訳）

> 旧層の軌道も、状態・方策を型変換すれば共通束側で厳密に回収される。

### 補題の説明

旧い層の**軌道**も、状態・方策を型の変換すれば、共通束の側で厳密に回収されます。

### 証明の概略

1. 定義を展開し、`dependentTrajectory_cast_eq`。

----

<a id="Tomabechi.Consistency.R1.commonConceptTheorem24Data_top_trajectory"></a>

## 補題 `commonConceptTheorem24Data_top_trajectory`

### 式

$$
\text{頂点の軌道}=\text{旧 C6 の頂点軌道}
$$

### Lean のコメント（日本語訳）

> 持ち上げた24データの頂点軌道は、旧C6頂点軌道そのものである。

### 補題の説明

引き戻したデータの頂点の軌道は、旧 C6 の頂点の軌道そのものです（`HEq`）。

### 証明の概略

1. 頂点は頂の番号に投影される（`commonConcept_layerProjection_top`）。投影した層の軌道は旧データの頂点の軌道。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
