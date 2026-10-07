# Tomabechi/Consistency/ConsistencyR123_BorelStructure.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_BorelStructure.lean`](../Tomabechi/Consistency/ConsistencyR123_BorelStructure.lean)（状態の距離・制御の位相は原文のノルム／Borel 構造と一致する（H-flow″））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

H-flow″ の前半（状態の距離）は、距離の統一で閉じました（定理 1・3・4 の誤差の境界と結論を、定理 20 と同じ Euclid 距離で述べ直した）。ここでは後半、**状態と制御の位相・Borel 構造が、原文のノルム／Borel 構造と一致する**ことを述語にします。

* **有限層の状態：** `AgentState = Fin 2 → ℝ`（sup 距離・積 σ 代数）と、Euclid 表示 `EuclideanSpace ℝ (Fin 2)` は、どちらも Borel 空間で、座標写像は同相かつ可測同値です。同じ \(\mathbb R^2\) の二つのノルムが、同じ位相・同じ Borel 構造を与えます。
* **頂点の状態：** `fullCommonLayerState ⊤` の可測構造は、E2 の距離を引き戻した距離の Borel 構造で、E2 への等長な可測同値があります。非負時刻つきの状態空間も Borel 空間です。
* **制御：** 有限層の制御は、\(\mathbb R\) 値の可測（標準 Borel 構造）で有界なゲイン信号（値は \([0,3]\)）。頂点の制御空間は E2（ノルム位相と Borel 構造）で、頂点の方策族は、非負時刻上の Borel マルコフフィードバックと同値です。

### 0.2 このファイルが証明していないこと

* 位相・Borel 構造の**一致の記述**です。制御の集合の位相（たとえば、ゲイン信号の空間に位相を入れたときの連続性）は課していません（原文の制御は、可測性だけが使われます）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> H-flow″ の前半（状態の距離）は距離の統一で、1・3・4 の誤差境界と結論を定理20と同じ Euclid 距離で述べ直して閉じた。ここでは後半、状態と制御の位相・Borel 構造が原文のノルム／Borel 構造と一致することを述語にする。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.SharedBorelStructure"></a>

## 構造体 `SharedBorelStructure`

### 式

$$
\text{状態の位相・Borel 構造と、制御の可測構造が、原文のノルム／Borel 構造と一致}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態と制御の位相・Borel 構造が、原文のノルム／Borel 構造と一致することを述べる受入の型です。フィールドは次のとおりです。

* 有限層の状態：`AgentState`（sup 距離）と Euclid 表示は、ともに Borel 空間（`state_borel`）。座標写像は同相（`state_chart_homeo`）かつ可測同値（`state_chart_measurable`）。
* 頂点の状態：頂点の状態の可測構造は、E2 の距離を引き戻した距離の Borel 構造で、E2 への等長な可測同値がある（`top_state_borel`・`top_state_chart`）。非負時刻つきの状態空間も Borel 空間（`top_time_state_borel`）。
* 制御：実数は Borel 空間（`real_borel`）。有限層の制御は、可測で有界（値は \([0,3]\)）のゲイン信号（`finite_control`）。頂点の制御空間は E2（`top_control_borel`）で、頂点の方策族は、非負時刻上の Borel マルコフフィードバックと同値（`top_policy_class`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedBorelStructure"></a>

## 定理 `SharedModelSignature.sharedBorelStructure`

### 式

$$
\mathrm{SharedBorelStructure}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

任意の共有署名が、Borel 構造の一致を満たします。

### 証明の概略

1. 各フィールドは、Mathlib の標準の事実（連続写像は可測、型クラスの推論）と、頂点の状態の同値の補題（`fullCommonTopStateMeasurableEquiv`・`fullCommonTopStateEquiv_isometry`）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_borelStructure"></a>

## 定理 `sharedModel_borelStructure`

### 式

$$
\mathrm{SharedBorelStructure}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、Borel 構造の一致を満たします。

### 証明の概略

1. 前の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_borel_structure"></a>

## 定理 `final_consistency_v2_with_borel_structure`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedBorelStructure}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、Borel 構造の一致を加えた版です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
