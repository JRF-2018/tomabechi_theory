# Tomabechi/Consistency/ConsistencyR123_Shared16LayerTCZ.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Shared16LayerTCZ.lean`](../Tomabechi/Consistency/ConsistencyR123_Shared16LayerTCZ.lean)（定理16の担体を層別 TCZ と同定）。
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
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 局所凸空間 | 凸な開集合の基をもつ位相ベクトル空間。Schauder 型不動点定理の舞台。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 16 の担体 \(K_{i,\alpha}(h)\) を、層別の TCZ と同定する**ファイルです。原文の §7 は \(K_{i,\alpha}(h):=\mathrm{TCZ}_{i,\alpha}(h)\subset E_{i,\alpha}\) と書きます。従来は、定理 16 の系の担体が、旧署名の自己表象の TCZ（全層で同じ区間 \([0,1]\)）を読むだけで、`N.data` の層 \(\alpha\) の制御データから作った TCZ との等式がありませんでした。また、存在節・表象節・縮小節の前件は具体的な定理の側にだけあり、述語の外にありました。

**案 A（観測で結ぶ）**を採ります。既存の区間の担体は保ち、層 \(\alpha=\) `index16 i` と履歴 \(h\) について、層別の TCZ を、**同時刻の到達 ∩ 評価の閾値**の集合として定義します。

* 履歴の中心での共有核の一歩の認知座標に到達する点であって、
* `N.data` の層 \(\alpha\) の**実走行費**が、閾値 \(1+16\cdot\tfrac12=9\) 以下（すなわち評価 \(V_h\le\tfrac12\)）であるもの。

層の状態の型と旧い有限層の `AgentState` は、型の同値で結びます（cast）。追加条件と保存式のもとで、旧署名の自己表象の TCZ・層別 TCZ・区間 \([0,1]\) が一致することと、定理 16 の存在節・表象節・縮小節を、同じ述語のフィールドに入れることを証明します。

### 0.2 このファイルが証明していないこと

* 層 \(\alpha\) の制御問題は、「共有核の一歩と層 \(\alpha\) の費用」を通して使います。層ごとに独立の制御問題から TCZ を再構成して、担体が層で変わる案 B は採りません（担体は全層で \([0,1]\) のまま）。
* 定理 16 の原文の仮定のうち、担体が局所凸 Hausdorff であることは、\([0,1]\subset\mathbb R\) で成り立ちます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §7 は K_{i,α}(h) := TCZ_{i,α}(h) ⊂ E_{i,α} と書く。従来、定理16の系の担体は旧署名の (selfRepresentation h).TCZ i（全層で同じ区間 [0,1]）を読むだけで、N.data の層 α の制御データから作った TCZ との等式がなかった。また、存在節・表象節・縮小節の前件は具体定理の側にだけあり、述語の外にあった。**案A（観測で結ぶ）を採る。** …（以下、上の二点と、範囲の注意が続く。）

---

<a id="Tomabechi.Consistency.R123.layerStateCast"></a>

## 定義 `layerStateCast`

### 式

$$
\text{AgentState}\to\text{層 }\mathrm{index}_{16}(i)\text{ の状態}
$$

### Lean のコメント（日本語訳）

> 層index16 iの状態型と旧有限層AgentStateの同一視（型の等式からのcast）。

### 定義の説明

層 `index16 i` の状態の型と、旧い有限層の `AgentState` の**同一視**です（型の等式からの cast）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.layerPolicyCast"></a>

## 定義 `layerPolicyCast`

### 式

$$
\text{ゲイン信号}\to\text{層 }\mathrm{index}_{16}(i)\text{ の方策}
$$

### Lean のコメント（日本語訳）

> 層α=index16 iの方策型と旧有限層の方策型の同一視。

### 定義の説明

層 \(\alpha=\) `index16 i` の方策の型と、旧い有限層の方策の型の同一視です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.layerCostThreshold"></a>

## 定義 `layerCostThreshold`

### 式

$$
9=1+16\cdot\tfrac12
$$

### Lean のコメント（日本語訳）

> 評価閾値V_h≤1/2に対応する実走行費の閾値1+16·(1/2)。

### 定義の説明

評価の閾値 \(V_h\le 1/2\) に対応する、実走行費の閾値 \(1+16\cdot\tfrac12=9\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerTCZ"></a>

## 定義 `SharedModelSignature.layerTCZ`

### 式

$$
\mathrm{TCZ}_{i,\alpha}(h)=\{\text{同時刻到達}\}\cap\{\text{層 }\alpha\text{ の実走行費}\le 9\}
$$

### Lean のコメント（日本語訳）

> 履歴h・層index16 iのTCZ（案A）。同時刻到達∩層αの実走行費の閾値集合。

### 定義の説明

履歴 \(h\)・層 `index16 i` の TCZ です（案 A）。履歴の中心での共有核の一歩の認知座標に**同時刻に到達**する点で、かつ、`N.data` の**層 \(\alpha\) の実走行費**が閾値以下のものの集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.layerCost_eq"></a>

## 補題 `SharedDataPreservation.layerCost_eq`

### 式

$$
\text{層 }\alpha\text{ の費用}=\text{旧有限層の費用}
$$

### Lean のコメント（日本語訳）

> 有限層の費用は、型のcastを通しても旧有限層の費用に等しい。

### 補題の説明

有限層の費用は、型の cast を通しても、旧い有限層の費用に等しいです。

### 証明の概略

1. 費用の保存式で書き換え、層の等式 \(idx=\mathrm{some}\ i\) について一般化した補題（`key`）で cast を消す。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerCost_eq_potential"></a>

## 補題 `SharedModelSignature.layerCost_eq_potential`

### 式

$$
\text{層 }\alpha\text{ の実走行費}=1+16\,V_h
$$

### Lean のコメント（日本語訳）

> 層αの実走行費は、同じ履歴中心の二次評価1+16V_hに等しい。

### 補題の説明

層 \(\alpha\) の実走行費は、同じ履歴の中心の二次の評価 \(1+16V_h\) に等しいです。

### 証明の概略

1. 前の補題で旧い有限層の費用に直し、追加条件の費用の式（`finite_c1_cost`）と、共有基礎評価の一致を使う。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerTCZ_eq_carrier"></a>

## 補題 `SharedModelSignature.layerTCZ_eq_carrier`

### 式

$$
\mathrm{TCZ}_{i,\alpha}(h)=[0,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層別の TCZ は、区間の担体 \([0,1]\) に等しいです。

### 証明の概略

1. 両方向の包含。\(\subseteq\)：到達する点の認知座標が区間に入る（履歴の中心・流れ・核の補題）。\(\supseteq\)：区間の点を、一歩の到達で実現し、費用の閾値以下であること（`layerCost_eq_potential`）を確かめる。

----

<a id="Tomabechi.Consistency.R123.Theorem16EntryClause"></a>

## 定義 `Theorem16EntryClause`

### 式

$$
\forall h,\ \exists!\,x\in\varprojlim,\ \text{固定点}\wedge\text{表象で固定}\wedge\text{関係}\wedge\text{率 }e^{-1}\text{ で幾何収束}
$$

### Lean のコメント（日本語訳）

> 定理16の存在節・表象節・縮小節（C4一般入口の第一連言）。履歴ごとの逆極限に一意な固定点があり、表象写像の下でも固定され、関係に属し、率exp(-1)で幾何収束する。

### 定義の説明

定理 16 の**存在節・表象節・縮小節**です（定理 16→25 の一般入口の第一連言）。履歴ごとの逆極限に一意な固定点があり、表象写像の下でも固定され、関係に属し、率 \(\exp(-1)\) で幾何収束します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.theorem16EntryClause_holds"></a>

## 定理 `theorem16EntryClause_holds`

### 式

$$
\mathrm{Theorem16EntryClause}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 16 の存在節・表象節・縮小節が成り立ちます。

### 証明の概略

1. 定理 16→25 の一般入口の接続（`theorem16_intervalGradientFlowC4_generalEntryConnection`）の第一成分。

----

<a id="Tomabechi.Consistency.R123.Shared16LayerTCZInputs"></a>

## 構造体 `Shared16LayerTCZInputs`

### 式

$$
\text{担体}=\text{層別TCZ}\ \wedge\ \text{費用}=1+16V_h\ \wedge\ \text{存在・表象・縮小節}
$$

### Lean のコメント（日本語訳）

> 定理16の担体と層別TCZの同定と、存在・表象・縮小節を同じNの述語に入れた受入型。層α=index16 i。

### 定義の説明

定理 16 の担体と層別 TCZ の同定、および存在・表象・縮小節を、同じ \(N\) の述語に入れた受入の型です（層 \(\alpha=\) `index16 i`）。フィールドは、旧署名の自己表象の TCZ が層別 TCZ に等しいこと、定理 16 の層系の担体が層別 TCZ に等しいこと、層の実走行費が \(1+16V_h\) に等しいこと、存在節・表象節・縮小節、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared16LayerTCZInputs"></a>

## 定理 `SharedModelSignature.shared16LayerTCZInputs`

### 式

$$
\mathrm{Shared16LayerTCZInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式と追加条件のもとで、署名は担体の同定の入力を満たします。

### 証明の概略

1. 各フィールドは上の補題（`layerTCZ_eq_carrier`・`layerCost_eq_potential` と、自己表象の TCZ の補題）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared16LayerTCZInputs"></a>

## 定理 `sharedModel_shared16LayerTCZInputs`

### 式

$$
\mathrm{Shared16LayerTCZInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、担体の同定の入力を満たします。

### 証明の概略

1. 保存式と追加条件の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_16layerTCZ"></a>

## 定理 `final_consistency_with_16layerTCZ`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{Shared16LayerTCZInputs}(N)
$$

### Lean のコメント（日本語訳）

> 容量入力・定理16の添字入力に、定理16の担体の層別TCZ同定を加えた存在宣言。

### 補題の説明

容量の入力・定理 16 の添字の入力に、定理 16 の担体の層別 TCZ の同定を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は、`sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
