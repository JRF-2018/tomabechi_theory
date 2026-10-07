# Tomabechi/Consistency/ConsistencyR123_Shared16Premises.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Shared16Premises.lean`](../Tomabechi/Consistency/ConsistencyR123_Shared16Premises.lean)（定理16の存在節・表象節・縮小節の前件を述語の field に）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

以前は、定理 16 の**結論**（`Theorem16EntryClause`：一意の固定点・表象の固定・関係・幾何収束）を受入の型に入れました。しかし、結論を出すための**前件**（M7.1–M7.6）は、具体的な定理 `theorem16_intervalGradientFlowC4_generalEntryConnection` の内側にだけあり、述語の外にありました。ここでは前件そのものをフィールドとして並べます。

* 層系（M7.1–M7.4）：各層の担体は層別 TCZ で、非空・コンパクト・凸。射影は担体上で連続アフィン、合成則・恒等、整合点。フィードバックは射影と可換で連続。添字は上向きに有向で最大元なし。
* 表象節（M7.5）：表象空間はコンパクト Hausdorff、関係は閉、表象写像は連続・表象関係を満たし、表象側の写像は連続で、逆極限の写像と同変。二履歴の固定点は異なる。
* 縮小節（M7.6）：履歴別の逆極限は SC 距離で完備、層別フィードバックが誘導する写像は率 \(\exp(-1)<1\) の縮小。

### 0.2 このファイルが証明していないこと

* 対象は具体的な C4 系（\([0,1]\) の対角の逆系、\(\mathbb N\) の添字）です。任意の層系・任意の自己表象についての、一般の前件ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前は定理16の結論（Theorem16EntryClause：一意固定点・表象の固定・関係・幾何収束）を受入型に入れた。しかし結論を出すための前件（M7.1–M7.6）は、具体定理 theorem16_intervalGradientFlowC4_generalEntryConnection の内側にだけあり、述語の外（W）にあった。ここでは前件そのものを field として並べる。…（以下、上の三点と範囲）。各 field の型は既存の層系・adapter の field の型そのもの（type_of%）なので、書き写しによる弱化はない。

---

<a id="Tomabechi.Consistency.R123.Shared16Premises"></a>

## 構造体 `Shared16Premises`

### 式

$$
\text{M7.1–M7.6：層系・表象節・縮小節の前件}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 16 の存在節・表象節・縮小節の**前件**（M7.1–M7.6）を、フィールドとして並べた受入の型です。フィールドは次のとおりです。

* M7.1：各層・各履歴の担体（層別 TCZ）は、空でなく、コンパクトで、凸（`layer_nonempty`・`layer_compact`・`layer_convex`）。
* M7.3：射影は担体上で連続アフィン、合成則・恒等、担体を担体へ送る（`project_maps`・`project_affine`・`project_refl`・`project_comp`・`project_continuous`）。
* M7.2：添字は上向きに有向で、最大元がない（`no_maximum`）。
* M7.4：層別のフィードバックは、射影と可換で連続（`feedback_commutes`・`feedback_continuous`）。
* M7.5（表象節）：表象空間はコンパクト Hausdorff、関係は閉、表象写像は連続で表象関係を満たし、表象側の写像は連続で、逆極限の写像と同変（`rep_*`）。25-A(1)：二履歴の固定点は異なる（`history_sensitive`）。
* M7.6（縮小節）：SC 距離で完備、率 \(\exp(-1)<1\) の縮小（`complete`・`contracting`）。

各フィールドの型は、既存の層系・アダプターのフィールドの型**そのもの**（`type_of%`）なので、書き写しによる弱化はありません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared16Premises"></a>

## 定理 `SharedModelSignature.shared16Premises`

### 式

$$
\mathrm{Shared16Premises}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式と追加条件のもとで、署名は定理 16 の前件をすべて満たします。

### 証明の概略

1. 層別 TCZ が \([0,1]\) に等しい（`layerTCZ_eq_carrier`）ので、非空・コンパクト・凸は区間の性質（`isCompact_Icc`・`convex_Icc`）。
2. それ以外のフィールドは、定理 16→25 の具体の層系の補題（`theorem16_intervalGradientFlowLayerSystem` の各フィールド）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared16Premises"></a>

## 定理 `sharedModel_shared16Premises`

### 式

$$
\mathrm{Shared16Premises}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、定理 16 の前件を満たします。

### 証明の概略

1. 保存式と追加条件の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_16premises"></a>

## 定理 `final_consistency_v2_with_16premises`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{Shared16Premises}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、定理 16 の前件を加えた版です。

### 証明の概略

1. 存在宣言です。前の版から \(N\) を取り、前件を加える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
