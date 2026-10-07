# Tomabechi/Consistency/ConsistencyR123_FinalV2.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FinalV2.lean`](../Tomabechi/Consistency/ConsistencyR123_FinalV2.lean)（最終存在宣言 v2（先行する受入型をまとめる））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

先行するファイルで作った受入の型（容量・層別 TCZ・距離の統一・H 条件・16 の添字・基礎評価の領域・N 自身の非退化性）を、**一つの最終の存在宣言の第 2 版**にまとめるファイルです。旧い `final_consistency_model_exists` は残し、新しい受入の型を足した別の宣言を置きます。

| 述語 | 旧の述語に足したもの |
| --- | --- |
| `FullOriginalPremisesV2` | 定理 19 の容量を \(\mathbb L\) の全域で／定理 16 の担体と層別 TCZ・存在表象縮小節／定理 1–4 の誤差を Euclid 距離で |
| `ExplicitAdditionalConditionsV2` | 名前つきの H-info/H-flow/H-sum/H-stage／定理 16 の層の添字／基礎評価の領域 \(X:=\mathrm{box}\) |
| `SharedNondegenerateV2` | \(N\) 自身の量で読む非退化性 |

### 0.2 このファイルが証明していないこと

* Lean で定義した述語についての存在証明です。原文の**読みの判断**（定理 21 の \(V_0\)、定理 26 の完全状態、19 と 16 の主体の同一性、定理 25-C4/C5 のモデル例）は、[前提の対応表](Consistency_Premises_Table.md)に記録しています。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 旧 final_consistency_model_exists は残し、新しい受入型を足した別の宣言を置く。（以下、三つの V2 の述語の内訳。）範囲：これは Lean で定義した述語についての存在証明である。原文の読みの判断は非公開の対応表に記録した。他AIによる読み合わせは未実施。

---

<a id="Tomabechi.Consistency.R123.FullOriginalPremisesV2"></a>

## 構造体 `FullOriginalPremisesV2`

### 式

$$
\text{旧の前提}\wedge\text{容量}\wedge\text{層別TCZ}\wedge\text{距離の統一}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

原文の前提の第 2 版です。フィールドは、旧い `FullOriginalPremises`、定理 19 の容量を \(\mathbb L\) の全域で（`SharedCapacityInputs`）、定理 16 の担体と層別 TCZ の同定・存在表象縮小節（`Shared16LayerTCZInputs`）、定理 1–4 の誤差を定理 20 と同じ Euclid 距離で（`SharedNormUnification`）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ExplicitAdditionalConditionsV2"></a>

## 構造体 `ExplicitAdditionalConditionsV2`

### 式

$$
\text{旧の追加条件}\wedge\text{H 条件}\wedge\text{16 の添字}\wedge X:=\mathrm{box}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

追加の明示条件の第 2 版です。フィールドは、旧い `ExplicitAdditionalConditions`、名前つきの H-info/H-flow/H-sum/H-stage（`ExplicitHConditions`）、定理 16 の層の添字（`Shared16Indexing`）、基礎評価の領域 \(X:=\mathrm{box}\)（`SharedBaseDomain`）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedNondegenerateV2"></a>

## 構造体 `SharedNondegenerateV2`

### 式

$$
\text{旧の非退化性}\wedge\text{N 自身の量の非退化性}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

非退化性の第 2 版です。旧い `SharedNondegenerate` に、\(N\) 自身の量で読む `SharedNativeNondegenerate` を加えたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.final_consistency_model_exists_v2"></a>

## 定理 `final_consistency_model_exists_v2`

### 式

$$
\exists N,\ \mathrm{FullOriginalPremisesV2}\wedge\mathrm{ExplicitAdditionalConditionsV2}\wedge\mathrm{SharedNondegenerateV2}
$$

### Lean のコメント（日本語訳）

> 最終存在宣言v2。外部のモデル前提を含まない。

### 補題の説明

**最終の存在宣言の第 2 版**です。外部のモデルの前提を含みません。

### 証明の概略

1. `sharedModel` を取り、各部品の定理（`sharedModel_fullOriginalPremises`・`sharedModel_capacityInputs`・`sharedModel_shared16LayerTCZInputs`・`sharedModel_normUnification` など）を組み合わせる。

----


## コメント修正記録

範囲の段落の末尾にあった、作業用の記録への言及は、この解説書では「前提の対応表」への言及に置き換えました。
