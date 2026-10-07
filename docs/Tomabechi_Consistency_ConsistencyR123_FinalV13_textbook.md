# Tomabechi/Consistency/ConsistencyR123_FinalV13.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FinalV13.lean`](../Tomabechi/Consistency/ConsistencyR123_FinalV13.lean)（最終存在宣言 v13：四つの追加を同じ共有モデル `N` で束ねる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

最初の最終存在宣言（[Final](Tomabechi_Consistency_ConsistencyR123_Final_textbook.md)）の後、共有モデルに次の四つの補完を足していきました。このファイルは、それらを**同じ一つの `sharedModel`** で同時に満たす、と述べる宣言 v13 をまとめます。

| 追加 | 内容 | 入力型 |
| --- | --- | --- |
| 層制御系 | 定理16の各層の TCZ を生成する制御系（速度制御 \(\dot x=u\)） | `LayerControlSound` |
| 担体全体の自己過程 | 定理16の担体 `ball16` 全体を型にした自己表象・自己過程（定理25） | `Shared25FullSelf` |
| 現行評価の原文前件 | 現行の基礎評価 `commonV0X` での有限地平 argmin、補題0 の全点・再始動 | `FullOriginalPremisesCurrent` |
| 容量 | 情報容量を「問題×方策」の上限として型づけ（定理19） | `SharedPolicyCapacityInputs` |

さらに、新しい制御族・表象・方策を入れた後でも、定理24の最適方策と実走行費、定理19の joint、定理25の介入不変性が保たれることを、`SharedFinalCrossChecksV13` で再確認します。

### 0.2 このファイルが証明していないこと（報告の範囲）

この宣言が言うのは**「限定つきの同時充足」**です。

* 定理16の層の TCZ を生成する制御系は、層ごとの**独立した**制御系（速度制御）を認める読みです。`N.data` の有界ゲインの力学（中心に到達しない）から導いたものではありません。
* 定理3の初期点は、`X1` の零平均点に限ります。
* 定理25-C4・25-C5 は、原文が「本モデルでは」と書くモデル例です。
* 容量の方策族は一元です。
* 距離は sup 距離です（Euclid 距離版は次の v14 で補います）。
* 原文を**一つの共有制御系**として読む強い認定ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> v11（`SharedFinalConsistency`）と v12（定理3の `Φ₂ = DX`）に、次の四つの追加を同じ `sharedModel` で束ねる。（四つの追加は上の表のとおり。）あわせて、新しい生成族・表象・方策を導入した後も、24 の最適方策・実走行費、19 の joint、25 の介入不変性が保たれることを `SharedFinalCrossChecksV13` で再照合する。
>
> **範囲（報告基準）：** 「限定つきの同時充足」。層別の独立生成系、定理3は `X1` の零平均点、25-C4/C5 はモデル例、容量の方策族は一元、距離は sup 距離（Euclid 版は別途）。原文を一つの共有制御系として読む強い認定ではない。

（v11・v12 は、途中の版の呼び名です。v11 は定理1–4・20・24・25 などの共通領域・容量・自己表象を整えた版、v12 は定理3を共通評価で述べた版です。）

---

<a id="Tomabechi.Consistency.R123.SharedFinalCrossChecksV13"></a>

## 構造体 `SharedFinalCrossChecksV13`

### 式

$$
\text{実走行費}=V_0,\quad \text{最適方策}\ne\text{他の方策},\quad \text{joint}=\text{情報法則},\quad \text{25-A(2)},\quad \mathrm{TCZ}_{\text{自己表象}}=\mathrm{TCZ}_{\text{正典}},\quad \text{定理3の目標非空}\iff x_0+x_1=0
$$

### Lean のコメント（日本語訳）

> 新しい生成族・表象・方策を入れた後の再照合。

各フィールドのコメント：

* `layer_cost_current`：24・13：有限層の実走行費は全域で `commonV0X`（制御系の導入で `N.data` は不変）。
* `optimal_policy_true`：最適方策：`decode c true` は `N.data` の最適方策で、`false` と別の実制御方策。
* `joint_information`：19：問題×方策の joint は情報法則で、固定 decoder の `capacityJoint` に一致。
* `intervention_invariance`：25：担体全体の自己過程でも介入不変性（条件 25-A(2)）が全主体・全共通束点で成り立つ。
* `tcz_canonical`：25・16：自己表象の TCZ は正典 TCZ で、Ego は担体全体上の選択フィードバック。
* `theorem3_zero_mean`：原文の目標非空条件を満たす定理3の初期点は零平均点に限る（モデル内の帰結）。

### 定義の説明

新しい部品を足すと、以前の部品との整合が崩れていないかが心配になります。この構造体は、その**再確認の項目表**です。

* 定理24の有限層の走行費が、いつでも共通評価 `commonV0X` に一致する（制御系を足しても `N.data` が変わらない）。
* ゴールを復号する二つの方策のうち、`true` に対応するものが最適方策で、`false` に対応するものは別の許容方策である。
* 定理19の問題×方策の joint は、情報法則に一致する。
* 定理25の介入不変性（条件 25-A(2)）が、担体全体の自己過程でも全主体・全共通束点で成り立つ。
* 自己表象の TCZ は正典 TCZ に一致する。
* 定理3は、目標が空でないことと初期点の座標和が 0 であることが同値（零平均の点に限る）。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedFinalConsistencyV13"></a>

## 構造体 `SharedFinalConsistencyV13`

### 式

$$
\text{v11}\ \wedge\ \text{定理3}\ \wedge\ \text{層制御系}\ \wedge\ \text{全担体の自己過程}\ \wedge\ \text{現行評価の前件}\ \wedge\ \text{容量}\ \wedge\ \text{再照合}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

v13 の述語です。七つのフィールドは次のとおりです。

* `final`：v11 の述語（`SharedFinalConsistency`。原文前提・追加条件・非退化性と、共通領域・容量などの整合）。
* `theorem3`：定理3の入力（`SharedDomainTheorem3`）。
* `layer_control`：層制御系の健全性（`LayerControlSound N sig`。制御系の署名 `sig` を引数に取る）。
* `full_self`：担体全体の自己過程（`Shared25FullSelf`）。
* `current_premises`：現行評価の原文前件（`FullOriginalPremisesCurrent`）。
* `policy_capacity`：問題×方策の容量（`SharedPolicyCapacityInputs`）。
* `cross_checks`：再照合（`SharedFinalCrossChecksV13`）。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_finalCrossChecksV13"></a>

## 定理 `sharedModel_finalCrossChecksV13`

### 式

$$
\mathrm{SharedFinalCrossChecksV13}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`sharedModel` が再照合の全項目を満たします。

### 証明の概略

各フィールドは、別のファイルで証明された入力型のフィールドをそのまま渡します。

1. 走行費：`FullOriginalPremisesCurrent` の `v0_is_layer_cost`。
2. 最適方策・別の方策：容量入力の `policy_true_optimal`・`policy_values_distinct`。
3. joint：`SharedPolicyCapacityInputs` の `joint_information`。
4. 介入不変性・正典 TCZ：`Shared25FullSelf` の `a2`・`tcz_canonical`。
5. 定理3の零平均：`FullOriginalPremisesCurrent` の `theorem3_target_nonempty`。

----

<a id="Tomabechi.Consistency.R123.sharedModel_finalConsistencyV13"></a>

## 定理 `sharedModel_finalConsistencyV13`

### 式

$$
\mathrm{SharedFinalConsistencyV13}(\text{sharedModel},\ \text{velocityLayerControlSignature})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`sharedModel` に、層制御系の署名として速度制御の署名 `velocityLayerControlSignature` を組み合わせると、v13 の述語が成り立ちます。

### 証明の概略

七つのフィールドを、それぞれ対応する定理で埋める（`sharedModel_finalConsistency`、`sharedModel_domainTheorem3`、`sharedModel_layerControlSound`、`sharedModel_shared25FullSelf`、`sharedModel_fullOriginalPremisesCurrent`、`sharedModel_policyCapacityInputs`、`sharedModel_finalCrossChecksV13`）。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v13"></a>

## 定理 `final_consistency_v13`

### 式

$$
\exists N,\ \exists\,\mathrm{sig},\ \mathrm{SharedFinalConsistencyV13}(N,\mathrm{sig})
$$

### Lean のコメント（日本語訳）

> v13：限定つきの同時充足（層別の独立生成系、定理3は `X1` 零平均、容量の方策族は一元）。

### 補題の説明

v13 の存在宣言です。§0.2 の限定つきで、原文の前提・追加条件・非退化性、および四つの補完が、同じ共有モデルで同時に満たされます。次の v14 が、現在の代表の宣言です。

### 証明の概略

1. `sharedModel` と `velocityLayerControlSignature` を取り、直前の定理を使う。

----

## コメント修正記録

`.lean` のコメントの修正はありません（この解説書の作成前に、作業記録への言及を取り除く修正を別に行いました）。
