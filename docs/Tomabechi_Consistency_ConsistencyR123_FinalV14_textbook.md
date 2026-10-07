# Tomabechi/Consistency/ConsistencyR123_FinalV14.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FinalV14.lean`](../Tomabechi/Consistency/ConsistencyR123_FinalV14.lean)（代表の最終存在宣言 v14：三つの小補完を加える）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| 標準公理 | `propext`, `Classical.choice`, `Quot.sound`。Mathlib の数学が使う標準的な公理。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

v13（[FinalV13](Tomabechi_Consistency_ConsistencyR123_FinalV13_textbook.md)）に、三つの小さな補完を足したのが v14 で、これが**無矛盾性の代表の存在宣言** `final_consistency_v14` です。v13 の宣言・型・結論は変えていません。

| 補完 | 内容 |
| --- | --- |
| Euclid 距離への統一 | 現行評価での定理1–4の「全点の二乗誤差」を、定理20と同じ Euclid 距離へ移す（定数 \(C=2\)）。これで定理1–4と20の距離が一つのノルムに揃う（追加条件 H-flow の一部）。 |
| 全担体の Self の等号 | 担体全体の自己表象で、Self が到達和集合から TCZ を**ちょうど**返す（包含ではなく等号）。 |
| 容量 joint の周辺 | 容量の「問題×方策」の joint は、担体全体の自己過程を含む実験の情報周辺にも一致する。 |

名前に含まれる `P21` は、作業の段階を示す名残で、意味は「この三つの補完」です。

### 0.2 このファイルが証明していないこと

* 報告の範囲は v13 と同じです（層別の独立生成系の読み）。単一の共有制御系ではありません。
* Self の等号は、この証人の**時間に依らない評価** `ball16` についての等号で、時間に依存する評価での一般の法則ではありません。
* 自己過程を含む joint 全体の、以前の版と新しい版の等号は要求しません（情報周辺の一致だけです）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 独立の監査で示された三つの小補完を、受入型へ入れる。v13 の宣言・型・結論は変更しない。
> * 現行評価 `commonV0X` の定理1–4（`FullOriginalPremisesCurrent` の `RestartLemma0`）の K 全点の二乗誤差を、定理20と同じ Euclid 距離へ移す（定数 C=2）。これで現行版でも定理1–4 と 20 の距離が一つのノルムに揃う（追加条件 H-flow″）。
> * 担体全体の自己表象で、Self が到達和集合から TCZ を**ちょうど**返す（包含ではなく等号）。この証人の時間独立な評価 `ball16` についての等号で、時変評価一般の法則ではない。
> * 容量の問題×方策の joint は、担体全体の自己過程を含む実験の情報周辺にも一致する。自己過程を含む joint 全体の旧新等号は要求しない。

---

<a id="Tomabechi.Consistency.R123.RestartLemma0.euclid_error_all_K"></a>

## 補題 `RestartLemma0.euclid_error_all_K`

### 式

$$
\operatorname{dist}_{\text{Euclid}}\bigl(y,\ \mathrm{TCZ}\bigr)^2\ \le\ 2\,\Phi(y,t)\qquad (y\in K)
$$

### Lean のコメント（日本語訳）

> `RestartLemma0` の K 全点の sup 距離の二乗誤差（係数1）を、Euclid 距離（係数2）へ移す。

### 補題の説明

補題0（`RestartLemma0`）は、定理1–4 の誤差境界「目標までの距離の二乗 \(\le\) 残差 \(\Phi\)」を、sup 距離（座標の最大値）で与えます。この補題は、同じことを Euclid 距離で述べ直します。平面では \(\lVert\cdot\rVert_\infty\le\lVert\cdot\rVert_2\le\sqrt2\,\lVert\cdot\rVert_\infty\) なので、二乗誤差の係数が 1 から 2 になります。

### 証明の概略

1. sup 距離の二乗誤差から Euclid 距離の二乗誤差を導く補題 `euclid_sq_error_of_sup` を適用する。
2. sup 版の誤差境界（`h.error_all_K`）を、その前件として渡す。

----

<a id="Tomabechi.Consistency.R123.EuclidAllKError"></a>

## 定義 `EuclidAllKError`

### 式

$$
\forall x\in D,\ \forall t_0\ge0,\ \forall y\in K(x,t_0),\ \forall t,\ \ \operatorname{dist}(y,\mathrm{Tgt}(x,t_0,t))^2\le 2\Phi(y,t)
$$

### Lean のコメント（日本語訳）

> Euclid 距離での K 全点の二乗誤差（`RestartLemma0` の誤差部分の Euclid 版）。

### 定義の説明

領域 `D` の初期点 `x`、非負の開始時刻 `t₀`、一点 K（`pointReachableClosure x t₀`）の全点 `y`、全時刻 `t` について、Euclid 距離での二乗誤差が \(2\Phi\) 以下であることを述べる命題です。

### 証明の概略

定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.RestartLemma0.euclidAllKError"></a>

## 補題 `RestartLemma0.euclidAllKError`

### 式

$$
\mathrm{RestartLemma0}(D,\Phi,\mathrm{Tgt},\mathrm{rate})\ \Longrightarrow\ \mathrm{EuclidAllKError}(D,\Phi,\mathrm{Tgt})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

補題0 が成り立つなら、Euclid 版の全点誤差が成り立ちます。前の補題を、`EuclidAllKError` の形に包み直したものです。

### 証明の概略

1. 全ての量化を取り、前の補題 `euclid_error_all_K` を適用する。

----

<a id="Tomabechi.Consistency.R123.sharedModel_full_self_eq"></a>

## 定理 `sharedModel_full_self_eq`

### 式

$$
\mathrm{Self}_i\bigl(\textstyle\bigcup_{\tau\ge0}\mathrm{Reach}(\tau)\bigr)\ =\ \mathrm{TCZ}_i
$$

### Lean のコメント（日本語訳）

> 担体全体の自己表象で、Self は到達和集合から TCZ をちょうど返す。

### 補題の説明

定理25の自己表象 `Self` に、一点の初期状態から到達できる点の和集合を渡すと、定理16の担体 TCZ がちょうど返ってきます（包含ではなく**等号**）。担体 `ball16` が時間に依らない評価に対する集合なので、この等号が成り立ちます。

### 証明の概略

1. 集合の外延性（`ext y`）で、両方向を示す。
2. （→）到達点 `y` が、時刻 `τ` で Ω に入っていることから、層の Ω の等式（`layerOmega_eq`）で `y ∈ ball16 h` に書き直す。
3. （←）`y ∈ ball16 h` なら、正典 TCZ の等式（`canonicalLayerTCZ_eq`）で正典 TCZ の元になり、そこから到達時刻 `τ`・到達性・Ω への所属を取り出して、Self の定義の条件を満たすことを示す。

----

<a id="Tomabechi.Consistency.R123.instance@L72"></a>

## インスタンス `instance@L72`

### 式

$$
\text{層 } a \text{ の状態型に、層の添字から決まる可測空間の構造を入れる}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

次の定理を述べるために、層 `a` の状態型 `fullCommonLayerState a` に、`sharedLayerStateMeasurable` による可測空間の構造を与える局所インスタンス（この節の中だけで有効）です。

### 証明の概略

定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_policy_joint_full"></a>

## 定理 `sharedModel_policy_joint_full`

### 式

$$
\text{joint}(\text{問題},\text{方策})\ =\ \bigl(\text{全担体の実験の法則}\bigr)\ \text{の情報周辺}
$$

### Lean のコメント（日本語訳）

> 容量の問題×方策の joint は、担体全体の自己過程を含む実験の情報周辺にも一致する。

### 補題の説明

定理19の容量で使う joint（`policyJoint`）は、担体全体の自己過程を含む実験の法則（`fullExperimentLawFull`）を、必要な成分だけ取り出して（`map`）作った周辺法則に一致します。容量が、実際の実験の情報量と同じものであることの保証です。

### 証明の概略

1. 問題×方策の方策成分が唯一の方策であること（`capPolicy_eq_the_one`）で書き換える。
2. 保存式の `fullExperimentFull_information`（全担体実験の情報周辺）で書き換える。
3. 容量入力の `joint_information`（joint は情報法則）から結論を得る。

----

<a id="Tomabechi.Consistency.R123.SharedP21Supplements"></a>

## 構造体 `SharedP21Supplements`

### 式

$$
\text{Euclid 全 K 誤差（定理1・2・3・4）}\ \wedge\ \text{Self の等号}\ \wedge\ \text{joint の周辺の一致}
$$

### Lean のコメント（日本語訳）

> 三つの小補完を N についての受入型として束ねる。

各フィールドのコメント：

* `euclid1`〜`euclid4`：現行の定理1–4：K 全点の二乗誤差を定理20と同じ Euclid 距離で（\(C=2\)）。
* `full_self_eq`：担体全体の Self は到達和集合から TCZ をちょうど返す。
* `policy_joint_full`：容量 joint と、担体全体の自己過程を含む実験の情報周辺の一致。

### 定義の説明

三つの補完を、共有モデル `N` についての一つの述語にまとめたものです。対象の領域は、定理1・4 は全領域（`fun _ => True`）、定理2 は `domainX3`、定理3 は `domain3` です。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_p21Supplements"></a>

## 定理 `sharedModel_p21Supplements`

### 式

$$
\mathrm{SharedP21Supplements}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`sharedModel` が三つの補完を満たします。

### 証明の概略

1. `euclid1`〜`euclid4`：現行評価の原文前件（`sharedModel_fullOriginalPremisesCurrent`）の、補題0（`lemma0_theorem1`〜`lemma0_theorem4`）に `euclidAllKError` を適用する。
2. `full_self_eq`：`sharedModel_full_self_eq`。
3. `policy_joint_full`：`sharedModel_policy_joint_full`。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v14"></a>

## 定理 `final_consistency_v14`

### 式

$$
\exists N,\ \exists\,\mathrm{sig},\ \mathrm{SharedFinalConsistencyV13}(N,\mathrm{sig})\ \wedge\ \mathrm{SharedP21Supplements}(N)
$$

### Lean のコメント（日本語訳）

> v14：v13 に小補完（現行1–4の Euclid 全K誤差、Self の等号、容量 joint の情報周辺）を同じ `N` で加える。報告範囲は v13 と同じ（層別の独立生成系の読み）。

### 補題の説明

**無矛盾性の代表の存在宣言**です。原文の前提を本プロジェクトで明示的に定式化した条件と、追加の明示条件を、同時に満たす非退化な共有モデル `N` が存在します（Lean／Mathlib の基礎に相対的）。定理16の正典 TCZ を生成する制御系は層別に置いたもので、定理24の制御系とは別です。原文全体を単一の共有制御系で実現したという主張ではありません（[見取り図](Consistency_Overview.md)）。公理は標準の3公理（`propext`・`Classical.choice`・`Quot.sound`）のみです。

### 証明の概略

1. `sharedModel` と `velocityLayerControlSignature` を取る。
2. v13 の述語は `sharedModel_finalConsistencyV13`、三つの補完は `sharedModel_p21Supplements`。

----

## コメント修正記録

`.lean` のコメントの修正はありません（この解説書の作成前に、作業記録への言及を取り除く修正を別に行いました）。
