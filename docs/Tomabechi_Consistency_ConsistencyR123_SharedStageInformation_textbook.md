# Tomabechi/Consistency/ConsistencyR123_SharedStageInformation.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedStageInformation.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedStageInformation.lean)（共有署名の平均場の段階と、直接 KL の情報量）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**平均場の段階**（H-stage）と、**直接の KL による情報量**を、同じ \(N\) の上で結ぶファイルです。平均場の段階の入力の全解析前件と、同じ平均場の支持・枝・LUB の対応を使い、情報の結合法則は、同じ `N.informationLaw` の**段の住所**に同定して、定理21の四つの結論を保持します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「段階の谷と情報」（C3）の、共有署名への接続です。

### 0.2 このファイルが証明していないこと

* 具体的な共有署名（`sharedModel`）についての構成です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> MeanFieldStageInput の全解析前件と同じ平均場の支持/枝/LUB 対応を使う。情報 joint は同じ N.informationLaw の段住所に同定し、21の四結論を保持する。

---

<a id="Tomabechi.Consistency.R123.sharedStageBranch"></a>

## 定義 `sharedStageBranch`

### 式

$$
\text{branch}=\text{symbolSupport}=\{U_n\}
$$

### Lean のコメント（日本語訳）

> 同じ共通束の真部分住所を支持とする情報枝。

### 定義の説明

同じ共通束の、頂より下の**真部分の住所**を支持とする、情報の枝です（定理21の枝の文脈）。枝と記号の台は、段 \(n\) の住所 \(U_n\) の一点集合です。

### 証明の概略

1. 非空。頂は枝に入らない（住所は頂より下）。台の最小上界は台自身。

----

<a id="Tomabechi.Consistency.R123.SharedStageInformationInputs"></a>

## 構造体 `SharedStageInformationInputs`

### 式

$$
\text{N の実平均場の提示と、同じ共通束の枝を結ぶ全前件}
$$

### Lean のコメント（日本語訳）

> Nの実平均場presentationと同じ共通束枝を結ぶ全前件。

### 定義の説明

\(N\) の**実際の平均場の提示**と、同じ共通束の枝を結ぶ、全前件です。フィールドは、段の住所での情報の法則が上位の結合法則であること、原子から共通束への表象（忠実・単調）、枝・台の対応、頂・LUB の対応です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageInformationInputs.theorem21"></a>

## 定義 `SharedStageInformationInputs.theorem21`

### 式

$$
\text{定理21の四つの結論（段 }n\text{）}
$$

### Lean のコメント（日本語訳）

> N.stagesの解析前件と支持前件を21の一般入口に直接渡す。

### 定義の説明

\(N\) の段の解析的な前件と、台の前件を、定理21の一般の入口に**直接渡します**（直接の KL による条件付き相互情報量の入口）。

### 証明の概略

1. 定理21の入口（`meanField_stage_theorem21_four_conclusions_directKL`）に、段・枝・Dirac 測度・質量・行為・原子の列・表象とその性質を渡す。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem22"></a>

## 定義 `SharedModelSignature.theorem22`

### 式

$$
\text{全谷・指数軌道の一般入口}
$$

### Lean のコメント（日本語訳）

> 同じ段列へ22の全谷・指数軌道一般入口を適用する。

### 定義の説明

同じ段の列に、定理22の「**全段の谷と指数軌道**」の一般の入口を適用します。

### 証明の概略

1. `all_mean_field_stages_have_global_valley_orbits` に `N.stages` を渡す。

----

<a id="Tomabechi.Consistency.R123.sharedModel_stageInformationInputs"></a>

## 定義 `sharedModel_stageInformationInputs`

### 式

$$
\mathrm{SharedStageInformationInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 共通束上の忠実な旧原子埋込みが具体平均場の枝対応を満たす。

### 定義の説明

共通束の上の**忠実な旧原子の埋め込み**が、具体的な平均場の枝の対応を満たします。

### 証明の概略

1. 表象は `layerAddressEmbedding`（単射・単調）、頂は頂に写る。
2. 段の情報の法則は上位の結合法則（保存式と追加条件）。枝・台・LUB は、原子 \(n+1\) の埋め込みが住所 \(U_n\) に等しいことから。

----

<a id="Tomabechi.Consistency.R123.SharedStageInformationInputs.cmiScore"></a>

## 定義 `SharedStageInformationInputs.cmiScore`

### 式

$$
\mathrm{KL}(\text{joint}\,\|\,\text{ref})\text{（段住所の情報法則）}
$$

### Lean のコメント（日本語訳）

> 同じNの段住所情報lawを読む直接KL型CMI。

### 定義の説明

同じ \(N\) の、段の住所での情報の法則を読んで計算する、**直接の KL 型の条件付き相互情報量**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageInformationInputs.cmiScore_eq_entropy"></a>

## 補題 `SharedStageInformationInputs.cmiScore_eq_entropy`

### 式

$$
\text{score}=H(G\mid X)>0
$$

### Lean のコメント（日本語訳）

> 21の第4結論は別lawのスコアではなくN自身のjointで成立する。

### 補題の説明

定理21の第 4 の結論（情報の結論）は、別の法則のスコアではなく、**\(N\) 自身の結合法則**で成り立ちます。スコアは条件付きゴールエントロピーに等しく、正です。

### 証明の概略

1. 定理21の結論から、情報の結論（スコア \(=\) ゴールのエントロピー）を取り出す。
2. 結合法則が上位の結合法則（`joint`）なので、同じ値。ゴールのエントロピーは正（`inputEntropy_pos`）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
