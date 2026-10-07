# Tomabechi/Consistency/ConsistencyR123_FullExperiment.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FullExperiment.lean`](../Tomabechi/Consistency/ConsistencyR123_FullExperiment.lean)（共通束の全点での、実際の情報・自己過程・状態費用の結合法則）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の、**共通束の全点**での、実際の**情報・自己過程・状態費用の結合法則**を作るファイルです。実験の層は `CommonConcept` 全体を走ります。非埋め込みの点でも `N.data` の同じ層を使い、頂点では頂点のベクトル状態・方策の型を保ちます。情報の二値の行為から実際の方策への**復号の族**は、引数で明示します。

### 0.2 このファイルが証明していないこと

* 「すべての復号の族」についての結果だけでは、復号の族の**存在・許容性**は証明しません（それは別のファイルで与えます）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 実験の層は CommonConcept 全体を走る。非埋込み点でも N.data の同じ層を使い、頂点では頂点のベクトル状態・方策型を保つ。情報の二値行為から実方策への復号族は引数で明示する。全復号族に対する結果だけでは、復号族の存在・許容性を証明しない。

---

<a id="Tomabechi.Consistency.R123.sharedLayerStateMeasurable"></a>

## 定義 `sharedLayerStateMeasurable`

### 式

$$
\text{各層の状態の元の可測構造}
$$

### Lean のコメント（日本語訳）

> 各層の実数二座標/Euclidean状態の元の可測構造を使用する。

### 定義の説明

各層の状態（実数の二座標、または Euclid の状態）の、**元の可測構造**を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L22"></a>

## インスタンス `instance@L22`

### 式

$$
\text{共通束の各点の状態型は可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の各点の状態の型に、可測空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedInformationDecoder"></a>

## 定義 `SharedInformationDecoder`

### 式

$$
\forall a,\ \mathrm{Bool}\to\text{層 }a\text{ の方策}
$$

### Lean のコメント（日本語訳）

> 二値情報行為を、各層の全方策族の中の二方策へ復号する。

### 定義の説明

二値の情報の行為を、各層の全方策の族の中の**二つの方策**に復号する写像の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.FullExperimentObservation"></a>

## 定義 `FullExperimentObservation`

### 式

$$
\text{標本}\times((\Gamma,R),h)\times(\text{層 }a\text{ の状態},\text{費用})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の点 \(a\) での実験の観測の型です（状態の型は層 \(a\) のもの）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentInputLaw"></a>

## 定義 `SharedModelSignature.fullExperimentInputLaw`

### 式

$$
\text{外生の法則}\otimes N.\mathrm{informationLaw}(a)
$$

### Lean のコメント（日本語訳）

> 外生標本と情報lawは同じNと同じ共通束点を読む。

### 定義の説明

外生の標本と情報の法則は、同じ \(N\) の、同じ共通束の点を読みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentObservation"></a>

## 定義 `SharedModelSignature.fullExperimentObservation`

### 式

$$
w\mapsto(w,\ \text{自己過程},\ \text{状態},\ \text{費用})
$$

### Lean のコメント（日本語訳）

> 同じ層・同じ情報方策による実状態と実走行費を保持する。

### 定義の説明

同じ層・同じ情報の方策による、**実際の状態と実際の走行費**を保持する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperimentLaw"></a>

## 定義 `SharedModelSignature.fullExperimentLaw`

### 式

$$
\text{標本の法則を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の全点での実験の法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullInformation_probability"></a>

## 補題 `SharedDataPreservation.fullInformation_probability`

### 式

$$
\text{全点で情報の法則は確率測度}
$$

### Lean のコメント（日本語訳）

> 全共通束点で情報lawは確率法則。物理層のみ零情報の別lawを使う。

### 補題の説明

共通束の全点で、情報の法則は確率測度です（物理層だけは零情報の別の法則を使う）。

### 証明の概略

1. 情報の保存式で、署名の情報の法則（番号）に書き換え、番号で場合分け（物理層・上位層）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperiment_probability"></a>

## 補題 `SharedDataPreservation.fullExperiment_probability`

### 式

$$
\text{実験は確率 joint}
$$

### Lean のコメント（日本語訳）

> 全点・全初期状態・全時刻・全復号族の実験は確率jointである。

### 補題の説明

全点・全初期状態・全時刻・全復号族の実験は、確率の結合法則です。

### 証明の概略

1. 情報の法則が確率測度（前の補題）。積測度と押し出しも確率測度。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperiment_stateCost"></a>

## 補題 `SharedModelSignature.fullExperiment_stateCost`

### 式

$$
\text{状態・費用の周辺}
$$

### Lean のコメント（日本語訳）

> 実状態・走行費の周辺。評価値だけでなく同じ実軌道も残す。

### 補題の説明

実際の状態・走行費の周辺です。評価値だけでなく、同じ実際の軌道も残します。

### 証明の概略

1. 像の合成（`map_map`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullExperiment_input"></a>

## 補題 `SharedModelSignature.fullExperiment_input`

### 式

$$
\text{標本の周辺}=\text{入力の法則}
$$

### Lean のコメント（日本語訳）

> 元標本lawを回収する。標本保持により全周辺が同一jointに属する。

### 補題の説明

元の標本の法則を回収します。標本を保持するので、すべての周辺が同一の結合法則に属します。

### 証明の概略

1. 像の合成。恒等写像の像。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperiment_information"></a>

## 補題 `SharedDataPreservation.fullExperiment_information`

### 式

$$
\text{情報の周辺}=N.\mathrm{informationLaw}(a)
$$

### Lean のコメント（日本語訳）

> 全点の情報周辺は同じ住所のN.informationLawそのもの。

### 補題の説明

全点の情報の周辺は、同じ住所の `N.informationLaw` **そのもの**です。

### 証明の概略

1. 積測度の第 2 周辺（`map_snd_prod`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperiment_selfProcess"></a>

## 補題 `SharedDataPreservation.fullExperiment_selfProcess`

### 式

$$
\text{自己過程の周辺を回収}
$$

### Lean のコメント（日本語訳）

> 全点のnative Γ・三表現・出力の自己過程周辺を回収する。

### 補題の説明

全点の、**元の \(\Gamma\)・三つの表現・出力**の自己過程の周辺を回収します。

### 証明の概略

1. 像の合成で、自己過程の成分は外生標本の関数。積測度の第 1 周辺は外生法則。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fullIntervenedExperimentObservation"></a>

## 定義 `SharedModelSignature.fullIntervenedExperimentObservation`

### 式

$$
\text{介入時の観測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

介入のときの、共通束の点 \(a\) での観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.fullExperiment_intervention"></a>

## 補題 `SharedKernelInputs.fullExperiment_intervention`

### 式

$$
\text{共通束の全点で、候補への介入は実験の結合法則全体を保つ}
$$

### Lean のコメント（日本語訳）

> 全共通束点で候補介入は実験joint全体を保つ。外生law上のa.e.非干渉を積lawの外生周辺から移す。

### 補題の説明

共通束の全点で、**候補への介入は、実験の結合法則の全体を保ちます**。外生の法則の上のほとんど至る所の非干渉を、積の法則の外生の周辺から移します。

### 証明の概略

1. 積測度の第 1 周辺が外生法則（`map_fst_prod`）。外生の法則の上で、出力が候補に依らない（a.e.）。
2. 観測の各成分（状態・費用・自己過程）が、介入に依らないことを示して、`map_congr`。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
