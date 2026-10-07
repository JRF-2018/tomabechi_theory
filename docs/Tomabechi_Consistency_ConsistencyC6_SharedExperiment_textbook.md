# Tomabechi/Consistency/ConsistencyC6_SharedExperiment.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_SharedExperiment.lean`](../Tomabechi/Consistency/ConsistencyC6_SharedExperiment.lean)（同じ主体・層・制御を観測する、情報と自己過程の実験の法則）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19の**情報**と、定理25の**自己過程**、定理24・1–4 の**制御**を、**同じ主体・層・制御**を観測する一つの「**実験の法則**」にまとめるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品です。

* SCM の外生標本と、情報の標本を、**異なる役割を保ったまま**積の空間に置く。
* 情報の二値の行為 \(g\) を、実際の許容ゲイン（`true`＝最大ゲイン 3、`false`＝ゼロ）に復号し、共通のモデルの実際の軌道を生成する。
* 観測するもの：型つき自己過程・情報行為による状態・同じモデルの走行費。
* **回収**：実験の法則から、元の情報の結合法則と、自己過程のベースライン結合法則を**厳密に**回収できる。復号・再符号化しても一致する。
* **介入不変性**：候補に介入しても、同じ全結合法則を観測する。

### 0.2 このファイルが証明していないこと

* 情報の二値の行為は、許容ゲインの**部分族**（ゼロと最大ゲイン）への復号です。許容族全体を二値に狭めるわけではありません。
* 候補を主体のラベルに使いません。情報の行為を、履歴の出力 \(Y^+\) と同一視しません。
* 物理層（\(k=0\)）は零情報の法則、正の層は元の上位層の法則です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> SCM の外生標本と情報標本は異なる役割を保った積空間に置く。主体 d と履歴 h を context で固定し、情報の行為ラベルは実際の許容ゲインへ復号する。候補を主体ラベルに使わず、情報行為を履歴出力 Y⁺ と同一視しない。物理層の零情報 law を保持し、正層で元の C3 上位 joint を使う。

---

<a id="Tomabechi.Consistency.C6.c6InformationPolicy"></a>

## 定義 `c6InformationPolicy`

### 式

$$
g\mapsto\begin{cases}u_{\max}&g=\text{true}\\u_0&g=\text{false}\end{cases}
$$

### Lean のコメント（日本語訳）

> 情報の二値行為を実際の許容ゲイン0/3へ復号する。この二方策は許容族の部分族であり、族全体を二値へ狭めない。

### 定義の説明

情報の**二値の行為** \(g\) を、**実際の許容ゲイン**（`true` は最大ゲイン 3、`false` はゼロ）に復号します。この二つの方策は、許容ゲインの族の**部分族**で、族の全体を二値に狭めるわけではありません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6InformationPolicy_code"></a>

## 補題 `c6InformationPolicy_code`

### 式

$$
\mathrm{encode}(\text{policy}(g)(t))=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

復号した方策の値を、再び二値の行為に符号化すると、元の \(g\) に戻ります。

### 証明の概略

1. `true`・`false` で場合分けして、ゲインの値（3 か 0）を代入する（`norm_num`）。

----

<a id="Tomabechi.Consistency.C6.c6InformationPolicy_distinct"></a>

## 補題 `c6InformationPolicy_distinct`

### 式

$$
\text{policy}(\text{false})\ne\text{policy}(\text{true})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二つの方策は異なります（行為が区別できる）。

### 証明の概略

1. ゼロゲインと最大ゲインが異なる許容制御であることの補題（`c1_two_distinct_admissible_gains`）。

----

<a id="Tomabechi.Consistency.C6.c6LayerInformationLaw"></a>

## 定義 `c6LayerInformationLaw`

### 式

$$
k\mapsto\begin{cases}\text{物理層の零情報の法則}&k=0\\\text{上位層の法則}&k\ge1\end{cases}
$$

### Lean のコメント（日本語訳）

> 底層の零情報lawと正層の元C3上位law。

### 定義の説明

層 \(k\) の情報の法則です。底の層（\(k=0\)）は**零情報の法則**（物理層）、正の層（\(k\ge1\)）は、段階の谷（C3）の**上位層の法則**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6LayerInformationLaw_probability"></a>

## 補題 `c6LayerInformationLaw_probability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各層の情報の法則は、確率測度です。

### 証明の概略

1. `k = 0` かどうかで場合分けして、それぞれの確率測度性を使う。

----

<a id="Tomabechi.Consistency.C6.c6LayerInformationLaw_stage"></a>

## 補題 `c6LayerInformationLaw_stage`

### 式

$$
\mathrm{Law}(n+1)=\text{上位層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の層の法則は、上位層の法則です。

### 証明の概略

1. `k = 0` でないので、`if` の偽の枝（`simp`）。

----

<a id="Tomabechi.Consistency.C6.C6ExperimentInput"></a>

## 定義 `C6ExperimentInput`

### 式

$$
(\text{SCM の外生標本})\times(\text{情報の標本})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の**入力標本**の型です。SCM の外生標本 \((\text{Bool}\times\text{Bool})\) と、情報の標本 \((\text{Unit}\times\text{Bool}\times\text{Bool})\) を、**異なる役割を保ったまま**積にします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentInputLaw"></a>

## 定義 `c6ExperimentInputLaw`

### 式

$$
\text{外生の法則}\otimes\text{層 }k\text{ の情報の法則}
$$

### Lean のコメント（日本語訳）

> 完全な外生lawと元情報jointを保持する共通実験の標本law。

### 定義の説明

共通の実験の標本の法則です。全層の SCM の**完全な外生法則**と、**元の情報の結合法則**の積です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentInputLaw_probability"></a>

## 補題 `c6ExperimentInputLaw_probability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

標本の法則は確率測度です（確率測度の積）。

### 証明の概略

1. 二つの確率測度の積（型クラスの自動解決）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentInputLaw_scm"></a>

## 補題 `c6ExperimentInputLaw_scm`

### 式

$$
\text{第 1 周辺}=\text{SCM の外生法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

標本の法則の第 1 周辺は、SCM の外生法則に一致します。

### 証明の概略

1. 積測度の第 1 周辺（`map_fst_prod`、確率測度なので全質量 1）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentInputLaw_information"></a>

## 補題 `c6ExperimentInputLaw_information`

### 式

$$
\text{第 2 周辺}=\text{情報の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

標本の法則の第 2 周辺は、情報の法則に一致します。

### 証明の概略

1. 積測度の第 2 周辺（`map_snd_prod`）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentState"></a>

## 定義 `c6ExperimentState`

### 式

$$
\text{情報行為が生成する、共通のモデル D の実軌道}
$$

### Lean のコメント（日本語訳）

> 同じ情報行為が共通Dの実軌道を生成する。

### 定義の説明

標本の情報の行為（二値）を、実際の許容ゲインに復号し、それで動かした**共通のモデルの実軌道**です（層 \(k\)、初期状態 \(x\)、開始時刻 \(T\)、時刻 \(t\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6ExperimentObservation"></a>

## 定義 `C6ExperimentObservation`

### 式

$$
\text{標本}\times\text{型つき自己過程}\times\text{状態}\times\text{走行費}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の**観測**の型です。元の標本、型つき自己過程の観測、情報行為が作る状態、同じモデルの走行費を、組にして持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentObservation"></a>

## 定義 `c6ExperimentObservation`

### 式

$$
w\mapsto\bigl(w,\ \text{自己過程のベースライン},\ \text{状態},\ \text{走行費}\bigr)
$$

### Lean のコメント（日本語訳）

> 同じcontextの型付き自己過程、情報行為による状態、同じDの走行費を同時に観測する。元標本も保持するので、主体/候補/行為を別の役割へ取り替えていないことを検査できる。

### 定義の説明

同じ文脈（主体 \(d\)・履歴 \(h\)）の**型つき自己過程**、情報行為による**状態**、同じモデルの**走行費**を、同時に観測します。元の標本も保持するので、主体・候補・行為を別の役割に取り替えていないことを、検査できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentLaw"></a>

## 定義 `c6ExperimentLaw`

### 式

$$
\text{標本の法則を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の法則です。標本の法則を、観測写像で押し出したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentLaw_probability"></a>

## 補題 `c6ExperimentLaw_probability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実験の法則は確率測度です。

### 証明の概略

1. 確率測度の像（可測写像による押し出しは確率測度）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentLaw_information"></a>

## 補題 `c6ExperimentLaw_information`

### 式

$$
\text{情報の周辺}=\text{元の情報の法則}
$$

### Lean のコメント（日本語訳）

> 情報の元jointを、制御状態/自己過程を付加した法則から厳密に回収する。

### 補題の説明

制御の状態と自己過程を付加した実験の法則から、**元の情報の結合法則を厳密に回収**できます。

### 証明の概略

1. 像の合成（`Measure.map_map`）で、第 1 成分の第 2 成分を取る写像と観測写像を合成すると、標本の第 2 成分を取る写像になる。
2. 標本の法則の第 2 周辺の補題（`c6ExperimentInputLaw_information`）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentLaw_selfProcess"></a>

## 補題 `c6ExperimentLaw_selfProcess`

### 式

$$
\text{自己過程の周辺}=\text{自己過程のベースライン joint}
$$

### Lean のコメント（日本語訳）

> 自己過程の同じbaseline jointを、情報/制御状態付き法則から厳密に回収する。

### 補題の説明

情報と制御の状態を付加した実験の法則から、**自己過程の同じベースライン結合法則を厳密に回収**できます。

### 証明の概略

1. 像の合成で、実験の法則の自己過程の成分を取る写像は、標本の第 1 成分（外生標本）にベースラインの式を合成したものになる。
2. 標本の法則の第 1 周辺は SCM の外生法則（`c6ExperimentInputLaw_scm`）。

----

<a id="Tomabechi.Consistency.C6.c6Experiment_subject_coordinate"></a>

## 補題 `c6Experiment_subject_coordinate`

### 式

$$
\text{主体 }d\text{ の状態}=\text{二主体の }d\text{ 番目の座標}
$$

### Lean のコメント（日本語訳）

> 実験の主体dは同じFin 2主体座標へ復号される。情報goalで主体を置換しない。

### 補題の説明

実験の主体 \(d\) は、二主体の座標（`Fin 2`）の対応する座標へ復号されます。情報のゴールで主体を取り替えることはしません。

### 証明の概略

1. 有限の主体の状態の見方（`c6FiniteSubjectStateView`）を、定義から展開して一致を示す。

----

<a id="Tomabechi.Consistency.C6.c6Experiment_cost"></a>

## 補題 `c6Experiment_cost`

### 式

$$
\text{費用}=1+8\,d^2
$$

### Lean のコメント（日本語訳）

> 費用は同じ実制御状態の層別二次評価。lawから独立した定数費用を付加していない。

### 補題の説明

費用は、同じ実際の制御状態の、層ごとの二次評価 \(1+8\,(\text{差の半分})^2\) です。法則とは独立な定数の費用を付加してはいません。

### 証明の概略

1. 定義から（`rfl`）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentLaw_actualPolicyInformation"></a>

## 補題 `c6ExperimentLaw_actualPolicyInformation`

### 式

$$
\text{復号→再符号化した joint}=\text{元の情報の joint}
$$

### Lean のコメント（日本語訳）

> 情報行為を実入力へ復号し再符号化したjointも、元の情報jointと完全に一致する。数値スコアの一致だけで制御の意味対応を済ませない。

### 補題の説明

情報の行為を、実際の入力（許容ゲイン）へ**復号し、再び符号化**した結合法則も、元の情報の結合法則と**完全に一致**します。数値のスコアが一致するだけで、制御の意味の対応を済ませてはいません。

### 証明の概略

1. 前の補題で、情報の周辺は元の情報の法則。
2. 復号・再符号化の補題（`c6InformationPolicy_code`）で、行為の成分が元に戻ることを示す。

----

<a id="Tomabechi.Consistency.C6.c6InformationPolicy_optimal"></a>

## 補題 `c6InformationPolicy_optimal`

### 式

$$
\text{policy}(\text{true})=\text{最適方策}
$$

### Lean のコメント（日本語訳）

> 情報行為trueは、同じ有限層Dの実最適方策を指定する。

### 補題の説明

情報の行為 `true` は、同じ有限層の**実際の最適方策**（最大ゲイン）を指定します。

### 証明の概略

1. 最適方策の定義（最大ゲイン）と一致する（`rfl`）。

----

<a id="Tomabechi.Consistency.C6.c6ExperimentIntervenedObservation"></a>

## 定義 `c6ExperimentIntervenedObservation`

### 式

$$
w\mapsto\bigl(w,\ \text{自己過程の介入した式},\ \text{状態},\ \text{走行費}\bigr)
$$

### Lean のコメント（日本語訳）

> 候補介入にも同じ情報行為・制御状態・費用観測を用いる。

### 定義の説明

候補への介入にも、同じ情報行為・同じ制御状態・同じ費用の観測を使います。ベースラインの式を、介入した式に替えたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6Experiment_intervention_invariance"></a>

## 補題 `c6Experiment_intervention_invariance`

### 式

$$
\text{介入後の joint}=\text{ベースラインの joint}
$$

### Lean のコメント（日本語訳）

> 候補と情報行為は異なる役割であり、候補介入後も同じ全jointを観測する。元SCMの候補非干渉からpointwise一致するこの具体モデルの結論。

### 補題の説明

候補と情報の行為は**異なる役割**で、候補に介入した後でも、**同じ全体の結合法則**を観測します。この具体モデルでは、元の SCM の候補の非干渉から、各点で一致するので、定義から成り立ちます。

### 証明の概略

1. 定義から（`rfl`）。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
