# Tomabechi/Consistency/ConsistencyR1_C6CommonConceptSCM.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C6CommonConceptSCM.lean`](../Tomabechi/Consistency/ConsistencyR1_C6CommonConceptSCM.lean)（共通束全体の上の、定理25の SCM（同じ外生法則））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理25の SCM（構造的因果モデル）を、**共通束 `CommonConcept` の全体**の上に、**同じ外生法則・履歴・候補**のまま直接構成するファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）の部品です。既存の全層 SCM（共通層 `WithTop ℕ` の上のもの）を新しい束の層の型に**読み替えるだけではなく**、`CommonConcept` を層の型とする測度つき C3 モデルを構成します。

* 全点で、同じ非空のプロファイルと、履歴に依存する関係の辺。\(\Gamma\)（関係的状態）は、履歴ごとの固定点の符号から回収。
* **全点で自己（アートマン）が存在しない**。候補の各値は正の質量。
* 型つき自己過程（Self・Ego・TCZ）と、条件 25-A(2)。
* **旧い二層への制限**：外生法則・履歴・候補は元と同じで、旧アドレスの介入結合法則は、制限して**完全に回収**できる。

### 0.2 このファイルが証明していないこと

* 全点で同じプロファイル・関係を持つ、具体的なモデルです。点ごとに異なる関係の構造を持たせたものではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 既存の全層 SCM を新束上の層型へ単に読み替えるのではなく、CommonConcept を層型とする測度付き C3 モデルを直接構成する。外生 law・履歴・候補変数は元の定理25モデルと同じものを使う。

---

<a id="Tomabechi.Consistency.R1.CommonConceptGamma"></a>

## 定義 `CommonConceptGamma`

### 式

$$
\text{共通束全体の関係的状態 }\Gamma
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束 `CommonConcept` **全体**を層の型とする、関係的状態 \(\Gamma\) の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.instance@L22"></a>

## インスタンス `instance@L22`

### 式

$$
\text{最大の可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(\Gamma\) の型に、最大の可測空間の構造（すべての部分集合が可測）を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptPresence"></a>

## 定義 `commonConceptPresence`

### 式

$$
\text{全共通概念点で、同じ非空のプロファイルと、履歴依存の関係の辺}
$$

### Lean のコメント（日本語訳）

> 全ての共通概念点で同じ非空profileと履歴依存の関係辺を持つ。

### 定義の説明

共通束の**すべての点**で、同じ非空のプロファイルと、履歴に依存する関係の辺を持つ「存在と関係」のモデルです（全層に現前するので、支持は非空で上に閉じている）。

### 証明の概略

1. 各フィールドに定義を与える。支持の非空性は頂が入ること、関係の辺の反転の条件は場合分けで示す（共通層全体の SCM のファイルと同様）。

----

<a id="Tomabechi.Consistency.R1.commonConceptStateCode"></a>

## 定義 `commonConceptStateCode`

### 式

$$
x\mapsto\mathrm{relationalState}(d,[x_0=1],a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

逆極限の点 \(x\) の符号です。第 0 座標が 1 かで履歴を決め、その履歴の関係的状態を返します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptStateCode_matches"></a>

## 補題 `commonConceptStateCode_matches`

### 式

$$
\text{固定点の符号}=\mathrm{relationalState}(d,h,a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴 \(h\) の固定点を符号化すると、その履歴の関係的状態に一致します。

### 証明の概略

1. 固定点の第 0 座標の値を使い、履歴の二値で場合分けして計算する。

----

<a id="Tomabechi.Consistency.R1.commonConceptGamma_event"></a>

## 補題 `commonConceptGamma_event`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\Gamma\) の観測についての事象は、すべて可測です。

### 証明の概略

1. \(\Gamma\) の型は最大の可測空間。第 1 成分への射影は可測。

----

<a id="Tomabechi.Consistency.R1.commonConceptMeasuredC3Model"></a>

## 定義 `commonConceptMeasuredC3Model`

### 式

$$
\text{共通束全点で、定理25の測度つき C3 の一般入口を満たすモデル}
$$

### Lean のコメント（日本語訳）

> CommonConcept全点で定理25の測度付きC3一般入口を満たすモデル。

### 定義の説明

共通束の**全点**で、定理25の**測度つき C3 の一般入口**を満たすモデルです。既存の全層 SCM を新しい束の層の型に読み替えるのではなく、`CommonConcept` を層の型とするモデルを**直接構成**します。外生法則・履歴・候補の変数は、元の定理25のモデルと同じものです。

### 証明の概略

1. 履歴の固定点から C3 モデルを作る一般の構成（`ofHistoryFixedPoints`）に、固定点・全点の関係モデル・符号・符号の一致・出力・元の外生法則・履歴・候補を渡す。

----

<a id="Tomabechi.Consistency.R1.commonConceptSCM_output_eq_history"></a>

## 補題 `commonConceptSCM_output_eq_history`

### 式

$$
\text{出力}=h
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

SCM の出力は、履歴 \(h\) そのものです（候補に依らない）。

### 証明の概略

1. 出力は「固定点の第 0 座標が 1 か」。履歴で場合分けして固定点の座標を代入する。

----

<a id="Tomabechi.Consistency.R1.commonConceptMeasuredC3Model_noAtman"></a>

## 補題 `commonConceptMeasuredC3Model_noAtman`

### 式

$$
\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)
$$

### Lean のコメント（日本語訳）

> 定理25の「自己（アートマン）の不在」の結論を、新しい共通束のすべての点に、このモデル自身の測度つき SCM を使って適用する。

### 補題の説明

定理25の「自己（アートマン）の不在」の結論が、**新しい共通束のすべての点**で、このモデル自身の測度つき SCM を使って成り立ちます。

### 証明の概略

1. 出力が候補に依らない（a.e.）ことから、一般の入口（`..._outputAENoninterference`）を適用する。

----

<a id="Tomabechi.Consistency.R1.commonConceptMeasuredC3Model_candidate_positive"></a>

## 補題 `commonConceptMeasuredC3Model_candidate_positive`

### 式

$$
\text{候補の各値は正の質量を持つ}
$$

### Lean のコメント（日本語訳）

> 各候補の値は、元の外生法則のもとで、共通束の全体にわたって一様に、零集合にならない。

### 補題の説明

候補の各値は、元の外生法則のもとで、共通束の全体で一様に、**正の質量**を持ちます。

### 証明の概略

1. 候補は元の SCM と同じ。元の SCM の正の質量の補題を使う。

----

<a id="Tomabechi.Consistency.R1.commonConceptTypedObservation"></a>

## 定義 `commonConceptTypedObservation`

### 式

$$
(\Gamma,h)\mapsto((\Gamma,R(h)),h)
$$

### Lean のコメント（日本語訳）

> 実際の C4 の Self・Ego・TCZ の表現を、共通束の Γ と同じ SCM の出力に付加する。外生の源も候補も変えない。

### 定義の説明

共通束の \(\Gamma\) と同じ SCM の出力に、**実際の C4 の Self・Ego・TCZ の表現**を付加する観測です。外生の源も候補も変えません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptTypedObservation_measurable"></a>

## 補題 `commonConceptTypedObservation_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測は可測です。

### 証明の概略

1. 各成分の可測性を合わせる。

----

<a id="Tomabechi.Consistency.R1.commonConceptTypedSelfProcess"></a>

## 定義 `commonConceptTypedSelfProcess`

### 式

$$
\text{各共通概念点での、同じ法則の型つき自己過程}
$$

### Lean のコメント（日本語訳）

> 各共通概念の点での、同じ法則の型つき自己過程。

### 定義の説明

各共通概念の点での、**同じ法則**の型つき自己過程です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptTypedSelfProcess_satisfies25A2"></a>

## 補題 `commonConceptTypedSelfProcess_satisfies25A2`

### 式

$$
\text{25-A(2)}
$$

### Lean のコメント（日本語訳）

> 25-A2はCommonConcept全点で元と同じ外生law上の独立性を満たす。

### 補題の説明

条件 25-A(2) は、共通束の**全点**で、元と同じ外生法則の上の独立性を満たします。

### 証明の概略

1. 候補と履歴の独立性（一様分布の積測度の二つの座標）。出力が候補に依らない。

----

<a id="Tomabechi.Consistency.R1.commonConceptTypedSelfProcess_representation"></a>

## 補題 `commonConceptTypedSelfProcess_representation`

### 式

$$
\text{介入観測}=(\mathrm{relationalState},\ R(h))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入観測は、関係的状態と、履歴の三つの表現の組です。

### 証明の概略

1. 第 1 成分は符号の補題、第 2 成分は三つの表現の取得。

----

<a id="Tomabechi.Consistency.R1.restrictCommonConceptGamma"></a>

## 定義 `restrictCommonConceptGamma`

### 式

$$
\Gamma\mapsto\Gamma|_{\text{元の Bool 二層}}
$$

### Lean のコメント（日本語訳）

> Γを元のBool二層観測へ制限する。

### 定義の説明

共通束の \(\Gamma\) を、もとの `Bool` の二つの層の観測へ**制限**する写像です（アドレスの埋め込みで、プロファイル・縦の近傍・辺を引き戻す）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptState_restricts_old"></a>

## 補題 `commonConceptState_restricts_old`

### 式

$$
\text{制限した状態の式}=\text{元の状態の式}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の SCM の状態の式を、元の二層に制限すると、元の状態の式に一致します。

### 証明の概略

1. 符号の式を展開し、制限と関係的状態の補題で一致を示す。

----

<a id="Tomabechi.Consistency.R1.commonConceptSCM_source_law_and_history"></a>

## 補題 `commonConceptSCM_source_law_and_history`

### 式

$$
\text{外生法則・履歴は元と同じ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の SCM の外生法則・履歴は、元の定理25のモデルと同じです。

### 証明の概略

1. 同じ定義から作ったので `rfl`。

----

<a id="Tomabechi.Consistency.R1.commonConceptSCM_candidate_matches_old"></a>

## 補題 `commonConceptSCM_candidate_matches_old`

### 式

$$
\text{候補の変数は元と同じ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

候補の変数も、元のモデルのものと同じです。

### 証明の概略

1. 同じ定義から作ったので `rfl`。

----

<a id="Tomabechi.Consistency.R1.commonConceptSCM_intervenedJoint_restricts_old"></a>

## 補題 `commonConceptSCM_intervenedJoint_restricts_old`

### 式

$$
\text{旧アドレスの介入 joint は、制限して回収できる}
$$

### Lean のコメント（日本語訳）

> 旧いアドレスの介入結合法則は、すべて、Γ を制限したあとに回収される。等式は、状態と出力の両方の座標を含み、同じ元の外生法則のもとで成り立つ。

### 補題の説明

旧いアドレスでの介入結合法則は、すべて、\(\Gamma\) を制限すれば回収できます。等式は、状態と出力の**両方の座標**を含み、同じ元の外生法則のもとで成り立ちます。

### 証明の概略

1. 像の合成（`map_map`）で制限と状態・出力の式を合成し、状態の制限の補題（`commonConceptState_restricts_old`）と出力が履歴であることから、元の式に一致させる。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
