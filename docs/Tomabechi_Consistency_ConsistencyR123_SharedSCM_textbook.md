# Tomabechi/Consistency/ConsistencyR123_SharedSCM.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedSCM.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedSCM.lean)（共有署名の SCM・介入の結合法則・型つき自己過程）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の **SCM・介入の結合法則・型つき自己過程**を扱うファイルです。共通束の \(\Gamma\) の全体を保持し、旧い層のアドレスでの観測の回収には、全プロファイル・近傍・関係の辺の**制限**を使います。共通束のすべての点では、`N.scm` 自身から自己過程を生成します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「自己意識の固定点」（C4）・定理25の、共有署名への接続です。

* 旧い層のアドレスでは、\(\Gamma\) を制限すると旧い共有束の関係的状態に一致します。
* 構造式（状態・候補・出力）の一致から、**介入結合法則・ベースライン結合法則を、旧い署名のものに完全に回収**できます。
* **型つき自己過程**：三つの表現を付加。条件 25-A(2) を**共通束の全点**で得る。回収は三つの表現・\(\Gamma\)・出力のすべてを保つ。

### 0.2 このファイルが証明していないこと

* 具体的な共有署名（`sharedModel`）についての構造式の一致です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通束の Γ 全体を保持し、旧層アドレスの観測回収には全 profile・近傍・関係辺の制限を使う。全共通束点では N.scm 自身から自己過程を生成する。

---

<a id="Tomabechi.Consistency.R123.sharedRestrictGamma"></a>

## 定義 `sharedRestrictGamma`

### 式

$$
\Gamma\mapsto\Gamma|_{\text{旧層アドレス}}
$$

### Lean のコメント（日本語訳）

> 共通束のΓを全旧層アドレスへ制限する。

### 定義の説明

共通束の \(\Gamma\) を、すべての**旧い層のアドレス**に制限する写像です（プロファイル・縦の近傍・入出の辺を、埋め込みで引き戻す）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedRestrictGamma_relationalState"></a>

## 補題 `sharedRestrictGamma_relationalState`

### 式

$$
\text{旧アドレスでは、制限した関係的状態}=\text{旧共有束の関係的状態}
$$

### Lean のコメント（日本語訳）

> 旧アドレスではΓの全構成成分が旧共有束の同じ関係的状態に一致する。

### 補題の説明

旧いアドレスでは、\(\Gamma\) の**すべての構成成分**（プロファイル・縦の近傍・辺）が、旧い共有束の同じ関係的状態に一致します。

### 証明の概略

1. 関係的状態の定義を展開し、プロファイル・近傍・辺の各成分を比べる（`ext`・`funext`）。共通束の「存在と関係」と旧い全層のそれとは同じ定義。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings"></a>

## 構造体 `SharedSCMCouplings`

### 式

$$
\text{旧層の回収に必要な構造式（状態・候補・出力）}
$$

### Lean のコメント（日本語訳）

> Nの旧層回収に必要な構造式。分布の各周辺だけの一致には弱めない。

### 定義の説明

\(N\) の旧い層の回収に必要な**構造式の一致**です。分布の各周辺だけの一致に弱めません。フィールドは、保存式、状態の式（\(\Gamma\) を制限すると旧の状態の式に一致）、候補の式の一致、出力の式の一致です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_scmCouplings"></a>

## 定理 `sharedModel_scmCouplings`

### 式

$$
\mathrm{SharedSCMCouplings}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 同じ具体共有署名に全旧層SCM保存式を供給する。

### 補題の説明

同じ具体的な共有署名に、全ての旧層の SCM の保存式を供給します。

### 証明の概略

1. 状態の式：符号の補題（`commonConceptStateCode_matches`・`c6FullLayerStateCode_matches`）と制限の補題（`sharedRestrictGamma_relationalState`）。
2. 候補・出力の式：定義から（`rfl`）か、出力が履歴であること。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.intervenedJoint"></a>

## 補題 `SharedSCMCouplings.intervenedJoint`

### 式

$$
\text{共通束の介入 joint を制限すると、旧署名の介入 joint}
$$

### Lean のコメント（日本語訳）

> 同じNの介入joint全体を旧署名の同じ層へ厳密に回収する。

### 補題の説明

同じ \(N\) の**介入結合法則の全体**を、旧い署名の同じ層へ、**厳密に回収**できます。

### 証明の概略

1. 外生法則が同じ（保存式 `scm_law`）。像の合成（`map_map`）で、制限と状態・出力の式を合成し、構造式の一致で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.baselineJoint"></a>

## 補題 `SharedSCMCouplings.baselineJoint`

### 式

$$
\text{共通束のベースライン joint を制限すると、旧署名のもの}
$$

### Lean のコメント（日本語訳）

> 同じNの基準jointも同じ観測写像で全回収する。

### 補題の説明

同じ \(N\) の**ベースラインの結合法則**も、同じ観測写像で、全体を回収できます。

### 証明の概略

1. 介入結合法則の補題と同様。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservation"></a>

## 定義 `SharedModelSignature.typedObservation`

### 式

$$
(\Gamma,h)\mapsto((\Gamma,R(h)),h)
$$

### Lean のコメント（日本語訳）

> Nに格納した三表現を、N.scmのΓと出力へ付加する。

### 定義の説明

\(N\) に格納した**三つの表現**（Self・Ego・TCZ）を、`N.scm` の \(\Gamma\) と出力に付加する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservation_measurable"></a>

## 補題 `SharedModelSignature.typedObservation_measurable`

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

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfProcess"></a>

## 定義 `SharedModelSignature.selfProcess`

### 式

$$
\text{全主体・全共通束点で、同じ N.scm から生成する型つき自己過程}
$$

### Lean のコメント（日本語訳）

> 全主体・全共通束点で、同じN.scmから生成する型付き自己過程。

### 定義の説明

全主体・全共通束の点で、**同じ `N.scm` から生成する**、型つきの自己過程です（外生法則・履歴・候補は `N.scm` のもの）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.selfProcess25A2"></a>

## 補題 `SharedKernelInputs.selfProcess25A2`

### 式

$$
\text{25-A(2)（全共通束点）}
$$

### Lean のコメント（日本語訳）

> 同じNの実非干渉入力から、型付き自己過程の25-A2を全共通束点で得る。

### 補題の説明

同じ \(N\) の実際の非干渉の入力（出力が候補に依らない）から、型つき自己過程の条件 25-A(2) を、**共通束の全点**で得ます。

### 証明の概略

1. 候補が全体の文脈と独立（SCM の性質）。
2. 介入観測とベースライン観測の法則が一致（出力が候補に依らない a.e. から）。

----

<a id="Tomabechi.Consistency.R123.sharedRestrictTypedObservation"></a>

## 定義 `sharedRestrictTypedObservation`

### 式

$$
((\Gamma,R),h)\mapsto((\Gamma|,R),h)
$$

### Lean のコメント（日本語訳）

> 三表現を保ったままΓだけを旧層へ制限する。

### 定義の説明

三つの表現を保ったまま、\(\Gamma\) だけを旧い層に制限する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedRestrictTypedObservation_measurable"></a>

## 補題 `sharedRestrictTypedObservation_measurable`

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

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.selfProcess_intervenedJoint"></a>

## 補題 `SharedSCMCouplings.selfProcess_intervenedJoint`

### 式

$$
\text{型つき介入 joint は、旧層で三表現・Γ・出力を保つ}
$$

### Lean のコメント（日本語訳）

> 同じNの型付き介入jointは旧層で全三表現・Γ・出力を保つ。

### 補題の説明

同じ \(N\) の型つきの**介入結合法則**は、旧い層で、**三つの表現・\(\Gamma\)・出力のすべて**を保ちます。

### 証明の概略

1. 像の合成で制限観測と自己過程の式を合成する。外生法則の一致（`scm_law`）と、構造式の一致で、旧署名の自己過程の介入結合法則に一致させる。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.selfProcess_baselineJoint"></a>

## 補題 `SharedSCMCouplings.selfProcess_baselineJoint`

### 式

$$
\text{型つきベースライン joint も、介入と同じ制限観測で回収}
$$

### Lean のコメント（日本語訳）

> 同じNの型付き基準jointも介入と同じ制限観測で回収する。

### 補題の説明

同じ \(N\) の型つきの**ベースラインの結合法則**も、介入と同じ制限した観測で回収できます。

### 証明の概略

1. 介入結合法則の補題と同様。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
