# Tomabechi/Consistency/ConsistencyC6_SignatureSelfProcess.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_SignatureSelfProcess.lean`](../Tomabechi/Consistency/ConsistencyC6_SignatureSelfProcess.lean)（共有署名自身から作る、型つきの自己過程）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

型つきの自己過程（Self・Ego・TCZ）を、**共有署名 `ModelSignature` 自身**の SCM・外生法則・履歴・候補・三つの表現から作り、共有保存式から**条件 25-A(2)**（介入不変性）と、全主体・全共通層での**自己の不在**（定理25の第二の結論）を得るファイルです。局所の SCM の結論を、データの同定なしに \(M\) に移したものではありません。

### 0.2 このファイルが証明していないこと

* 定理25の結論は、共有保存式（`CommonDataCouplings`）を仮定したものです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> M の同じ SCM・外生法則・履歴・候補・Self/Ego/TCZ から自己過程を構成する。共有保存式から 25-A2 の同時法則不変性と全主体/共通層の 25.2 入口適用を得る。局所 SCM の結論を、データ同定なしに M へ移した結果ではない。

---

<a id="Tomabechi.Consistency.C6.ModelSignature.typedObservation"></a>

## 定義 `ModelSignature.typedObservation`

### 式

$$
(\Gamma,h)\mapsto((\Gamma,R(h)),h)
$$

### Lean のコメント（日本語訳）

> 同じモデルの三表現を付加し、Γと出力を保存する観測。

### 定義の説明

共有署名の三つの表現（Self・Ego・TCZ）を付加し、\(\Gamma\) と出力を保存する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.typedObservation_measurable"></a>

## 補題 `ModelSignature.typedObservation_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測は可測です。

### 証明の概略

1. 各成分（恒等・有限の型からの写像・恒等）の可測性を合わせる。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.intervenedSelfObservation"></a>

## 定義 `ModelSignature.intervenedSelfObservation`

### 式

$$
\text{介入時の観測}
$$

### Lean のコメント（日本語訳）

> 介入時も同じMのΓ/出力に同じ三表現観測を施す。

### 定義の説明

介入のときも、同じ \(M\) の \(\Gamma\)・出力に、同じ三つの表現の観測を施します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.ModelSignature.selfProcess"></a>

## 定義 `ModelSignature.selfProcess`

### 式

$$
\text{全主体・全共通層の自己過程}
$$

### Lean のコメント（日本語訳）

> Mの同じ外生確率空間から生成する全主体・全共通層の自己過程。

### 定義の説明

同じ \(M\) の外生確率空間から作る、全主体・全共通層の**自己過程**です。外生法則・入力履歴・候補は SCM のもの、ベースライン・介入した式は上の観測です。

### 証明の概略

1. 各フィールドに \(M\) の SCM の対応するものを入れる。可測性は観測の可測性と SCM の可測性の合成。

----

<a id="Tomabechi.Consistency.C6.CommonDataCouplings.selfObservation_invariant"></a>

## 補題 `CommonDataCouplings.selfObservation_invariant`

### 式

$$
\text{介入観測}=\text{ベースライン観測}
$$

### Lean のコメント（日本語訳）

> 共有保存式により、Mの型付き表象/Γ/出力の全介入観測は基準観測と一致する。

### 補題の説明

共有の保存式により、型つきの表象・\(\Gamma\)・出力の、すべての介入観測が、ベースラインの観測と一致します。

### 証明の概略

1. 両方の定義を展開し、出力が履歴（`scm_output_history`）、状態の式・表象が候補に依らないことを使う。

----

<a id="Tomabechi.Consistency.C6.CommonDataCouplings.selfProcess25A2"></a>

## 補題 `CommonDataCouplings.selfProcess25A2`

### 式

$$
\text{25-A(2)}
$$

### Lean のコメント（日本語訳）

> MのSCMが持つ独立性と全介入観測の保存から、同じ自己過程の25-A2を供給する。

### 補題の説明

SCM が持つ独立性と、全介入観測の保存から、同じ自己過程について条件 25-A(2)（介入不変性）を与えます。

### 証明の概略

1. 候補が全体の文脈と独立（SCM の性質）。
2. 介入観測がベースライン観測と一致（前の補題）から、介入した結合法則が一致する。

----

<a id="Tomabechi.Consistency.C6.CommonDataCouplings.noAtman"></a>

## 補題 `CommonDataCouplings.noAtman`

### 式

$$
\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)
$$

### Lean のコメント（日本語訳）

> Mの実SCMを25.2一般入口へ渡す。全主体/全共通層でΓ全観測を保持する。

### 補題の説明

\(M\) の実際の SCM を、定理25の第二の結論の一般入口へ渡し、**すべての主体・すべての共通層で自己（アートマン）が存在しない**ことを得ます。\(\Gamma\) のすべての観測を保持します。

### 証明の概略

1. 出力が候補に依らない（a.e.）ことから、一般入口（`..._outputAENoninterference`）を適用する。

----

<a id="Tomabechi.Consistency.C6.commonModel_selfProcess25A2"></a>

## 定理 `commonModel_selfProcess25A2`

### 式

$$
\text{25-A(2)（共有モデル）}
$$

### Lean のコメント（日本語訳）

> 同じ署名の保存証拠に対する閉じた25-A2適用。

### 補題の説明

共有モデル自身の保存の証拠に対する、閉じた形の 25-A(2) です。

### 証明の概略

1. `commonModel_couplings` に前の補題を適用する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
