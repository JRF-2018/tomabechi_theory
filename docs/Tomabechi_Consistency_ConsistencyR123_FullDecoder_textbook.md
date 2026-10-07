# Tomabechi/Consistency/ConsistencyR123_FullDecoder.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FullDecoder.lean`](../Tomabechi/Consistency/ConsistencyR123_FullDecoder.lean)（全共通束点の許容情報方策族）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共通束の**全点**での、許容される**情報の方策の族**（復号）を与えるファイルです。有限層では元のゲイン 0/3、頂点では元の可測な動径ゲイン 0/1/2 を使います。二つの方策は、各層の許容族の**部分族**であり、元の全方策族を置き換えません。同じ `N.data` での許容性と、`true` の方策の最適性を、全初期状態・非負の開始時刻で要求します。

### 0.2 このファイルが証明していないこと

* 二値の行為は、許容方策の族の中の**二つの方策**を指定するだけです。
* 作用による符号化は、時刻 0・参照状態での作用を読むもので、任意の初期状態で作用が区別されるとは主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 有限層では元のゲイン0/3、頂点では元の可測動径ゲイン0/1/2を使用する。二方策は各層の許容族の部分族であり、元の全方策族を置き換えない。同じN.dataでの許容性・true方策の最適性を全初期状態・非負開始時刻で要求する。

---

<a id="Tomabechi.Consistency.R123.instance@L19"></a>

## インスタンス `instance@L19`

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

<a id="Tomabechi.Consistency.R123.fullDecoderZeroGain"></a>

## 定義 `fullDecoderZeroGain`

### 式

$$
u(t)\equiv0
$$

### Lean のコメント（日本語訳）

> 頂点で使う定数零動径ゲイン。生命方向の成分は元の方策に保つ。

### 定義の説明

頂点で使う、**定数の零の動径ゲイン**です。生命の方向の成分は、元の方策に保ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullLayerDecoder"></a>

## 定義 `fullLayerDecoder`

### 式

$$
\text{false}\mapsto\text{ゲイン 0},\ \text{true}\mapsto\text{ゲイン最大}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの二値の復号です。頂点では、`true` が最大の動径ゲイン、`false` が零のゲイン。有限層では、元の情報の方策（ゲイン 0/3）を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder"></a>

## 定義 `fullInformationDecoder`

### 式

$$
a\mapsto\mathrm{fullLayerDecoder}(\mathrm{index}(a))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の各点での、二値の情報の行為の復号の族です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullLayerDecoder_distinct"></a>

## 補題 `fullLayerDecoder_distinct`

### 式

$$
\mathrm{decode}(\mathrm{false})\ne\mathrm{decode}(\mathrm{true})
$$

### Lean のコメント（日本語訳）

> 実方策族の中の二方策は全層で区別される。

### 補題の説明

実際の方策の族の中の二つの方策は、**全層で区別**されます。

### 証明の概略

1. 有限層では、元の情報の方策の区別（`c6InformationPolicy_distinct`）。
2. 頂点では、等しいと仮定して、参照状態・時刻 0 での動径作用を比べ、矛盾を出す。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder_optimal"></a>

## 補題 `fullInformationDecoder_optimal`

### 式

$$
\mathrm{decode}(a,\mathrm{true})=\text{実データの最適方策}
$$

### Lean のコメント（日本語訳）

> true情報行為は実Dの最適方策。全共通束点・全初期状態・全開始時刻。

### 補題の説明

`true` の情報の行為は、実際のデータの**最適方策**です（全共通束点・全初期状態・全開始時刻）。

### 証明の概略

1. 層の番号で場合分け（有限層・頂点）。どちらも定義から `rfl`。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder_false_admissible"></a>

## 補題 `fullInformationDecoder_false_admissible`

### 式

$$
\mathrm{decode}(a,\mathrm{false})\ \text{は許容}
$$

### Lean のコメント（日本語訳）

> false方策も同じ実Dの許容方策族に属する。

### 補題の説明

`false` の方策も、同じ実際のデータの**許容方策の族**に属します。

### 証明の概略

1. 層の番号で場合分け。有限層は自明、頂点は零ゲインが許容されること。

----

<a id="Tomabechi.Consistency.R123.fullInformationEncode"></a>

## 定義 `fullInformationEncode`

### 式

$$
\pi\mapsto[\pi=\mathrm{decode}(a,\mathrm{true})]
$$

### Lean のコメント（日本語訳）

> 方策を同じ二値行為へ戻す符号化。全方策上に定義し、復号像上で左逆を証明する。

### 定義の説明

方策を、同じ二値の行為へ戻す**符号化**です。全方策の上に定義し、復号の像の上で左逆であることを証明します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder_code"></a>

## 補題 `fullInformationDecoder_code`

### 式

$$
\mathrm{encode}(\mathrm{decode}(g))=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

符号化は、復号の左逆です。

### 証明の概略

1. `g` の値で場合分け。`false` は、二方策が異なること（`fullLayerDecoder_distinct`）から。

----

<a id="Tomabechi.Consistency.R123.fullLayerActionEncode"></a>

## 定義 `fullLayerActionEncode`

### 式

$$
\text{実制御の観測による符号化（時刻 0・参照状態）}
$$

### Lean のコメント（日本語訳）

> 実制御の観測による符号化。有限層は時刻0のゲイン、頂点は時刻0・参照状態e₀での動径作用を読む。任意の初期状態で作用が区別されるとは主張しない。

### 定義の説明

実際の制御の**観測による符号化**です。有限層は時刻 0 のゲインを、頂点は時刻 0・参照状態 \(e_0\) での動径の作用を読みます。任意の初期状態で作用が区別される、とは主張しません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullActionEncode"></a>

## 定義 `fullActionEncode`

### 式

$$
\text{共通束の点での、作用による符号化}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の点での、作用による符号化です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullLayerDecoder_action_code"></a>

## 補題 `fullLayerDecoder_action_code`

### 式

$$
\mathrm{actionEncode}(\mathrm{decode}(g))=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

作用による符号化も、復号の左逆です。

### 証明の概略

1. 有限層は、元の情報の方策の補題（`c6InformationPolicy_code`）。頂点は、`g` で場合分けして計算。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder_action_code"></a>

## 補題 `fullInformationDecoder_action_code`

### 式

$$
\mathrm{actionEncode}(\mathrm{decode}(a,g))=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の点でも、作用による符号化は、復号の左逆です。

### 証明の概略

1. 層ごとの補題。

----

<a id="Tomabechi.Consistency.R123.decoder_cast"></a>

## 補題 `decoder_cast`

### 式

$$
\text{復号は層の等式に沿った cast と可換}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の等式に沿った型の変換（cast）と、復号が可換であることを示す補助補題です（`private`）。

### 証明の概略

1. 等式で場合分け。

----

<a id="Tomabechi.Consistency.R123.fullInformationDecoder_finite"></a>

## 補題 `fullInformationDecoder_finite`

### 式

$$
\text{有限の旧住所で、実復号方策が元の情報方策に戻る}
$$

### Lean のコメント（日本語訳）

> 全有限旧住所では、実復号方策がNの元の情報方策へ厳密に戻る。

### 補題の説明

すべての有限の旧い住所で、実際の復号の方策が、\(N\) の元の情報の方策に、**厳密に戻ります**。

### 証明の概略

1. `decoder_cast` と、層の番号の補題（`fullCommonLayerIndex_layerAddress`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperiment_actualPolicyInformation"></a>

## 補題 `SharedDataPreservation.fullExperiment_actualPolicyInformation`

### 式

$$
\text{復号・再符号化した情報 joint}=N.\mathrm{informationLaw}(a)
$$

### Lean のコメント（日本語訳）

> 全点の情報jointは実方策を復号・再符号化しても変わらない。

### 補題の説明

全点の情報の結合法則は、実際の方策を復号し、再び符号化しても、変わりません。

### 証明の概略

1. 全域実験の情報の周辺と、復号の左逆（`fullInformationDecoder_code`）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fullExperiment_actualActionInformation"></a>

## 補題 `SharedDataPreservation.fullExperiment_actualActionInformation`

### 式

$$
\text{作用で観測・再符号化した情報 joint}=N.\mathrm{informationLaw}(a)
$$

### Lean のコメント（日本語訳）

> 指定の参照状態で実入力を観測・再符号化した情報jointも同じlawである。

### 補題の説明

指定の参照状態で、実際の入力を観測し、再び符号化した情報の結合法則も、同じ法則です。

### 証明の概略

1. 前の補題と同様。作用による符号化の左逆（`fullInformationDecoder_action_code`）を使う。

----

<a id="Tomabechi.Consistency.R123.SharedFullExperimentInputs"></a>

## 構造体 `SharedFullExperimentInputs`

### 式

$$
\text{復号が最適・許容・区別・有限住所で元に戻る}
$$

### Lean のコメント（日本語訳）

> 全実験の復号族について、同じN.dataの許容性・最適性を必須にする。

### 定義の説明

全実験の復号の族について、**同じ `N.data` の許容性・最適性**を必須にする受入の型です（`SharedPointInputs` を拡張）。フィールドは、`true` の復号が最適方策、全方策が許容（開始時刻が非負のとき）、二方策が区別される、有限の旧い住所で元の情報の方策に戻る、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_fullExperimentInputs"></a>

## 定理 `sharedModel_fullExperimentInputs`

### 式

$$
\mathrm{SharedFullExperimentInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 許容・最適・非退化の復号族と、既存全入力を同じ署名で構成する。

### 補題の説明

許容・最適・非退化の復号の族と、既存の全入力を、同じ署名で構成します。

### 証明の概略

1. 既存の入力（`sharedModel_pointInputs`）、最適性（`fullInformationDecoder_optimal`）、許容性（`false` は `fullInformationDecoder_false_admissible`、`true` は最適方策の許容性）、有限の旧い住所（`fullInformationDecoder_finite`）。

----

<a id="Tomabechi.Consistency.R123.shared_full_experiment_model_exists"></a>

## 定理 `shared_full_experiment_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedFullExperimentInputs}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

復号の族の入力を満たす共有署名が存在します。

### 証明の概略

1. `sharedModel` を取る。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
