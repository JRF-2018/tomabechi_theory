# Tomabechi/Consistency/ConsistencyR123_FixedCapacity.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FixedCapacity.lean`](../Tomabechi/Consistency/ConsistencyR123_FixedCapacity.lean)（定理19の容量を固定した主体・履歴で）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 19 の容量を、固定した主体・履歴で**定義し直すファイルです。原文 §8 は、主体 \(i\) と履歴 \(h\) を**固定**して、\(\mathcal F_i(\alpha)=\sup_{\text{問題},\text{許容方策}}I(G;Y^\pi\mid X)\) を定義します。従来の `SharedModelSignature.sharedCapacity` は、問題の族が主体・履歴・初期状態・時刻のすべてを動かす上限で、固定した \((i,h)\) の容量ではありませんでした。

ここでは \((d,H)\) を**外側の引数**にします。

* **問題：** 層 \(c\preceq a\)、その層の初期状態 \(x\)、開始時刻 \(T\)、時刻 \(t\)。生成の結合法則は、`N.fullExperimentLaw`（実軌道・実費用を含む、固定した \(d,H\)）を、入力・ゴール・実方策から再符号化した行為へ押し出したもの。評価値はその直接 CMI。許容問題は \(T\ge0\)。
* **許容方策の族（層 \(c\) ごとに有限族）：** 情報実験で既に実現した二つの復号を使います。方策の相違は実制御の相違（復号が区別される、再符号化で `false/true` に戻る）で、両方が同じ `N.data` の許容方策で、`true` は最適方策です。
* **容量：** `fixedCapacity N d H a`（定理 19 の依存型の容量）。包含の埋め込みで、全対の結合法則と評価値を保ちます。有限・非空・単調・端点・正規化。固定しない従来の `sharedCapacity` と一致します（この証人では、結合法則が主体・履歴によらないため）。
* **主体・履歴の対応：** 固定した \((d,H)\) の実験の自己過程の周辺は、`N.selfProcess d a` のベースラインの結合法則です。

### 0.2 このファイルが証明していないこと

* 方策の族は、情報実験で実現した二つの復号に限ります（原文は方策の族を固定していません）。ゴールは `Bool` 一つです。
* 容量が主体・履歴によらないのは、**この証人の性質**であり、一般の \(N\) で成り立つとは主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §8 は主体 i と履歴 h を固定して、ℱ_i(α) = sup_{問題, 許容方策} I(G;Y^π|X) を定義する。従来の SharedModelSignature.sharedCapacity は、問題族 CapProblem a が主体・履歴・初期状態・時刻のすべてを動かす上限で、固定した (i,h) の容量ではなかった。ここでは (d, H) を外側の引数にする。…（以下、上の四点と範囲）。

---

<a id="Tomabechi.Consistency.R123.instance@L32"></a>

## インスタンス `instance@L32`

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

<a id="Tomabechi.Consistency.R123.FixedExperiment"></a>

## 定義 `FixedExperiment`

### 式

$$
\text{初期状態}\times\text{開始時刻}\times\text{時刻}
$$

### Lean のコメント（日本語訳）

> 層cの実験データ（主体・履歴を除く）：初期状態・開始時刻・時刻。

### 定義の説明

層 \(c\) の実験のデータ（主体・履歴を除く）です。初期状態・開始時刻・時刻から成ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.CapProblemFixed"></a>

## 定義 `CapProblemFixed`

### 式

$$
\Sigma\ c\preceq a,\ \mathrm{FixedExperiment}(c)
$$

### Lean のコメント（日本語訳）

> 固定した主体・履歴の問題族：a以下の層cと、その層の実験データ。

### 定義の説明

固定した主体・履歴の**問題の族**です。\(a\) 以下の層 \(c\) と、その層の実験のデータの組です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissibleFixed"></a>

## 定義 `capacityAdmissibleFixed`

### 式

$$
\{p\mid 0\le T\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

許容される問題です。開始時刻が非負であること。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.toPooled"></a>

## 定義 `toPooled`

### 式

$$
\text{固定した }(d,H)\text{ の問題を、}d,H\text{ を動かす問題族の一要素として見る}
$$

### Lean のコメント（日本語訳）

> 固定した(d,H)の問題を、d,Hを動かす問題族の一要素として見る。

### 定義の説明

固定した \((d,H)\) の問題を、\(d,H\) を動かす問題の族の一要素として見る写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.capacityScoreFixed"></a>

## 定義 `SharedModelSignature.capacityScoreFixed`

### 式

$$
\mathrm{score}_{d,H}(p)=\mathrm{score}(\mathrm{toPooled}(p))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

固定した主体・履歴での、問題の評価値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fixedCapacity"></a>

## 定義 `SharedModelSignature.fixedCapacity`

### 式

$$
\mathcal F_{d,H}(a)=\sup_{p}\ \mathrm{score}_{d,H}(p)
$$

### Lean のコメント（日本語訳）

> 固定した主体d・履歴Hの容量ℱ_{d,H}(a)（定理19の依存型容量）。

### 定義の説明

固定した主体 \(d\)・履歴 \(H\) の**容量** \(\mathcal F_{d,H}(a)\) です（定理 19 の依存型の容量）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityEmbeddingFixed"></a>

## 定義 `capacityEmbeddingFixed`

### 式

$$
\iota_{ab}
$$

### Lean のコメント（日本語訳）

> 層の包含による問題の埋込み。

### 定義の説明

層の包含による、問題の埋め込みです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityEmbeddingFixed_injective"></a>

## 補題 `capacityEmbeddingFixed_injective`

### 式

$$
\iota_{ab}\text{ は単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

埋め込みは単射です。

### 証明の概略

1. 成分を比べ、層の等しさから置換して実験データの等しさを得る。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissibleFixed_nonempty"></a>

## 補題 `capacityAdmissibleFixed_nonempty`

### 式

$$
\text{許容問題は空でない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容される問題は存在します。

### 証明の概略

1. 底の層の状態の非空性から、開始時刻 0 の問題を取る。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityScoreFixed_eq"></a>

## 補題 `SharedDataPreservation.capacityScoreFixed_eq`

### 式

$$
\mathrm{score}_{d,H}(p)=\begin{cases}0&c=\bot\\ \log2&\text{それ以外}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定した主体・履歴でも、評価値は、底の層の問題では 0、それ以外では \(\log2\) です。

### 証明の概略

1. 従来の `capacityScore_eq` に帰着。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.capacityScoreFixed_bounded"></a>

## 補題 `SharedDataPreservation.capacityScoreFixed_bounded`

### 式

$$
\text{評価値の像は上に有界}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

評価値の像は、上に有界です（上界 \(\log2\)）。

### 証明の概略

1. 各評価値が 0 または \(\log2\)。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fixedCapacity_monotone"></a>

## 補題 `SharedDataPreservation.fixedCapacity_monotone`

### 式

$$
a\preceq b\Rightarrow\mathcal F_{d,H}(a)\le\mathcal F_{d,H}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定した主体・履歴の容量は、単調です。

### 証明の概略

1. 定理 19 の埋め込みによる単調性の補題（`dependentCapacity_nondecreasing_of_scorePreservingEmbedding`）に、非空・有界・埋め込みを渡す。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fixedCapacity_bottom"></a>

## 補題 `SharedDataPreservation.fixedCapacity_bottom`

### 式

$$
\mathcal F_{d,H}(\bot)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底の容量は 0 です。

### 証明の概略

1. 底以下の問題は底の層のものだけで、評価値は 0 だけ。上限が 0。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fixedCapacity_top"></a>

## 補題 `SharedDataPreservation.fixedCapacity_top`

### 式

$$
\mathcal F_{d,H}(\top)=\log2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の容量は \(\log2\) です。

### 証明の概略

1. 上界 \(\log2\) と、頂の層の問題（開始時刻 0）の評価値が \(\log2\) であること。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.fixedCapacity_eq_shared"></a>

## 補題 `SharedDataPreservation.fixedCapacity_eq_shared`

### 式

$$
\mathcal F_{d,H}(a)=\mathcal F(a)
$$

### Lean のコメント（日本語訳）

> 固定した(d,H)の容量は、従来の（主体・履歴を動かす）sharedCapacityと、全点で一致する。

### 補題の説明

固定した \((d,H)\) の容量は、従来の（主体・履歴を動かす）`sharedCapacity` と、**全点で一致**します。

### 証明の概略

1. 評価値の像の集合が一致する。両方とも評価値が層で決まる（`capacityScoreFixed_eq` と `capacityScore_eq`）。

----

<a id="Tomabechi.Consistency.R123.SharedFixedCapacityInputs"></a>

## 構造体 `SharedFixedCapacityInputs`

### 式

$$
\text{問題族・許容方策族・生成 joint・保存単射・容量を原文の量化で}
$$

### Lean のコメント（日本語訳）

> 固定した(d,H)の容量の受入型：問題族・許容方策族・生成joint・保存単射・容量を原文の量化で。

### 定義の説明

固定した \((d,H)\) の容量の受入の型です（問題族・許容方策族・生成の結合法則・保存する単射・容量を、原文の量化で述べる）。フィールドは次のとおりです。

* 各固定 \((d,H)\) で、問題族は非空・上界つき。
* 各問題の結合法則は、固定した \((d,H)\) の実験の結合法則の押し出しで、確率測度・KL 有限。
* 許容方策族：各層 \(c\) の有限族 \(\{\mathrm{decode}\,c\,\mathrm{false},\mathrm{decode}\,c\,\mathrm{true}\}\)。`true` は最適。方策の相違は実制御の相違で、再符号化で `false/true` に戻る。
* 実験の状態・費用は、同じ `N.data` の実軌道・実走行費。
* 固定した \((d,H)\) の実験の自己過程の周辺は、25 の `N.selfProcess d a` のベースラインの結合法則。
* 層の包含による埋め込み（単射・許容性・評価値を保存）。
* 容量：有限（\(\le\log2\)）・非負・単調・端点・正規化。
* 従来の `sharedCapacity`（主体・履歴を動かす）と一致する（この証人の性質）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_fixedCapacityInputs"></a>

## 定理 `sharedModel_fixedCapacityInputs`

### 式

$$
\mathrm{SharedFixedCapacityInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、固定した主体・履歴の容量の入力を満たします。

### 証明の概略

1. 各フィールドは、上の補題と、全実験の入力（`sharedModel_fullExperimentInputs`）の復号の性質から。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v9"></a>

## 定理 `final_consistency_v9`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedFixedCapacityInputs}(N)
$$

### Lean のコメント（日本語訳）

> v9：v8に、固定した主体・履歴の定理19容量を加えた存在宣言。

### 補題の説明

第 9 版です。第 8 版に、固定した主体・履歴の定理 19 の容量を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
