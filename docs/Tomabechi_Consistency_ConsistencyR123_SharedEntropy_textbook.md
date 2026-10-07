# Tomabechi/Consistency/ConsistencyR123_SharedEntropy.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedEntropy.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedEntropy.lean)（共有署名の観測と完全状態の軌道による、15→23 の入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**観測と完全状態の軌道**から、**定理15→23**（エントロピーの収支）の入力を作るファイルです。可算個の正の層の重み・観測・完全状態の軌道を、**同じ署名 \(N\)** から読み、全有限部分和の一様可積分性と A7 を含む、一般の入口に直接渡します。層の添字は、共通束の中の正の層の住所の**可算な族**であり、束のすべての点が可算だと仮定してはいません。

### 0.2 このファイルが証明していないこと

* 生成率は 3（定数）、生きている時間は非負の半直線の、具体的なモデルです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 可算正層の重み・観測・完全状態 path を同じ署名 N から読む。全有限部分和の一様可積分性と A7 を含む一般入口へ直接渡す。層添字は共通束内の正層住所の可算族であり、全束点を可算と仮定しない。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.positiveObservation"></a>

## 定義 `SharedModelSignature.positiveObservation`

### 式

$$
(p,z)\mapsto N.\mathrm{observation}(\mathrm{addr}_p,z)
$$

### Lean のコメント（日本語訳）

> 正層住所を読む観測と重み。元モデルの観測を別に注入しない。

### 定義の説明

正の層の**住所**で読む観測です。元のモデルの観測を、別に注入しません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.positiveWeight"></a>

## 定義 `SharedModelSignature.positiveWeight`

### 式

$$
p\mapsto N.\mathrm{weight}(\mathrm{addr}_p)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

正の層の住所で読む重みです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedEntropyInputs"></a>

## 構造体 `SharedEntropyInputs`

### 式

$$
\text{共有署名上の定理15・23-A の全積分収支入力}
$$

### Lean のコメント（日本語訳）

> 共有署名上の定理15/23-Aの全積分収支入力。A7は他条件から導く仮定に変更せず、独立の収支式として保持する。

### 定義の説明

共有署名の上の**定理15・23-A の全積分収支の入力**です。A7 は、他の条件から導く仮定に変えず、**独立した収支式**として保持します。フィールドは、重みは正、層の観測は非負、生成の積分は正・可積分、層・物理の観測は絶対連続、端点で総和可能、有限部分和は一様可積分、列挙に沿った部分和は a.e. 収束、A7 の収支、生成は非負、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.entropyInputs"></a>

## 定理 `SharedDataPreservation.entropyInputs`

### 式

$$
\text{保存式と以前のエントロピー入力から、署名 }N\text{ の入力を得る}
$$

### Lean のコメント（日本語訳）

> 観測・重み・pathの保存式を使い、全積分入力を署名Nへ移す。Nのデータをcanonical値へ置き換える外部仮定は要求しない。

### 補題の説明

観測・重み・軌道の保存式を使って、全積分の入力を、署名 \(N\) に移します。\(N\) のデータを正典の値に置き換える外部の仮定は要求しません。

### 証明の概略

1. 重み・正の層の観測・物理観測が、以前のものに等しい（保存式から関数として）。
2. 各フィールドを、以前の署名のエントロピーの入力から、等式で書き換えて得る（`simpa`）。

----

<a id="Tomabechi.Consistency.R123.SharedEntropyInputs.nonrecurrence"></a>

## 定理 `SharedEntropyInputs.nonrecurrence`

### 式

$$
t_1<t_2\Rightarrow N.\mathrm{path}(t_2)\ne N.\mathrm{path}(t_1)
$$

### Lean のコメント（日本語訳）

> 同じ署名の完全状態pathに一般15→23入口を直接適用する。

### 補題の説明

同じ署名の完全状態の軌道に、一般の 15→23 の入口を直接適用します（軌道は同じ状態に戻らない）。

### 証明の概略

1. 可算無限層の入口（`theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence`）に、物理観測・正の層の観測・重み・完全軌道・生成率 3 を渡し、各前件を入力のフィールドで対応させる。

----

<a id="Tomabechi.Consistency.R123.sharedModel_entropyInputs"></a>

## 定理 `sharedModel_entropyInputs`

### 式

$$
\mathrm{SharedEntropyInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 共有署名の具体path上で全入力を同時に満たす。

### 補題の説明

共有署名の具体的な軌道の上で、全入力を同時に満たします。

### 証明の概略

1. 保存式の定理（`sharedModel_preservation.entropyInputs`）に、以前の署名のエントロピーの入力（`commonModel_entropyInputs`）を渡す。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
