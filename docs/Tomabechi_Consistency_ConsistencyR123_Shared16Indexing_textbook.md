# Tomabechi/Consistency/ConsistencyR123_Shared16Indexing.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Shared16Indexing.lean`](../Tomabechi/Consistency/ConsistencyR123_Shared16Indexing.lean)（定理16の層添字を共通束へ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 16 の層の添字を、共通束 \(\mathbb L\) へ載せる**ファイルです。原文の §2.3 は、定理 16 の抽象度の族 \(\mathfrak A_{16}\) を、\(\mathbb L\setminus\{\top\}\) の部分集合で、**上向きに有向で最大元を持たない**ものとします。従来は、定理 16 の系が、旧い署名の自然数の添字だけを読み、共通束への埋め込みを課すフィールドがありませんでした。

ここでは、定理 16 の層 \(i\in\mathbb N\) を共通束の対角の層へ割り当て（`index16`）、同じ共有署名 \(N\) について次を示します。

* `index16` は狭義単調で、すべて頂 \(\top\) より真に下にあります。
* \(\mathfrak A_{16}\) は上向きに有向で、最大元を持ちません。
* 21–23 の段の住所との関係は、段 \(n\) が 16 の層 \(n+1\) です（添字が 1 ずれる。同一視はしない）。旧い有限層の埋め込みとは、`index16 i` が一致します。

### 0.2 このファイルが証明していないこと

* 定理 16 の**担体**（\(K_{i,\alpha}(h)\) の中身）と、層別の TCZ との同定は別の課題です（次のファイル）。ここでは、添字の順序の構造だけを扱います。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §2.3 は、定理16の抽象度の族 𝔄16 を 𝕃∖{⊤} の部分集合で、上向き有向かつ最大元を持たないものとする。従来、定理16の系は旧署名の ℕ 添字だけを読み、共通束への埋込みを課す field がなかった（非退化性 N2 は別物の N.stageAddress を読んでいた）。ここでは定理16の層 i : ℕ を共通束の対角層 diagonalLayer i へ割り当て（index16）、次を同じ SharedModelSignature N について示す。…（以下、上の三点）。定理16の担体と層別 TCZ との同定は別の課題であり、ここでは添字の順序構造だけを扱う。

---

<a id="Tomabechi.Consistency.R123.index16"></a>

## 定義 `index16`

### 式

$$
\mathrm{index}_{16}(i)=\mathrm{diagonalLayer}(i)
$$

### Lean のコメント（日本語訳）

> 定理16の層iの共通束での住所。

### 定義の説明

定理 16 の層 \(i\) の、共通束での**住所**です（共通束の対角の層）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.index16_eq_layerAddressEmbedding"></a>

## 補題 `index16_eq_layerAddressEmbedding`

### 式

$$
\mathrm{index}_{16}(i)=\iota(i)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理 16 の層の住所は、旧い有限層の共通束への埋め込みに一致します。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Consistency.R123.Shared16Indexing"></a>

## 構造体 `Shared16Indexing`

### 式

$$
\mathfrak A_{16}\subset\mathbb L\setminus\{\top\}\text{：狭義単調・上向き有向・最大元なし}
$$

### Lean のコメント（日本語訳）

> 𝔄16の添字構造：𝕃∖{⊤}内、狭義単調、上向き有向、最大元なし。

### 定義の説明

\(\mathfrak A_{16}\) の**添字の構造**の受入型です。フィールドは、住所が狭義単調、すべて頂より真に下、上向きに有向、最大元がない、21–23 の段 \(n\) は 16 の層 \(n+1\)（添字が 1 ずれる）、旧い有限層の埋め込みと一致、\(\mathfrak A_{16}\) の上限は束の頂（有限層は頂に達しない）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.shared16Indexing"></a>

## 定理 `SharedDataPreservation.shared16Indexing`

### 式

$$
\mathrm{Shared16Indexing}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式を満たす署名は、定理 16 の添字の構造を満たします。

### 証明の概略

1. 順序構造は、対角の層の補題（`diagonalLayer_strictMono` など）。
2. 段の住所は、保存式（`stageAddress`）と定義の展開で `index16 (n+1)` に一致する。

----

<a id="Tomabechi.Consistency.R123.Shared16Indexing.inverse_indices16"></a>

## 補題 `Shared16Indexing.inverse_indices16`

### 式

$$
(\exists n,\ \mathrm{index}_{16}(n)\ne\top)\ \wedge\ \text{有向}\ \wedge\ \text{最大元なし}
$$

### Lean のコメント（日本語訳）

> 非退化性N2と同じ形（頂点より下・有向・最大元なし）をindex16で述べ直したもの。N.stageAddress版のinverse_indicesは残している。

### 補題の説明

非退化性 N2 と同じ形（頂より下・有向・最大元なし）を、`index16` で述べ直したものです。`N.stageAddress` 版の `inverse_indices` は残してあります。

### 証明の概略

1. フィールドの組み合わせ。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared16Indexing"></a>

## 定理 `sharedModel_shared16Indexing`

### 式

$$
\mathrm{Shared16Indexing}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、定理 16 の添字の構造を満たします。

### 証明の概略

1. 保存式の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_capacity_and_16indexing"></a>

## 定理 `final_consistency_with_capacity_and_16indexing`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedCapacityInputs}(N)\wedge\mathrm{Shared16Indexing}(N)
$$

### Lean のコメント（日本語訳）

> 容量入力に、定理16の添字入力を加えた存在宣言。

### 補題の説明

容量の入力に、定理 16 の添字の入力を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は、`sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
