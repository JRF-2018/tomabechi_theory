# Tomabechi/Consistency/ConsistencyC6_OriginalLayerInputs.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_OriginalLayerInputs.lean`](../Tomabechi/Consistency/ConsistencyC6_OriginalLayerInputs.lean)（同じ完全状態の上の、定理15 の A1・A3・A4）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理15の**常設仮定 A1・A3・A4**（層の添字の集合・領域・射影・粗視化）を、**同じ完全状態**の上で、共有署名から構成するファイルです。原文の層の添字は自然数の実数像で、物理層 0 と正の層 \(n+1\) を区別します。物理層の観測にはモデルの物理観測を採用し、正層の列挙には入れません。状態の領域・射影は完全状態の上で固定し、共通束の頂点を実数の添字へ写しません。

### 0.2 このファイルが証明していないこと

* A2・A5・A6′・A7 は、`EntropyBalanceInputs`（別のファイル）で扱います。
* 射影は恒等写像の具体例で、A4 の「可逆」はそれによって成り立ちます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文の層添字は自然数の実数像で、物理層0と正層n+1を区別する。物理層の観測にはMの物理観測を採用し、正層列挙へは入れない。状態領域・射影は完全状態上で固定し、共通束の頂点を実数添字へ写さない。

---

<a id="Tomabechi.Consistency.C6.ModelSignature.originalEntropy"></a>

## 定義 `ModelSignature.originalEntropy`

### 式

$$
H_a(z)=\begin{cases}S_{\mathrm{phys}}(z)&a=0\\H_{a-1}(z)&a>0\end{cases}
$$

### Lean のコメント（日本語訳）

> 原文の全層観測。物理層0は同じ収支の物理観測、正層aは正層列挙a-1。

### 定義の説明

原文の全層の観測量です。層 0（物理層）はモデルの物理観測、正の層 \(a\) は、正層の列挙の \(a-1\) 番目です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.OriginalLayerInputs"></a>

## 構造体 `OriginalLayerInputs`

### 式

$$
\text{定理15 の A1・A3・A4}
$$

### Lean のコメント（日本語訳）

> O04–O06の全層入力。A2/A5/A6′/A7はEntropyBalanceInputsと組み合わせる。

### 定義の説明

定理15の**常設仮定 A1・A3・A4** に当たる全層の入力です（A2・A5・A6′・A7 は `EntropyBalanceInputs` と組み合わせます）。フィールドは、(A1) 層の添字の集合は可算・非負で、0（物理層）と正の層の添字を含み、正の添字はちょうど正の層、各層の領域・観測量・軌道・直和は可測、(A3) 射影は可測・反射的・合成可能、(A4) 粗視化でエントロピーは減らず、等号なら可逆（元に戻せる）です。

### 証明の概略

1. 構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_completePath_measurable"></a>

## 定理 `commonModel_completePath_measurable`

### 式

$$
t\mapsto\mathrm{completePath}(t)\ \text{は可測}
$$

### Lean のコメント（日本語訳）

> 元段の完全pathを、全実数連続なC1積分軌道の認知射影へ、非負時間域で結ぶ。物理座標は同じ状態の収支式から回収する。新しい時計は追加しない。

### 補題の説明

完全軌道は、非負の時間で可測です。段を継ぎ合わせた軌道を、全実数で連続な C1 の積分軌道の認知座標に結び、物理座標は同じ状態の収支の式から回収します。新しい時計の座標は加えません。

### 証明の概略

1. 認知座標 \(q(t)=1+(\text{積分軌道})\) は連続（`c1ControlledOrbit_continuous`）なので可測。
2. 完全軌道が \((q(t),\ 3t-q(t)^2)\) に等しいことを、C1 の軌道との一致と一般化エントロピーの式から示す。
3. 可測関数の組・積・差・冪は可測。

----

<a id="Tomabechi.Consistency.C6.commonModel_originalLayerInputs"></a>

## 定理 `commonModel_originalLayerInputs`

### 式

$$
\mathrm{OriginalLayerInputs}(\text{commonModel})
$$

### Lean のコメント（日本語訳）

> 全層可測性と原文射影条件を同じcommonModelの観測/完全pathで構成する。

### 補題の説明

全層の可測性と、原文の射影の条件を、同じ共有モデルの観測・完全軌道で構成します。

### 証明の概略

1. 添字の集合の性質は定理15の層アダプタ（`c6Theorem15LayerAdapter`）から。
2. 観測量の可測性は、物理層は第 2 座標、正層は \(1+q^2\) として、場合分けで示す。
3. 射影の性質は C2 の補題（恒等写像）。粗視化の不等式は等号、可逆性は \(y=z\)。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
