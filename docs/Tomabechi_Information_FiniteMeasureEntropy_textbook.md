# Tomabechi/Information/FiniteMeasureEntropy.lean 解説

> 対象: [`Tomabechi/Information/FiniteMeasureEntropy.lean`](../Tomabechi/Information/FiniteMeasureEntropy.lean)（有限ゴール条件付きエントロピーの測度論的基礎）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`FiniteCMI.lean` の「有限の同時質量」の条件付きエントロピーを、**一般の可測な入力空間**（確率測度 \(\mu\)）へ広げる準備のファイルです。
目標空間 \(G\) は有限のまま、入力 \(x\) ごとに「目標の条件付き確率 \(\text{mass}(x,\cdot)\)」があり、エントロピー密度 \(x\mapsto\sum_gh(\text{mass}(x,g),1)\) を**入力で積分**して \(H(G|X)\) とします。

### 0.2 このファイルが示すこと

- エントロピー密度が可測であること、各項が \([0,1]\) の確率で \(|{-p\log p}|\le1\) と抑えられること。
- 確率ベクトルについてエントロピー密度が \(|G|\)（目標の個数）で抑えられること。
- したがって、確率測度の上でエントロピー密度が**可積分**になり、積分（\(H(G|X)\)）が意味をもつこと。

### 0.3 このファイルが証明していないこと

- 残余エントロピー・相互情報量・定理21の情報容量は `DeterministicOutput.lean` で扱います。
- 条件付き確率 \(\text{mass}(x,g)\) の存在・可測性は**仮定**です（どのように生成されるかは扱わない）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 有限の目標についての条件付きエントロピーの、測度論的な基礎。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem21`。

---

<a id="Tomabechi.Theorem21.conditionalGoalEntropyAt"></a>

## 定義 `conditionalGoalEntropyAt`

### 式

$$\mathrm{ent}(\text{mass})=\sum_gh(\text{mass}(g),1)=-\sum_g\text{mass}(g)\log\text{mass}(g)$$

### Lean のコメント（日本語訳）

> 有限の目標空間についての、1 つの入力での条件付きエントロピー密度。

### 定義の説明

入力が 1 つ決まったときの、目標の確率ベクトル \(\text{mass}\) の（通常の）エントロピーです（分母を 1 としたもの）。これを入力について積分して条件付きエントロピーを作ります。

### 証明の概略

1. 定義：`∑ g, finiteConditionalEntropyTerm (mass g) 1`。

----

<a id="Tomabechi.Theorem21.measurable_finiteConditionalEntropyTerm_one"></a>

## 補題 `measurable_finiteConditionalEntropyTerm_one`

### 式

$$p\mapsto h(p,1)\ \text{は可測}$$

### Lean のコメント（日本語訳）

> 有限のエントロピーの和の各項は、その質量の関数として可測である。

### 補題の説明

エントロピーの 1 項を実数の関数として見ると、可測（積分できる）関数です。

### 証明の概略

1. `if p = 0 then 0 else -p * log (p/1)` の形なので、条件 \(p=0\) の可測性（`measurableSet_eq_fun`）と、各分岐の可測性（`Measurable.ite`）から。

----

<a id="Tomabechi.Theorem21.conditionalGoalEntropyAt_aestronglyMeasurable"></a>

## 補題 `conditionalGoalEntropyAt_aestronglyMeasurable`

### 式

$$\forall g,\ x\mapsto\text{mass}(x,g)\ \text{可測}\ \Longrightarrow\ x\mapsto\mathrm{ent}(\text{mass}(x,\cdot))\ \text{可測}$$

### Lean のコメント（日本語訳）

> 各条件付きの目標の質量が可測であることから、その有限のエントロピー密度が可測であることが出る。

### 補題の説明

入力 \(x\) の関数としてのエントロピー密度が可測（概強可測）です。積分の前提になります。

### 証明の概略

1. 有限和の可測性（`Finset.aestronglyMeasurable_fun_sum`）と、各項の合成の可測性（前の補題）から。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyTerm_one_abs_le_one"></a>

## 補題 `finiteConditionalEntropyTerm_one_abs_le_one`

### 式

$$0\le p\le1\ \Longrightarrow\ \lvert-p\log p\rvert\le1$$

### Lean のコメント（日本語訳）

> 二値のエントロピーの項 \(-p\log p\) の絶対値は、確率の区間上で高々 1 である。

### 補題の説明

確率 \(p\in[0,1]\) について \(-p\log p\) は 0 以上 \(1/e\) 以下なので、1 以下とできます。

### 証明の概略

1. \(p=0\) は自明。\(0<p\le1\) では Mathlib の `Real.abs_log_mul_self_lt`（\(|\log p\cdot p|<1\)）を使う（8 行）。

----

<a id="Tomabechi.Theorem21.conditionalGoalEntropyAt_norm_le_card"></a>

## 補題 `conditionalGoalEntropyAt_norm_le_card`

### 式

$$\text{mass}\ge0,\ \sum_g\text{mass}(g)=1\ \Longrightarrow\ \lVert\mathrm{ent}(\text{mass})\rVert\le|G|$$

### Lean のコメント（日本語訳）

> 有限の目標空間上の確率ベクトルについて、エントロピー密度は目標の個数で抑えられる。この粗い上界は、任意の確率の入力空間上の可積分性を示すのに十分である。

### 補題の説明

各成分は確率（\(\le1\)）で、その項は絶対値 \(\le1\)。\(|G|\) 個の和なので \(|G|\) 以下です。

### 証明の概略

1. 各 \(\text{mass}(g)\le1\)（和が 1 で非負）。
2. 各項の絶対値 \(\le1\)（前の補題）。三角不等式で \(|G|\) 以下（16 行）。

----

<a id="Tomabechi.Theorem21.conditionalGoalEntropy_integrable_of_ae_probability"></a>

## 補題 `conditionalGoalEntropy_integrable_of_ae_probability`

### 式

$$\text{可測},\ \text{ほぼ確実に確率ベクトル}\ \Longrightarrow\ x\mapsto\mathrm{ent}(\text{mass}(x,\cdot))\ \text{は可積分}$$

### Lean のコメント（日本語訳）

> 有限の条件付き分布の可測性と正規化から、そのエントロピー密度の可積分性が出る：各確率は 1 以下で、有限のエントロピーの和は、前の一様な上界をもつ。

### 補題の説明

確率測度の上で、有界な可測関数は可積分です。

### 証明の概略

1. エントロピー密度はほぼ確実に \(|G|\) 以下（前の補題）。
2. 有界・可測・確率測度（有限測度）なので可積分（`Integrable.of_bound`、7 行）。

----

<a id="Tomabechi.Theorem21.conditionalGoalEntropy"></a>

## 定義 `conditionalGoalEntropy`

### 式

$$H(G\mid X)=\int\mathrm{ent}(\text{mass}(x,\cdot))\,d\mu(x)$$

### Lean のコメント（日本語訳）

> 有限の目標の、一般の可測な入力に関する条件付きエントロピー。有限の条件付きエントロピー密度の積分として定義する。

### 定義の説明

入力が一般の測度空間のときの \(H(G|X)\) です。有限入力のときは、`finiteConditionalEntropyGivenInput` と一致します（入力が Dirac 測度の混合のとき）。

### 証明の概略

1. 定義：`∫ x, conditionalGoalEntropyAt (mass x) ∂μ`。

----


## コメント修正記録

（なし）
