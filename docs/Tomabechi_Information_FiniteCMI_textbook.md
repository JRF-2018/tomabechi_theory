# Tomabechi/Information/FiniteCMI.lean 解説

> 対象: [`Tomabechi/Information/FiniteCMI.lean`](../Tomabechi/Information/FiniteCMI.lean)（定理21の有限ゴール・決定論的出力に対するエントロピー差）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の**情報理論的な結論**（「行動が目標を区別するなら、条件付き相互情報量は目標の条件付きエントロピーに等しく、正になる」）を、
**有限個の確率質量**だけで述べて証明する、純粋に代数的・計算的な核です。測度論は使いません。

- 入力（文脈）\(X\)、目標 \(G\)、出力 \(Y=\text{action}(X,G)\) はすべて**有限集合**。
- 同時の質量 \(\text{mass}(x,g)\ge0\) が与えられます。
- 条件付きエントロピー \(H(G|X)\)、残余エントロピー \(H(G|X,Y)\)、条件付き相互情報量 \(I(G;Y|X)=H(G|X)-H(G|X,Y)\) を定義し、
  **非負性**・**上界**・**定理21の結論**を示します。

### 0.2 エントロピーの項

\(-p\log(p/q)\)（\(p=0\) のときは 0 と定める）を基本の項とします。\(p\) は同時の質量、\(q\) は条件づけるファイバー（グループ）の質量の合計です。

### 0.3 このファイルが証明していないこと

- 変数は有限です。一般の測度空間の場合は `FiniteMeasureEntropy.lean`・`DeterministicOutput.lean` が扱います。
- ここでの条件付き相互情報量は**エントロピーの差**として定義したものです。KL ダイバージェンスから作る定義（`Theorem21.lean` 系の KL 型）との同一視は、このファイルでは主張しません。
- 「残余エントロピーが 0」は、行動が目標を区別する（台の上で単射）という**仮定**から導きます。この仮定を論文のモデルで確かめることは別の課題です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の有限 CMI 情報核**
>
> 旧 `Theorem21.lean` の、有限ゴール・決定論的出力に対するエントロピー差の API。最適化・ODE・平均場の段階から独立した計算核として、名前空間と公開宣言名を保つ。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem21`。

---

<a id="Tomabechi.Theorem21.finiteConditionalEntropyTerm"></a>

## 定義 `finiteConditionalEntropyTerm`

### 式

$$h(p,q)=\begin{cases}0&(p=0)\\-p\log(p/q)&(p\ne0)\end{cases}$$

### Lean のコメント（日本語訳）

> 有限の条件付きエントロピーで使う和の各項 \(-p\log(p/q)\)。\(p=0\) の場合は 0 と定義し、確率の計算で \(\log0\) の規約を避ける。

### 定義の説明

エントロピーの 1 項です。\(p\) は 1 つの目標の質量、\(q\) はその目標が属するグループの質量の合計。\(p/q\) は条件付き確率で、\(-p\log(p/q)\) が「情報量×重み」です。\(p=0\) のとき \(\log 0\) が現れないよう 0 と定めます。

### 証明の概略

1. 定義：`if p = 0 then 0 else -p * Real.log (p / q)`。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyGivenInput"></a>

## 定義 `finiteConditionalEntropyGivenInput`

### 式

$$H(G\mid X)=\sum_x\sum_g h\Bigl(\text{mass}(x,g),\ \sum_{g'}\text{mass}(x,g')\Bigr)$$

### Lean のコメント（日本語訳）

> 有限の目標変数 \(G\) の、有限の文脈変数 \(X\) が与えられたもとでの条件付きエントロピー。両者の同時の確率質量から直接表現する。

### 定義の説明

入力 \(x\) ごとの「目標の不確かさ」を足し合わせたものです。分母 \(q\) は、その入力 \(x\) での全目標の質量の合計です（正規化されていれば周辺確率）。

### 証明の概略

1. 定義：二重和（`Finset.sum`）。分母は `∑ g', mass x g'`。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyGivenInputAndOutput"></a>

## 定義 `finiteConditionalEntropyGivenInputAndOutput`

### 式

$$H(G\mid X,Y)=\sum_x\sum_g h\Bigl(\text{mass}(x,g),\ \sum_{g':\,\text{action}(x,g')=\text{action}(x,g)}\text{mass}(x,g')\Bigr)$$

### Lean のコメント（日本語訳）

> \(X\) と決定論的な出力 \(\text{action}(X,G)\) を観測した後の、\(G\) の残余の条件付きエントロピー。観測された各 \((x,y)\) について、分母は、その出力を生む目標すべての同時質量である。

### 定義の説明

行動の結果（出力）を見たあとに残る不確かさです。出力が同じ目標どうしを 1 つの「ファイバー（同値類）」にまとめ、そのファイバー内での条件付き確率でエントロピーを測ります。出力が目標を完全に区別すれば、各ファイバーは 1 つの目標だけで、この値は 0 になります。

### 証明の概略

1. 定義：二重和。分母は `∑ g', if action x g' = action x g then mass x g' else 0`（ファイバーの質量）。

----

<a id="Tomabechi.Theorem21.finiteConditionalMutualInformation"></a>

## 定義 `finiteConditionalMutualInformation`

### 式

$$I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)$$

### Lean のコメント（日本語訳）

> 決定論的な出力についての有限の条件付き相互情報量。標準的なエントロピーの差 \(H(G|X)-H(G|X,Y)\) で定義する。

### 定義の説明

「出力を観測することで、目標について得られる情報量」です。観測前の不確かさ \(H(G|X)\) から観測後の不確かさ \(H(G|X,Y)\) を引きます。

### 証明の概略

1. 定義：二つのエントロピーの差。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyTerm_difference_nonneg"></a>

## 補題 `finiteConditionalEntropyTerm_difference_nonneg`

### 式

$$0\le p\le q\le\text{total}\ \Longrightarrow\ h(p,\text{total})-h(p,q)\ge0$$

### Lean のコメント（日本語訳）

> 非負のエントロピー質量の分母を大きくすると、そのエントロピーへの寄与は増えるだけである。このスカラーの不等式が、決定論的な条件付き相互情報量の非負性の鍵となる事実である。

### 補題の説明

分母（条件づけるグループの質量）が大きいほど、条件付き確率 \(p/q\) は小さくなり、不確かさ \(-p\log(p/q)\) は大きくなります。

### 証明の概略

1. \(p=0\) なら両辺 0。\(p>0\) なら \(0<q\le\text{total}\)。
2. 差 \(=p\bigl(\log(\text{total}/q)\bigr)\)（\(\log(p/\text{total})\) と \(\log(p/q)\) の差）。
3. \(\text{total}/q\ge1\) より \(\log\ge0\)、\(p\ge0\) なので差は非負（18 行）。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyTerm_nonneg_of_le"></a>

## 補題 `finiteConditionalEntropyTerm_nonneg_of_le`

### 式

$$0\le p\le q\ \Longrightarrow\ h(p,q)\ge0$$

### Lean のコメント（日本語訳）

> 有限の条件付きエントロピーへの寄与は、その質量が条件づけるファイバーを超えない限り、非負である。

### 補題の説明

条件付き確率 \(p/q\le1\) なので \(\log(p/q)\le0\)、したがって \(-p\log(p/q)\ge0\) です。

### 証明の概略

1. \(p=0\) は自明。\(0<p\le q\) なら \(p/q\in(0,1]\)、\(\log(p/q)\le0\)。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyTerm_le_denominator"></a>

## 補題 `finiteConditionalEntropyTerm_le_denominator`

### 式

$$0\le p\le q\ \Longrightarrow\ h(p,q)\le q$$

### Lean のコメント（日本語訳）

> 有限の条件付きエントロピーへの寄与は、その分母で上から抑えられる。この不等式は、\([0,1]\) 上で \(-r\log r\le1-r\) が成り立つことから出る。

### 補題の説明

1 項のエントロピーは、グループの質量 \(q\) を超えません。後で、総エントロピーの粗い上界（目標の個数×全質量）を出すのに使います。

### 証明の概略

1. \(r=p/q\in[0,1]\)。\(h(p,q)=-q\,r\log r\)。
2. \(-r\log r\le1-r\le1\)（\(\log r\ge1-1/r\) の変形）から \(h\le q\)（21 行）。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyGivenInput_le_card_mul_total"></a>

## 補題 `finiteConditionalEntropyGivenInput_le_card_mul_total`

### 式

$$H(G\mid X)\le|G|\cdot\sum_{x,g}\text{mass}(x,g)$$

### Lean のコメント（日本語訳）

> 非負の有限の同時質量については、条件付きエントロピーは、目標の文字の数と総質量の積で上から抑えられる。特に、正規化されたモデルでは、条件付きエントロピーは高々 `card G` である。

### 補題の説明

エントロピーの粗い上界です（\(\log|G|\) よりずっと粗いですが、有限性・可積分性の議論には十分）。

### 証明の概略

1. 各項を `finiteConditionalEntropyTerm_le_denominator` で分母（入力 \(x\) の質量）以下に抑える。
2. \(x\) ごとの質量の和を、目標の個数 \(|G|\) 倍して全体の和に直す（26 行）。

----

<a id="Tomabechi.Theorem21.finiteConditionalEntropyGivenInputAndOutput_nonneg"></a>

## 補題 `finiteConditionalEntropyGivenInputAndOutput_nonneg`

### 式

$$H(G\mid X,Y)\ge0$$

### Lean のコメント（日本語訳）

> 決定論的な観測の後の残余の条件付きエントロピーは非負である：各目標の質量は、その出力のファイバーの質量で抑えられる。

### 補題の説明

各項が `finiteConditionalEntropyTerm_nonneg_of_le` により非負なので、和も非負です。

### 証明の概略

1. `Finset.sum_nonneg` を二重に適用。
2. 各項で、自分の質量 \(\le\) ファイバーの質量（ファイバーは自分を含む非負の和）。

----

<a id="Tomabechi.Theorem21.finiteConditionalMutualInformation_le_entropy"></a>

## 補題 `finiteConditionalMutualInformation_le_entropy`

### 式

$$I(G;Y\mid X)\le H(G\mid X)$$

### Lean のコメント（日本語訳）

> 決定論的な条件付き相互情報量は、残余の条件付きエントロピーが非負なので、入力の条件付きエントロピーを超えない。

### 補題の説明

得られる情報は、もともとの不確かさを超えません。

### 証明の概略

1. \(I=H(G|X)-H(G|X,Y)\) と \(H(G|X,Y)\ge0\) から直ちに。

----

<a id="Tomabechi.Theorem21.finiteConditionalMutualInformation_le_card_mul_total"></a>

## 補題 `finiteConditionalMutualInformation_le_card_mul_total`

### 式

$$I(G;Y\mid X)\le|G|\cdot\sum_{x,g}\text{mass}(x,g)$$

### Lean のコメント（日本語訳）

> 非負の有限の同時質量は、決定論的な条件付き相互情報量を、目標の文字の数と総質量の積で抑える。

### 補題の説明

上の 2 つの上界の組み合わせです。

### 証明の概略

1. `finiteConditionalMutualInformation_le_entropy` と `finiteConditionalEntropyGivenInput_le_card_mul_total` をつなぐ。

----

<a id="Tomabechi.Theorem21.finiteConditionalMutualInformation_nonneg"></a>

## 補題 `finiteConditionalMutualInformation_nonneg`

### 式

$$\text{mass}\ge0\ \Longrightarrow\ I(G;Y\mid X)\ge0$$

### Lean のコメント（日本語訳）

> 決定論的な出力の条件付き相互情報量は、すべての非負の有限の同時質量について非負である。証明は、各入力での総質量と、現在の目標を含む出力ファイバーの質量とを、項ごとに比べる。正規化の仮定は要らない。

### 補題の説明

情報量は負にならない、というよく知られた性質を、有限の場合に直接示したものです（正規化しなくても成り立つ）。

### 証明の概略

1. 差を項ごとにまとめる（`Finset.sum_sub_distrib`）。各項は \(h(p,\text{total})-h(p,\text{fiber})\)。
2. \(p\le\text{fiber}\le\text{total}\)（`hpq`, `hqt`）なので、`finiteConditionalEntropyTerm_difference_nonneg` により各項が非負（38 行）。

----

<a id="Tomabechi.Theorem21.theorem21_finite_information_capacity"></a>

## 定理 `theorem21_finite_information_capacity`

### 式

$$\text{action が台上で目標を区別},\ H(G\mid X)>0\ \Longrightarrow\ I(G;Y\mid X)=H(G\mid X)\ \wedge\ I(G;Y\mid X)>0$$

### Lean のコメント（日本語訳）

> 有限の変数についての、定理21の情報理論的な節。行動が、ある文脈で正の条件付き質量をもつ目標の値のどの対も区別するなら、\((X,\text{action}(X,G))\) を観測することは \(G\) をほぼ確実に決定する。したがって \(I(G;Y|X)=H(G|X)\) であり、残余の目標のエントロピーが正であるという仮定から、条件付き相互情報量は厳密に正になる。

### 補題の説明

**定理21の情報容量の結論（有限版）**：行動が目標を区別する（台の上で単射）なら、観測後の不確かさは 0（\(H(G|X,Y)=0\)）なので、条件付き相互情報量は \(H(G|X)\) に等しく、不確かさが正なら情報量も正です。

### 証明の概略

1. 各項の残余エントロピーが 0：単射性から、質量が正の目標のファイバーは自分だけなので、分母＝自分の質量、\(h(p,p)=-p\log1=0\)（質量 0 なら項も 0）。
2. よって \(H(G|X,Y)=0\)、\(I=H(G|X)\)（`Finset.sum_eq_zero`）。
3. \(H(G|X)>0\) の仮定から \(I>0\)（34 行）。

----


## コメント修正記録

（なし）
