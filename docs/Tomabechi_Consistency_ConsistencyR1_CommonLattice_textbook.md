# Tomabechi/Consistency/ConsistencyR1_CommonLattice.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_CommonLattice.lean`](../Tomabechi/Consistency/ConsistencyR1_CommonLattice.lean)（全定理で共通に使う概念束 `CommonConcept` と、層・記号・区間の順序を保つ埋め込み）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文の複数の定理は、「概念」「記号の情報」「層の番号（抽象度）」を、**同じ一つの順序の構造**の上で語っています。以前のモデルでは、これらがそれぞれ別の型で作られていて、「同じものを指す」ことの保証がありませんでした。このファイルは、**共通の完備束** `CommonConcept` \(=[0,1]^2\) を作り、三者をそこへ順序を保って埋め込みます。

| 埋め込む対象 | 方法 | 主な性質 |
| --- | --- | --- |
| 層の番号（自然数と頂） | 対角線上の点 \((\tfrac n{n+1},\tfrac n{n+1})\)。頂は束の頂 | 順序を保つ。有限層は頂の下。上に有向で最大元がない。上限は頂 |
| 単位区間 | 第 \(i\) 座標に置き、他は 0 | 順序を保つ・反映する |
| 記号の有限集合 | 0/1 指示関数 | 包含が順序、和集合が結び、共通部分が交わり、空集合が最小元、全体が頂 |

さらに、束の点から層の番号へ戻す**投影**（`layerProjection`）と、番号で定義されたデータを束全体へ延長する関数（`extendLayerData`）を与えます。

無矛盾性の証明（[見取り図](Consistency_Overview.md)）では、「共通の概念束」（R1）の土台です。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、ここは**束への保存つき埋め込みの基礎**で、既存の定理群や統合モデルへの接続は別に必要です。
* 束は二つの座標で作った**具体的な選択**です（原文が束の具体形を指定しているわけではありません）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 有限個の座標を持つ単位区間の積を、概念・記号情報・層添字を接続する共通束の候補として用いる。このファイルは束への保存付き埋込みの基礎を与える。既存の定理群や統合モデルへの接続は別途必要である。

---

<a id="Tomabechi.Consistency.R1.CommonConcept"></a>

## 定義 `CommonConcept`

### 式

$$
[0,1]^2
$$

### Lean のコメント（日本語訳）

> 二つの座標を持つ共通概念束。順序と束演算は座標ごとに定める。

### 定義の説明

全定理が共通に使う**概念の束**（完備束）です。単位区間 \([0,1]\) を二つ並べた積 \([0,1]^2\) で、順序と結び・交わりは座標ごとに決めます。最小元は \((0,0)\)、最大元（頂、「空」に当たる元）は \((1,1)\) です。層の番号・記号の情報・抽象度は、すべてこの束の点として表します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.layerRatio"></a>

## 定義 `layerRatio`

### 式

$$
\frac{n}{n+1}
$$

### Lean のコメント（日本語訳）

> Nat段を共通束の対角線上へ送るための有理数列 `n/(n+1)`。

### 定義の説明

段の番号 \(n=0,1,2,\dots\) を、\(0,\tfrac12,\tfrac23,\dots\) と、1 に近づく数列にします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.layerRatio_nonneg"></a>

## 補題 `layerRatio_nonneg`

### 式

$$
0\le\tfrac{n}{n+1}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

数列は 0 以上です。

### 証明の概略

1. 分子 \(n\ge0\)、分母 \(n+1>0\)。

----

<a id="Tomabechi.Consistency.R1.layerRatio_lt_one"></a>

## 補題 `layerRatio_lt_one`

### 式

$$
\tfrac{n}{n+1}<1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

数列は 1 より小さいです（1 には届かない）。

### 証明の概略

1. \(n<n+1\) から、`div_lt_one`。

----

<a id="Tomabechi.Consistency.R1.layerRatio_strictMono"></a>

## 補題 `layerRatio_strictMono`

### 式

$$
m<n\Rightarrow\tfrac{m}{m+1}<\tfrac{n}{n+1}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

数列は狭義に増加します。

### 証明の概略

1. 分母を払って（`div_lt_div_iff₀`）、\(m(n+1)<n(m+1)\iff m<n\)（`nlinarith`）。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer"></a>

## 定義 `diagonalLayer`

### 式

$$
n\mapsto\bigl(\tfrac{n}{n+1},\tfrac{n}{n+1}\bigr)
$$

### Lean のコメント（日本語訳）

> 各Nat層を共通束の対角上に配置する。すべての有限層は共通の頂より下にある。

### 定義の説明

自然数の層 \(n\) を、共通束の対角線上の点 \((\tfrac n{n+1},\tfrac n{n+1})\) に置きます。どの有限層も、頂 \((1,1)\) より真に下にあります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer_strictMono"></a>

## 補題 `diagonalLayer_strictMono`

### 式

$$
m<n\Rightarrow\mathrm{layer}(m)<\mathrm{layer}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角の層は、狭義に増加します。

### 証明の概略

1. 各座標で狭義に増加（`layerRatio_strictMono`）なので \(\le\)。
2. 逆向きの \(\le\) が成り立てば、0 番座標で矛盾する。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer_le_iff"></a>

## 補題 `diagonalLayer_le_iff`

### 式

$$
\mathrm{layer}(m)\le\mathrm{layer}(n)\iff m\le n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角の層の順序は、自然数の順序と一致します。

### 証明の概略

1. （→）\(n<m\) なら \(\mathrm{layer}(n)<\mathrm{layer}(m)\) で矛盾。（←）単調性。

----

<a id="Tomabechi.Consistency.R1.exists_diagonalLayer_strictly_above"></a>

## 補題 `exists_diagonalLayer_strictly_above`

### 式

$$
\forall n\ \exists m,\ \mathrm{layer}(n)<\mathrm{layer}(m)
$$

### Lean のコメント（日本語訳）

> 対角層列はどの有限段よりも後の段を持つので、最大層を持たない。

### 補題の説明

どの有限段にも、それより真に上の段があります（最大の有限層はありません）。

### 証明の概略

1. \(m=n+1\) を取り、狭義単調性を使う。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer_pair_has_upper"></a>

## 補題 `diagonalLayer_pair_has_upper`

### 式

$$
\exists k,\ \mathrm{layer}(m)\le\mathrm{layer}(k)\wedge\mathrm{layer}(n)\le\mathrm{layer}(k)
$$

### Lean のコメント（日本語訳）

> 二つのNat層には、その両方以上となる対角層がある。

### 補題の説明

どの二つの有限層にも、その両方以上の層があります（有向）。

### 証明の概略

1. \(k=\max(m,n)\) を取り、単調性を使う。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer_lt_top"></a>

## 補題 `diagonalLayer_lt_top`

### 式

$$
\mathrm{layer}(n)<\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

どの有限層も、束の頂より真に下です。

### 証明の概略

1. 各座標で \(<1\)。頂以上だと \(1\le\tfrac n{n+1}\) となり矛盾。

----

<a id="Tomabechi.Consistency.R1.diagonalLayer_range_isLUB_top"></a>

## 補題 `diagonalLayer_range_isLUB_top`

### 式

$$
\sup_n\mathrm{layer}(n)=\top
$$

### Lean のコメント（日本語訳）

> 対角Nat層は共通束の頂点へ近づき、その上限は頂点そのものになる。

### 補題の説明

対角の層の最小上界（上限）は、束の頂そのものです。有限層は頂に限りなく近づきます。

### 証明の概略

1. 頂は上界（`le_top`）。
2. 他の上界 \(b\) は、各座標で \(\tfrac n{n+1}\le b_i\)（全 \(n\)）を満たすので、\(b_i\ge1\)（極限）。したがって頂 \(\le b\)。

----

<a id="Tomabechi.Consistency.R1.layerAddress"></a>

## 定義 `layerAddress`

### 式

$$
n\mapsto\mathrm{layer}(n),\quad\top\mapsto\top
$$

### Lean のコメント（日本語訳）

> 既存の有限Nat層と無限頂点を、同じ共通束の対角列と頂点へ移す写像。

### 定義の説明

以前の層の番号（自然数に頂 `⊤` を加えたもの）を、共通束の点に移す写像です。有限層は対角線上の点へ、頂は束の頂へ送ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.layerAddress_top"></a>

## 補題 `layerAddress_top`

### 式

$$
\mathrm{layerAddress}(\top)=\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂は頂に移ります。

### 証明の概略

1. 定義を展開する（`simp`）。

----

<a id="Tomabechi.Consistency.R1.layerAddress_nat"></a>

## 補題 `layerAddress_nat`

### 式

$$
\mathrm{layerAddress}(n)=\mathrm{layer}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自然数 \(n\) は、対角の層 \(n\) に移ります。

### 証明の概略

1. 定義そのもの（`rfl`）。

----

<a id="Tomabechi.Consistency.R1.layerAddressEmbedding"></a>

## 定義 `layerAddressEmbedding`

### 式

$$
a\le b\iff\mathrm{layerAddress}(a)\le\mathrm{layerAddress}(b)
$$

### Lean のコメント（日本語訳）

> 有限Nat段と無限頂を共通束の対角鎖と束頂へ移す順序埋込み。

### 定義の説明

`layerAddress` が、**順序を保つ埋め込み**であること（\(a\le b\iff\) 像でも \(\le\)）を述べ、埋め込みとしてまとめたものです。無矛盾性の追加条件の「層の添字が順序と頂を保つ」の根拠になります。

### 証明の概略

1. 場合分け（\(a,b\) が頂か自然数か）で、順序の同値を示す。
2. 頂と有限層の比較は、有限層が頂より真に下（`diagonalLayer_lt_top`）であることから。有限層同士は `diagonalLayer_le_iff`。

----

<a id="Tomabechi.Consistency.R1.layerProjection"></a>

## 定義 `layerProjection`

### 式

$$
x\mapsto\sup\{k\mid\mathrm{layer}(k)\le x\}
$$

### Lean のコメント（日本語訳）

> 任意の共通束点を、その下にある最大の対角Nat層へ戻す単調な層番号。

### 定義の説明

束の任意の点 \(x\) に対し、\(x\) 以下の対角層の番号の上限を返す写像です（束の点から層の番号へ戻す写像）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.layerProjection_monotone"></a>

## 補題 `layerProjection_monotone`

### 式

$$
x\le y\Rightarrow\mathrm{proj}(x)\le\mathrm{proj}(y)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

投影は単調です。

### 証明の概略

1. \(x\) 以下の層は、\(y\) 以下でもある。上限の単調性（`iSup_le`、`le_iSup_of_le`）。

----

<a id="Tomabechi.Consistency.R1.layerProjection_diagonal"></a>

## 補題 `layerProjection_diagonal`

### 式

$$
\mathrm{proj}(\mathrm{layer}(n))=n
$$

### Lean のコメント（日本語訳）

> 投影は各有限Nat層で元の層番号を正確に返す。

### 補題の説明

対角の層 \(n\) の投影は、ちょうど \(n\) です。

### 証明の概略

1. （≤）層 \(m\) が層 \(n\) 以下なら \(m\le n\)（`diagonalLayer_le_iff`）。
2. （≥）\(n\) 自身が上限の候補。

----

<a id="Tomabechi.Consistency.R1.layerProjection_layerAddress"></a>

## 補題 `layerProjection_layerAddress`

### 式

$$
\mathrm{proj}(\mathrm{layerAddress}(a))=a
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の番号を束に移して投影すると、元の番号に戻ります（頂も）。

### 証明の概略

1. 自然数の場合は前の補題。
2. 頂の場合は、頂以下の層の番号の集合が上に有界でない（任意の \(b\) に対し \(b+1\) が入る）ので、上限は \(\top\)。

----

<a id="Tomabechi.Consistency.R1.layerProjection_lt_top_of_lt_top"></a>

## 補題 `layerProjection_lt_top_of_lt_top`

### 式

$$
x<\top\Rightarrow\mathrm{proj}(x)<\top
$$

### Lean のコメント（日本語訳）

> 下限層投影は、共通束の真部分点を頂添字へ誤って送らない。

### 補題の説明

束の頂より真に下の点は、投影しても頂の番号にはなりません。

### 証明の概略

1. 頂の番号になるとすると、\(x\) 以下の層の番号が上に有界でない。
2. すると、すべての対角層が \(x\) 以下となり、その上限である頂も \(x\) 以下（`diagonalLayer_range_isLUB_top`）。\(x<\top\) に矛盾。

----

<a id="Tomabechi.Consistency.R1.extendLayerData"></a>

## 定義 `extendLayerData`

### 式

$$
f\mapsto f\circ\mathrm{proj}
$$

### Lean のコメント（日本語訳）

> 既存のNat/頂添字データを、新しい共通束全体へ延長する関数。

### 定義の説明

自然数と頂の番号で定義されたデータ \(f\) を、束の全体へ延長します（\(x\) には \(f(\mathrm{proj}(x))\) を割り当てる）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.extendLayerData_on_oldAddress"></a>

## 補題 `extendLayerData_on_oldAddress`

### 式

$$
\text{延長}(\mathrm{layerAddress}(a))=f(a)
$$

### Lean のコメント（日本語訳）

> 延長データは埋込み像上で元の有限層/頂データを厳密に回収する。

### 補題の説明

延長したデータは、埋め込みの像の上で、元のデータにちょうど一致します。

### 証明の概略

1. 投影が元の番号に戻す（`layerProjection_layerAddress`）。

----

<a id="Tomabechi.Consistency.R1.extendLayerData_top"></a>

## 補題 `extendLayerData_top`

### 式

$$
\text{延長}(\top)=f(\top)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂での延長は、元の頂のデータに一致します。

### 証明の概略

1. `extendLayerData_on_oldAddress` を頂に適用する。

----

<a id="Tomabechi.Consistency.R1.extendLayerData_monotone"></a>

## 補題 `extendLayerData_monotone`

### 式

$$
f\ \text{単調}\Rightarrow\text{延長も単調}
$$

### Lean のコメント（日本語訳）

> 層順序に関して単調な既存データは、全共通束上への延長後も単調である。

### 補題の説明

元のデータが層の順序について単調なら、延長したデータも束の順序について単調です。

### 証明の概略

1. \(x\le y\) なら投影が単調（`layerProjection_monotone`）。\(f\) の単調性を合成する。

----

<a id="Tomabechi.Consistency.R1.coordinateEmbedding"></a>

## 定義 `coordinateEmbedding`

### 式

$$
x\mapsto(0,\dots,x,\dots,0)
$$

### Lean のコメント（日本語訳）

> 各座標の単位区間を、他座標を底に固定して共通束へ埋め込む。

### 定義の説明

単位区間 \([0,1]\) を、第 \(i\) 座標に置き、他の座標は 0 にして、束へ埋め込む写像です。順序を保ち、順序を反映します。

### 証明の概略

1. 順序の同値：（→）第 \(i\) 座標を見る。（←）\(i\) 座標は仮定、他の座標は 0 で等しい。

----

<a id="Tomabechi.Consistency.R1.coordinateEmbedding_apply_self"></a>

## 補題 `coordinateEmbedding_apply_self`

### 式

$$
\mathrm{emb}_i(x)_i=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 \(i\) 座標には \(x\) が入ります。

### 証明の概略

1. 定義の展開（`simp`）。

----

<a id="Tomabechi.Consistency.R1.coordinateEmbedding_apply_other"></a>

## 補題 `coordinateEmbedding_apply_other`

### 式

$$
j\ne i\Rightarrow\mathrm{emb}_i(x)_j=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

他の座標は 0 です。

### 証明の概略

1. 定義の展開（`simp`）。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding"></a>

## 定義 `finiteSymbolsEmbedding`

### 式

$$
s\mapsto\bigl(\mathbf 1[0\in s],\ \mathbf 1[1\in s]\bigr)
$$

### Lean のコメント（日本語訳）

> 有限記号集合を0/1指示関数へ移す。有限集合の包含は座標ごとの順序と同値。

### 定義の説明

二つの記号の部分集合 \(s\subseteq\{0,1\}\) を、0/1 の指示関数（\(i\in s\) なら 1、そうでなければ 0）として、束の点に移します。集合の包含 \(\subseteq\) が、座標ごとの順序 \(\le\) と同値です。

### 証明の概略

1. 順序の同値：（→）\(i\in s\) の座標が 1 以上、なので \(i\in t\)。（←）包含なら、各座標で指示関数が大小関係を保つ。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_apply"></a>

## 補題 `finiteSymbolsEmbedding_apply`

### 式

$$
\mathrm{emb}(s)_i=\mathbf 1[i\in s]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

像の座標は、指示関数の値です。

### 証明の概略

1. 定義そのもの（`rfl`）。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_le_iff"></a>

## 補題 `finiteSymbolsEmbedding_le_iff`

### 式

$$
\mathrm{emb}(s)\le\mathrm{emb}(t)\iff s\subseteq t
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

像の順序と、集合の包含は同値です。

### 証明の概略

1. 順序埋め込みの性質（`le_iff_le`）。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_union"></a>

## 補題 `finiteSymbolsEmbedding_union`

### 式

$$
\mathrm{emb}(s\cup t)=\mathrm{emb}(s)\sqcup\mathrm{emb}(t)
$$

### Lean のコメント（日本語訳）

> 有限記号の和集合は、共通束上のjoinへそのまま移る。

### 補題の説明

集合の和集合は、束の結び（join）に移ります。

### 証明の概略

1. 各座標で、\(i\in s\) か \(i\in t\) かの場合分け（`by_cases`）。指示関数の最大が結びになる。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_inter"></a>

## 補題 `finiteSymbolsEmbedding_inter`

### 式

$$
\mathrm{emb}(s\cap t)=\mathrm{emb}(s)\sqcap\mathrm{emb}(t)
$$

### Lean のコメント（日本語訳）

> 有限記号の共通部分は、共通束上のmeetへそのまま移る。

### 補題の説明

共通部分は、束の交わり（meet）に移ります。

### 証明の概略

1. 各座標で場合分けして計算する（`simp`）。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_empty"></a>

## 補題 `finiteSymbolsEmbedding_empty`

### 式

$$
\mathrm{emb}(\emptyset)=\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

空集合は最小元 \((0,0)\) に移ります。

### 証明の概略

1. 各座標で \(i\notin\emptyset\)、値は 0。

----

<a id="Tomabechi.Consistency.R1.finiteSymbolsEmbedding_univ"></a>

## 補題 `finiteSymbolsEmbedding_univ`

### 式

$$
\mathrm{emb}(\{0,1\})=\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全体は頂 \((1,1)\) に移ります。

### 証明の概略

1. 各座標で \(i\in\mathrm{univ}\)、値は 1。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
