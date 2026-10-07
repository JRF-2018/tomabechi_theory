# Tomabechi/Consistency/ConsistencyR1_C1Information.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C1Information.lean`](../Tomabechi/Consistency/ConsistencyR1_C1Information.lean)（定理19の情報と定理20の象徴データを、共通束の上に載せる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19（情報）と定理20（象徴）のデータを、**共通束 `CommonConcept` の上**に載せるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）の一部です。

* **定理19の情報の法則を、共通束の全点へ延長**：最小元（物理層）では「ゴールの情報が出力に伝わらない」法則（スコア 0）、それ以外の全点では「完全に伝わる」法則（スコア \(\log2>0\)）。層の番号 0 は底、正の番号は底以外に移ります。
* **定理20の有限情報束（\(\{\emptyset,\{0\}\}\)）を共通束の部分集合として表す**：記号の埋め込みの像。結び・交わりで閉じ、真部分集合で、アドレスの像は象徴の像の LUB。

### 0.2 このファイルが証明していないこと

* 情報の法則は、このモデルのために置いた**具体的な法則**（底とそれ以外の二種類）です。
* 全点で同じ上位層の法則を使います。層ごとに異なる情報量を割り当てるわけではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理20の二主体有限情報束を、共通概念束の0/1指示関数部分へ写す。有限集合の演算と順序は共通束側でも保存される。

---

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw"></a>

## 定義 `commonConceptInformationLaw`

### 式

$$
a\mapsto\begin{cases}\text{物理層の法則}&a=\bot\\\text{上位層の法則}&a\ne\bot\end{cases}
$$

### Lean のコメント（日本語訳）

> 定理19の情報lawを全共通束へ延長する。底では物理層lawを保ち、底以外の全概念点では同じ正情報lawを使う。

### 定義の説明

定理19の情報の法則（入力・ゴール・出力の同時分布）を、共通束の**すべての点**に割り当てます。最小元 \(\bot\)（物理層）では物理層の法則を、\(\bot\) 以外のすべての点では同じ「正の情報」を持つ上位層の法則を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair"></a>

## 定義 `commonConceptInformationPair`

### 式

$$
a\mapsto(\text{joint},\ \text{reference})
$$

### Lean のコメント（日本語訳）

> 情報lawからTheorem 19のjoint/reference問題を同時に構成する。

### 定義の説明

情報の法則から、定理19の条件付き相互情報量（CMI）を計算するための二つの分布（結合分布 `joint` と参照分布 `reference`）の組を作ります。底では物理層の組、それ以外では上位層の組です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_bottom"></a>

## 補題 `commonConceptInformationLaw_bottom`

### 式

$$
\mathrm{Law}(\bot)=\text{物理層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底での法則は、物理層の法則です。

### 証明の概略

1. `if a = ⊥` の条件が成り立つ（`simp`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_of_ne_bottom"></a>

## 補題 `commonConceptInformationLaw_of_ne_bottom`

### 式

$$
a\ne\bot\Rightarrow\mathrm{Law}(a)=\text{上位層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底以外では、上位層の法則です。

### 証明の概略

1. `if` の条件が偽（`simp`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_isProbability"></a>

## 補題 `commonConceptInformationLaw_isProbability`

### 式

$$
\mathrm{Law}(a)\ \text{は確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

どの点でも、法則は確率測度です（全質量 1）。

### 証明の概略

1. 底の場合と底以外の場合に分けて、それぞれの確率測度性を使う。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair_joint_eq"></a>

## 補題 `commonConceptInformationPair_joint_eq`

### 式

$$
\text{法則から作った結合分布}=\text{組の joint}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

法則から直接作った結合分布は、組の `joint` に一致します。

### 証明の概略

1. 底かどうかで場合分けして、定義を展開して一致を示す。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair_reference_eq"></a>

## 補題 `commonConceptInformationPair_reference_eq`

### 式

$$
\text{法則から作った参照分布}=\text{組の reference}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

法則から直接作った参照分布は、組の `reference` に一致します。

### 証明の概略

1. 底かどうかで場合分け。確率測度であることの型クラスの引数を整えて、定義を展開して一致を示す。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair_score_bottom"></a>

## 補題 `commonConceptInformationPair_score_bottom`

### 式

$$
I(\text{底})=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底（物理層）では、条件付き相互情報量のスコアは 0 です（ゴールの情報が出力に伝わらない）。

### 証明の概略

1. 底での組の定義を展開し、物理層の組のスコアが 0 であることを使う。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair_score_of_ne_bottom"></a>

## 補題 `commonConceptInformationPair_score_of_ne_bottom`

### 式

$$
a\ne\bot\Rightarrow I(a)=\log2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底以外では、スコアは \(\log2\) です（二値のゴールの情報が完全に伝わる）。

### 証明の概略

1. 上位層の組のスコアが \(\log2\) であることを使う。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationPair_score_positive_of_ne_bottom"></a>

## 補題 `commonConceptInformationPair_score_positive_of_ne_bottom`

### 式

$$
a\ne\bot\Rightarrow I(a)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底以外では、スコアは正です（非退化性）。

### 証明の概略

1. スコアが \(\log2\)（前の補題）で、\(\log2>0\)。

----

<a id="Tomabechi.Consistency.R1.layerAddress_zero_eq_bottom"></a>

## 補題 `layerAddress_zero_eq_bottom`

### 式

$$
\mathrm{layerAddress}(0)=\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の番号 0 は、束の最小元に移ります。

### 証明の概略

1. 対角の層 0 の座標は \(0/(0+1)=0\)（`simp`）。

----

<a id="Tomabechi.Consistency.R1.layerAddress_succ_ne_bottom"></a>

## 補題 `layerAddress_succ_ne_bottom`

### 式

$$
\mathrm{layerAddress}(n+1)\ne\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の番号 \(n+1\)（正の番号）は、最小元には移りません。

### 証明の概略

1. 最小元だとすると、座標が 0 になるが、\(\tfrac{n+1}{n+2}>0\) で矛盾。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_recovers_physical_address"></a>

## 補題 `commonConceptInformationLaw_recovers_physical_address`

### 式

$$
\mathrm{Law}(\mathrm{layerAddress}(0))=\text{物理層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

番号 0 の住所では、物理層の法則を回収します。

### 証明の概略

1. 住所 0 は底（前の補題）なので、底での法則。

----

<a id="Tomabechi.Consistency.R1.commonConceptInformationLaw_recovers_upper_address"></a>

## 補題 `commonConceptInformationLaw_recovers_upper_address`

### 式

$$
\mathrm{Law}(\mathrm{layerAddress}(n+1))=\text{上位層の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

正の番号の住所では、上位層の法則を回収します。

### 証明の概略

1. 正の番号の住所は底ではない（`layerAddress_succ_ne_bottom`）ので、底以外の法則。

----

<a id="Tomabechi.Consistency.R1.c1InformationImage"></a>

## 定義 `c1InformationImage`

### 式

$$
\mathrm{emb}(\{\emptyset,\{0\}\})
$$

### Lean のコメント（日本語訳）

> 定理20の有限情報束を共通束の部分集合として表したもの。

### 定義の説明

定理20の有限の情報束（\(\{\emptyset,\{0\}\}\)）を、共通束の部分集合として表したものです（記号の指示関数への埋め込みの像）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.c1SymbolImage"></a>

## 定義 `c1SymbolImage`

### 式

$$
\mathrm{emb}(W)
$$

### Lean のコメント（日本語訳）

> 定理20の象徴集合を共通束へ写した集合。

### 定義の説明

象徴の指示集合 \(W\) の、共通束での像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.c1SymbolAddressImage"></a>

## 定義 `c1SymbolAddressImage`

### 式

$$
\mathrm{emb}(\{0\})
$$

### Lean のコメント（日本語訳）

> 定理20の住所候補も同じ写像を通して共通束の元にする。

### 定義の説明

象徴のアドレス \(\{0\}\) の、共通束での像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.c1SymbolImage_subset_c1InformationImage"></a>

## 補題 `c1SymbolImage_subset_c1InformationImage`

### 式

$$
\mathrm{emb}(W)\subseteq\mathrm{emb}(\mathcal L)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

象徴の像は、情報束の像に含まれます。

### 証明の概略

1. 象徴の指示集合は情報束に含まれる（`c1SymbolW_subset_info`）。

----

<a id="Tomabechi.Consistency.R1.c1InformationImage_bottom"></a>

## 補題 `c1InformationImage_bottom`

### 式

$$
\bot\in\mathrm{emb}(\mathcal L)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最小元は、情報束の像に入ります。

### 証明の概略

1. 空集合の像は最小元（`finiteSymbolsEmbedding_empty`）。

----

<a id="Tomabechi.Consistency.R1.c1InformationImage_join_closed"></a>

## 補題 `c1InformationImage_join_closed`

### 式

$$
a,b\in\mathrm{emb}(\mathcal L)\Rightarrow a\sqcup b\in\mathrm{emb}(\mathcal L)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

情報束の像は、束の結びで閉じています。

### 証明の概略

1. 元の集合 \(x,y\) の和集合を取る。和集合は情報束に入る（`c1SymbolInfo_join_closed`）。像は結びに移る（`finiteSymbolsEmbedding_union`）。

----

<a id="Tomabechi.Consistency.R1.c1InformationImage_meet_closed"></a>

## 補題 `c1InformationImage_meet_closed`

### 式

$$
a,b\in\mathrm{emb}(\mathcal L)\Rightarrow a\sqcap b\in\mathrm{emb}(\mathcal L)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

情報束の像は、束の交わりで閉じています。

### 証明の概略

1. 共通部分を取る。共通部分は情報束に入る。像は交わりに移る（`finiteSymbolsEmbedding_inter`）。

----

<a id="Tomabechi.Consistency.R1.c1InformationImage_proper"></a>

## 補題 `c1InformationImage_proper`

### 式

$$
\mathrm{emb}(\mathcal L)\ne\text{全体}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

情報束の像は、共通束全体ではありません（真部分集合）。

### 証明の概略

1. 全体だと仮定して、第 1 座標だけが 1 の点が像に入る。すると、元の集合 \(s\) の指示関数が \((0,1)\) になるが、\(s\) は \(\emptyset\) か \(\{0\}\) で、どちらも矛盾。

----

<a id="Tomabechi.Consistency.R1.c1SymbolImage_eq_singleton"></a>

## 補題 `c1SymbolImage_eq_singleton`

### 式

$$
\mathrm{emb}(W)=\{\mathrm{emb}(\{0\})\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

象徴の像は、アドレスの像だけの一点集合です。

### 証明の概略

1. \(W=\{\{0\}\}\) なので、像は一点集合。

----

<a id="Tomabechi.Consistency.R1.c1SymbolAddressImage_isLUB"></a>

## 補題 `c1SymbolAddressImage_isLUB`

### 式

$$
\mathrm{emb}(\{0\})=\sup\mathrm{emb}(W)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスの像は、象徴の像の最小上界（LUB）です。

### 証明の概略

1. 象徴の像は一点集合（前の補題）。一点集合の上限はその点自身。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
