# Tomabechi/Information/Capacity.lean 解説

> 対象: [`Tomabechi/Information/Capacity.lean`](../Tomabechi/Information/Capacity.lean)（定理22の情報容量・KL スコア・条件付き相互情報量の測度データ）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22の**情報容量の単調性**（結論 (22.6)：段階が上がると、許容される問題・方策の情報量の上限（容量）は減らない）の、**抽象的な形**と、**測度論的な条件付き相互情報量（CMI）**への具体化を扱うファイルです。LUB の段階列や ODE を参照しない、純粋に情報理論の API として分離されています。

### 0.2 構成

| 節 | 宣言 | 内容 |
| --- | --- | --- |
| 抽象容量 | `layerCapacity`, `capacity_nondecreasing_of_embedding_condition`, `…_of_injective_law_preserving_embedding` | スコアの上限としての容量と、埋め込みがスコアを保つときの単調性 |
| 有限 KL スコア | `FiniteKLDivergenceLaw`, `finiteKLDivergenceScore`, `capacity_nondecreasing_of_finite_kl_preserving_embedding` | 有限な KL ダイバージェンスをスコアにした場合 |
| CMI の測度データ | `ConditionalMutualInformationLaw` とその補題 | 同時法則と 2 つの条件付き周辺核。条件付き独立の参照測度の構成 |
| CMI での容量 | `FiniteConditionalMutualInformationLaw`, `toFiniteKLLaw`, `capacity_nondecreasing_of_*_embedding` | CMI のスコアでの単調性 |

### 0.3 容量とは

各段階（層）\(a\) に、許容される「問題・方策の組」の集合 `admissible a` があり、それぞれにスコア（定理19では条件付き相互情報量）があるとします。**層の容量**は、許容される組のスコアの**上限**（`sSup`）です。

### 0.4 このファイルが証明していないこと

- 容量の単調性は、**埋め込みがスコアを保つ**という仮定（定理19の埋め込み条件）から導きます。この仮定自体を、論文のモデルで確かめる作業はここにはありません。
- 条件付き相互情報量の測度論的な定義（KL ダイバージェンス）は、**条件付き核が与えられている**として構成します。同時法則から条件付き核を作る（正則条件付き確率の存在）ことは別の課題で、ここでは仮定していません（核は明示的なデータです）。
- スコアの有界性（`BddAbove`）は仮定です。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **情報容量と一般測度 CMI の共有核**
>
> 定理22の抽象的な容量・KL スコア・条件付き相互情報量の法則と、その層間の保存補題。LUB の段階列や段階 ODE を参照しない情報理論の API を、既存の名前空間と宣言名のまま分離する。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem22`。`open Filter`、`open scoped Topology ProbabilityTheory`。

---

<a id="Tomabechi.Theorem22.layerCapacity"></a>

## 定義 `layerCapacity`

### 式

$$\mathrm{cap}(a)=\sup\{\,\text{score}(x)\mid x\in\text{admissible}(a)\,\}$$

### Lean のコメント（日本語訳）

> 1 つの LUB の層での、許容される目標・方策の族の、抽象的な容量。スコアは、定理19で使う条件付き相互情報量で具体化できる。
> 日本語の要約：LUB の段階ごとに許容される問題・方策のスコアの上限を、容量として定義する。

### 定義の説明

層 \(a\) の容量は、その層で許容されるすべての（問題・方策）のスコアの上限です。

### 証明の概略

1. 定義：`sSup (score '' admissible a)`。

----

<a id="Tomabechi.Theorem22.capacity_nondecreasing_of_embedding_condition"></a>

## 補題 `capacity_nondecreasing_of_embedding_condition`

### 式

$$a\le b,\ \ \forall x\in\text{adm}(a),\ \exists y\in\text{adm}(b),\ \text{score}(y)=\text{score}(x)\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 容量の結論 (22.6)。より高い層への埋め込みは、低い層の許容される問題・方策の組のスコアを保たなければならない。空でないことと有界性が、上限を有限にする。スコアを条件付き相互情報量にとれば、論文の分布を保つ埋め込みの条件になる。この API は、定理19の埋め込みの、スコア保存という帰結だけを切り出したもので、容量の単調性そのものを仮定するものではない。補題 `capacity_nondecreasing_of_injective_law_preserving_embedding` は、単射かつ同時法則を保つという完全な仮定を保持し、スコアがその法則を経由するとき、このスコアレベルの条件を導く。
> 日本語の要約：低い層の許容項目を高い層へ移す、スコア保存の条件から、上限で定義した容量の単調性を示す。

### 補題の説明

「上の層は下の層の全スコアを実現できる」なら、上の層の容量（上限）は下の層以上です（上限の基本性質）。

### 証明の概略

1. 下の層のスコア集合 \(I_a\)、上の層のスコア集合 \(I_b\) は非空・上に有界で、`sSup` が最小上界（`IsLUB`）。
2. \(I_a\) の各元 \(s=\text{score}(x)\) について、仮定から \(\text{score}(y)=s\) となる \(y\in\text{adm}(b)\) があるので \(s\le\sup I_b\)。
3. よって \(\sup I_a\le\sup I_b\)（18 行）。

----

<a id="Tomabechi.Theorem22.capacity_nondecreasing_of_injective_law_preserving_embedding"></a>

## 補題 `capacity_nondecreasing_of_injective_law_preserving_embedding`

### 式

$$\text{単射}\ \wedge\ \text{同時法則を保存}\ \wedge\ \text{score}=\text{scoreOfLaw}\circ\text{law}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> (22.6) の完全な埋め込みの形：高い層への単射が、許容される問題・方策の組のそれぞれの同時法則を保ち、スコアはその法則の関数である。先に述べたスコアの実現可能性の補題は、小さな順序論的な核であり、この版は、定理19の単射性と分布保存の条件を明示的に保持する。
> 日本語の要約：単射かつ同時分布を保存する層間の写像と、スコアの分布への依存性から (22.6) を証明する。

### 補題の説明

埋め込みが単射で、各組の同時法則を保てば、スコア（法則の関数）も保たれます。あとは上の補題を適用します。

### 証明の概略

1. 埋め込み \(x\mapsto\text{embedding}(x)\) は \(\text{adm}(b)\) に入り、法則を保つので、\(\text{score}(\text{embedding}\,x)=\text{scoreOfLaw}(\text{law}(\text{embedding}\,x))=\text{scoreOfLaw}(\text{law}(x))=\text{score}(x)\)。
2. `capacity_nondecreasing_of_embedding_condition` を適用（12 行）。

----

<a id="Tomabechi.Theorem22.FiniteKLDivergenceLaw"></a>

## 構造体 `FiniteKLDivergenceLaw`

### 式

$$\text{joint},\ \text{reference}:\ \text{測度},\qquad \mathrm{KL}(\text{joint}\,\Vert\,\text{reference})\ne\infty$$

### Lean のコメント（日本語訳）

> 有限の測度の KL のスコアと、その有限性の証明書。条件付き相互情報量については、`joint` は同時法則で、`reference` は条件付き独立の参照法則 \(P_X\otimes P_{G|X}\otimes P_{Y|X}\) でなければならない。この構造体自体は、任意の測度がこの解釈をもつ、とは意図的に主張しない。
> 日本語の要約：有限な測度の KL ダイバージェンスをスコアにするデータ。条件付き相互情報量として使う場合の参照法則の意味は、使う側が与える。

### 定義の説明

2 つの測度（同時法則と参照測度）の組と、その KL ダイバージェンスが無限大でないという証明書の束です。KL ダイバージェンスの値をスコアにします。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.finiteKLDivergenceScore"></a>

## 定義 `finiteKLDivergenceScore`

### 式

$$\mathrm{score}=\bigl(\mathrm{KL}(\text{joint}\,\Vert\,\text{reference})\bigr).\mathrm{toReal}$$

### Lean のコメント（日本語訳）

> 測度の組の、実数値の KL スコア。

### 定義の説明

KL ダイバージェンスは \([0,\infty]\) の値をとるので、有限性の証明書のもとで実数に直したものです。

### 証明の概略

1. 定義：`(InformationTheory.klDiv law.joint law.reference).toReal`。

----

<a id="Tomabechi.Theorem22.capacity_nondecreasing_of_finite_kl_preserving_embedding"></a>

## 補題 `capacity_nondecreasing_of_finite_kl_preserving_embedding`

### 式

$$\text{埋め込みが KL の組を保存}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 容量の単調性の定理を、一般の可測空間の KL スコアに特殊化したもの。埋め込みは、KL の組の両方の測度を保つ（したがって元の同時法則と、指定された参照法則も保つ）。`FiniteKLDivergenceLaw` の条件付き独立の参照測度を使えば、これは (22.6) の測度論的な条件付き相互情報量の例である。条件付き核からその参照測度を構成し、その保存を証明することは、別の課題として残る。
> 日本語の要約：一般の可測空間の有限 KL スコアについて、単射かつ KL の法則の組を保つ埋め込みから、容量の単調性を示す。条件付き独立の参照測度の構成は別の課題。

### 補題の説明

抽象版（`capacity_nondecreasing_of_injective_law_preserving_embedding`）で、法則を `FiniteKLDivergenceLaw`、スコアを KL スコアとした場合です。

### 証明の概略

1. 抽象版を、`jointLaw := law`、`scoreOfLaw := finiteKLDivergenceScore` で適用（6 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw"></a>

## 構造体 `ConditionalMutualInformationLaw`

### 式

$$\text{input }P_X,\ \ P_{G\mid X},P_{Y\mid X}\ (\text{Markov 核}),\ \ \text{joint on }X\times(G\times Y),\ \ \text{周辺の整合}$$

### Lean のコメント（日本語訳）

> \(X\times(G\times Y)\) 上の同時法則と、その条件付きの周辺 \(G\mid X\)、\(Y\mid X\) を与える核。整合性のフィールドは、2 つの対の周辺が、入力の法則と、対応する核の合成であることを述べる。これは、\(I(G;Y\mid X)\) の KL による定義で使う、条件付き独立の参照測度を構成するのに必要なデータである。
> 日本語の要約：同時法則と 2 つの条件付き周辺の核をもち、周辺の法則との整合性を明示する、条件付き相互情報量の測度のデータ。

### 定義の説明

CMI を測度論で定義するための材料です。入力 \(X\) の確率測度 `input`、目標の条件付き分布（Markov 核）`goalGivenInput`、行動の条件付き分布 `actionGivenInput`、同時法則 `joint`、そして「同時法則の \((X,G)\) 周辺は `input ⊗ goalGivenInput`、\((X,Y)\) 周辺は `input ⊗ actionGivenInput`」という整合条件（`jointGoalMarginal`, `jointActionMarginal`）が束ねられています。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.joint_isProbabilityMeasure"></a>

## 補題 `ConditionalMutualInformationLaw.joint_isProbabilityMeasure`

### 式

$$\text{joint は確率測度}$$

### Lean のコメント（日本語訳）

> 同時法則自体が確率測度である：その \((X,G)\) の周辺は、入力の確率の法則と Markov 核の合成なので確率測度である。したがって、整合性のフィールドが、無限の質量をもつ任意の測度を、同時分布と呼ぶことを排除する。
> 日本語の要約：入力の確率測度と確率核の合成が確率測度であり、それが同時法則の周辺であることから、同時法則自体も確率測度とわかる。

### 補題の説明

周辺が確率測度なら、全体の質量も 1 です（全質量は周辺で保たれる）。

### 証明の概略

1. \((X,G)\) 周辺は `input ⊗ goalGivenInput`（確率測度と Markov 核の合成）で確率測度。
2. `isProbabilityMeasure_of_map`（像測度が確率測度で、写像が可測なら元も）を適用（12 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure"></a>

## 定義 `ConditionalMutualInformationLaw.referenceMeasure`

### 式

$$P_X(dx)\,P_{G\mid X}(dg\mid x)\,P_{Y\mid X}(dy\mid x)$$

### Lean のコメント（日本語訳）

> 条件付き独立の参照測度 \(P_X(dx)P_{G|X}(dg|x)P_{Y|X}(dy|x)\)。\(X\) の対角コピーに沿って、2 つの条件付き核の並列の積をとることで構成する。
> 日本語の要約：条件付き相互情報量の KL の参照測度を、\(X\) を共有する条件付き核の独立な積として構成する。

### 定義の説明

\(G\) と \(Y\) が \(X\) のもとで**条件付き独立**だったときの同時分布です。CMI は、実際の同時法則とこの参照測度の KL ダイバージェンスとして定義されます。

### 証明の概略

1. 入力 \(P_X\) を対角（\(x\mapsto(x,x)\)）で複製し、2 つの核の積核（`×ₖ`）を合成する（9 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_fst"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_fst`

### 式

$$\text{referenceMeasure}.\mathrm{fst}=P_X$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

参照測度の \(X\) の周辺は入力の法則です。

### 証明の概略

1. 合成の第 1 成分の周辺が入力になることを、`Measure.fst` と核の合成の性質で示す（8 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_isProbabilityMeasure"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_isProbabilityMeasure`

### 式

$$\text{referenceMeasure は確率測度}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Markov 核の積と合成は確率測度を保ちます。

### 証明の概略

1. `isProbabilityMeasure_iff`（全質量が 1）に直し、積核・合成の質量を計算する（13 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_goalMarginal"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_goalMarginal`

### 式

$$\text{referenceMeasure の }(X,G)\text{ 周辺}=P_X\otimes P_{G\mid X}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

参照測度の \((X,G)\) 周辺は、実際の同時法則の同じ周辺と一致します（`jointGoalMarginal` と同じ形）。KL の参照として自然であることの確認です。

### 証明の概略

1. 積核の第 1 成分の周辺が `goalGivenInput` に等しいこと（`Kernel.fst_eq`、Markov 核）。
2. 合成の周辺を計算して等式を得る（25 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_actionMarginal"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_actionMarginal`

### 式

$$\text{referenceMeasure の }(X,Y)\text{ 周辺}=P_X\otimes P_{Y\mid X}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上の補題の行動 \(Y\) 版です。

### 証明の概略

1. 積核の第 2 成分の周辺が `actionGivenInput` に等しいこと（`Kernel.snd_eq`）から（25 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_eq_of_kernels_ae_eq"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_eq_of_kernels_ae_eq`

### 式

$$P_X\ \text{同じ},\ \text{核が}\ P_X\text{-a.e. 等しい}\ \Longrightarrow\ \text{参照測度が等しい}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

条件付き核は、ほとんど至るところ等しければ参照測度も等しくなります（核は測度ゼロの集合で変えても結果が同じ）。

### 証明の概略

1. 積核もほとんど至るところ等しい（`filter_upwards`）。
2. 合成は a.e. 等しい核で変わらない（`Measure.compProd` の a.e. 等しい核に対する不変性、21 行）。

----

<a id="Tomabechi.Theorem22.ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq"></a>

## 補題 `ConditionalMutualInformationLaw.referenceMeasure_eq_of_joint_eq`

### 式

$$\text{同時法則が等しい}\ \Longrightarrow\ \text{参照測度が等しい}\quad(\text{可算生成の下で})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同時法則が等しければ、条件付き核は（可算生成性のもとで）ほとんど至るところ一意なので、参照測度も等しくなります。次の容量の補題で、「同時法則の保存」だけから「参照測度の保存」を出すのに使います。

### 証明の概略

1. 同時法則の \((X,G)\)・\((X,Y)\) 周辺が等しいので、`input ⊗ goalGivenInput`、`input ⊗ actionGivenInput` が等しい。
2. 入力が等しく（`Measure.fst`）、可算生成性の下で条件付き核が a.e. 一意（`Measure.compProd_eq_iff` 型の補題）。
3. `referenceMeasure_eq_of_kernels_ae_eq` を適用（37 行）。

----

<a id="Tomabechi.Theorem22.FiniteConditionalMutualInformationLaw"></a>

## 構造体 `FiniteConditionalMutualInformationLaw`

### 式

$$I(G;Y\mid X)=\mathrm{KL}\bigl(P_{XGY}\,\Vert\,P_X\otimes P_{G\mid X}\otimes P_{Y\mid X}\bigr)<\infty$$

### Lean のコメント（日本語訳）

> 条件付き相互情報量の測度論的な定義 \(\mathrm{klDiv}(P_{XGY},P_X\otimes P_{G|X}\otimes P_{Y|X})\)。ただし、その KL ダイバージェンスが有限のとき。条件付き核と、それらが同時法則と一致することは、明示的なデータであり、したがって、正則条件付き確率の存在定理は、ここで暗黙に仮定されていない。
> 日本語の要約：条件付き核から構成した参照法則に対する有限の KL ダイバージェンスとして、条件付き相互情報量を表す。

### 定義の説明

`ConditionalMutualInformationLaw`（核と同時法則）に、「同時法則と参照測度の KL ダイバージェンスが有限」という証明書を足した構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem22.FiniteConditionalMutualInformationLaw.toFiniteKLLaw"></a>

## 定義 `FiniteConditionalMutualInformationLaw.toFiniteKLLaw`

### 式

$$\text{CMI のデータ}\ \mapsto\ (\text{joint},\ \text{referenceMeasure},\ \text{finite})$$

### Lean のコメント（日本語訳）

> 条件付き確率としての解釈を忘れて、一般の容量の定理が使う、同時の測度・参照測度の組と有限な KL の証明書を保つ。
> 日本語の要約：条件付き相互情報量のデータを、一般の有限 KL 容量の API の測度の組に変換する。

### 定義の説明

CMI のデータを、KL ダイバージェンスのスコア用の一般の形（`FiniteKLDivergenceLaw`）に変換します。

### 証明の概略

1. 定義：`joint := distribution.joint`、`reference := distribution.referenceMeasure`、`finite := finite`（9 行）。

----

<a id="Tomabechi.Theorem22.capacity_nondecreasing_of_conditional_mutual_information_embedding"></a>

## 補題 `capacity_nondecreasing_of_conditional_mutual_information_embedding`

### 式

$$\text{埋め込みが CMI の KL の組を保存}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)$$

### Lean のコメント（日本語訳）

> 定理19/22の容量の単調性を、可測空間上の条件付き相互情報量の KL による定義に特殊化する。各層の埋め込みは、誘導される同時法則と、その条件付き独立の参照測度を保つ（結果の有限 KL の法則の等式としてまとめる）。層をまたいで、共通の可測な文字集合を使う。姉妹の定理 `capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding` は、入出力の対の空間が可算生成のとき、同時法則の保存から参照測度の保存を導く。与えられた同時法則から核を構成することは、別の正則性/分解の問題として残る。
> 日本語の要約：条件付き独立の参照測度をもつ一般の測度の CMI について、KL の法則の組を保つ単射の埋め込みから、容量の単調性を示す。

### 補題の説明

`capacity_nondecreasing_of_finite_kl_preserving_embedding` を CMI のデータ（`toFiniteKLLaw`）に適用したものです。

### 証明の概略

1. `toFiniteKLLaw` の保存の仮定から、一般の有限 KL 版に渡す（5 行）。

----

<a id="Tomabechi.Theorem22.capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding"></a>

## 補題 `capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding`

### 式

$$\text{同時法則の保存だけ}\ \Longrightarrow\ \mathrm{cap}(a)\le\mathrm{cap}(b)\quad(\text{可算生成の下で})$$

### Lean のコメント（日本語訳）

> 層が完全な同時法則を保つなら、可算生成な入出力の空間で、条件付き核はほとんど至るところ一意なので、誘導される条件付き独立の参照法則と、CMI のスコアも保たれる。これは、(22.6) の参照法則の部分を、独立した埋め込みの仮定として要求するのでなく、導く。
> 日本語の要約：可算生成性のもとで、条件付き核のほとんど至るところの一意性を使い、同時法則の保存だけから、条件付き独立の参照法則の保存を導く。

### 補題の説明

上の補題の、仮定を弱めた版です：埋め込みが**同時法則だけ**を保存するなら十分です（参照測度の保存は `referenceMeasure_eq_of_joint_eq` で導きます）。

### 証明の概略

1. 同時法則の保存から参照測度の保存（`referenceMeasure_eq_of_joint_eq`）。
2. KL の組（`toFiniteKLLaw`）の保存を得て、直前の補題を適用（18 行）。

----


## コメント修正記録

- `capacity_nondecreasing_of_injective_law_preserving_embedding` の docstring の最終行が重複していた（"distribution-preservation condition explicitly." が 2 回）。重複を 1 つに修正した（コメントのみ）。
