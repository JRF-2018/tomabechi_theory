# Theorem19_Counterexample.lean 解説

> 対象: [`Theorem19_Counterexample.lean`](../Theorem19_Counterexample.lean)（定理19の情報達成節に対する反例モデルの候補（P16））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Schauder–Tychonoff 不動点定理 | コンパクト凸集合上の連続な自己写像に固定点がある。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19（目標情報の容量）の**「情報達成」節**に対する、具体的な**反例モデルの候補**（プロジェクト内の識別名 P16）です。

定理19の情報達成の主張は、**決定論的で単射な方策**（ゴールを可逆に符号化して出力する方策）なら、方策の出力とゴールの条件付き相互情報量（CMI）が、ゴールのエントロピーに等しくなる、という形をしています。ところが、**出力の可測構造を自明な σ 代数にする**（出力が何も区別できない）と、方策が単射でも、**CMI は 0** になってしまいます。ゴールが二値の一様分布なら、ゴールのエントロピーは \(\log2>0\) なので、情報達成の等式 \(\text{score}=\text{goalEntropy}\) は**破れます**。

これを、定理16の区間逆系の固定点（主体）、全抽象度で同じ問題・方策を持つ定理19の容量系、と**同一のモデルに束ねて**示します。

- **主体（固定点）**：定理16の区間逆系 \([0,1]\)（全層で恒等射影、定数フィードバック \(1/2\)）の固定点 \((1/2,1/2,\dots)\)。座標 \(1/2\) は二値ゴールの一様事前分布を表します。
- **層ごとの容量系**：各抽象度（Bool 束）に、同じ許容問題・方策の対を 1 つ置く。各層の容量は 0（有限）。
- **反例**：自明 σ 代数の出力 `IndiscreteBit` を使う直接問題 `indiscreteBitDirectProblem` で、score = 0 < \(\log2\) = goalEntropy。

### 0.2 このファイルが証明していないこと

- **「任意の可測な出力」という読みの下での反例**です（ファイル冒頭のコメント）。**出力規約の適合性は、原文の記述が曖昧なため、別途監査の対象**とします。つまり、「原文の定理19が偽である」とは主張せず、「原文の出力の可測性についての読み方によっては、情報達成の等式が破れる」ことを示します。
- 反例は特殊なモデル（二値ゴール・Unit の入力・単点の問題）で、一般の反例分類ではありません。
- 物理層の「全問題でゴールのエントロピーが 0」という条件は、このモデルでは成立しません。ただし原文の条件文「その場合は容量 0」は、実際に容量が 0 なので満たされます。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # P16：定理19の情報達成節に対する反例モデルの候補
>
> 任意の可測な出力という読みの下で、二値ゴールを、自明 σ 代数の出力へ写す。定理16の固定点の証人と、全抽象度で同じ問題・方策を持つ定理19の容量系を束ねた、候補である。定理19の内部ゴール表象は、固定点の状態・そのコンパクトな表象・ゴールの事前確率が一致する形で、明示する。出力規約の適合性は、原文の記載が曖昧なため、別途、監査の対象とする。

### 0.4 節見出しのコメント（日本語訳）

> 元の Unit 逆系は、ゴール情報を保持できないため、ここでは各層の状態を `[0,1]` に広げる。固定点の座標 `1/2` は、Bool ゴールの一様事前分布を表し、ゴール型で添字づけた表象ベクトルを定義する。

> Bool 束の各層に、同じ 1 つの許容問題・方策の対を置く。恒等埋め込みは joint と CMI の評価を保存し、各層の容量は 0 なので有限である。物理層の「全問題で H=0」という条件は、このモデルでは成立しないが、原文の条件文「その場合は容量 0」は、容量が実際に 0 なので満たす。

名前空間は `Tomabechi.Theorem19_Counterexample`（`open MeasureTheory ProbabilityTheory Topology Tomabechi.Theorem16_25`）。

---

<a id="Tomabechi.Theorem19_Counterexample.SubjectLayer"></a>

## 定義 `SubjectLayer`

### 式

$$\mathrm{SubjectLayer}=\mathbb N$$

### Lean のコメント（日本語訳）

> 全層で同じ単点 TCZ を使う逆系。層は自然数で、上向き有向・最大元なし。

### 定義の説明

主体の逆系の層の添字は自然数です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectFixedPointExists"></a>

## 定義 `subjectFixedPointExists`

### 式

$$\exists x\in\varprojlim,\ \mathrm{feedback}(x)=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

単点（`Unit`）の逆系に固定点が存在する、という命題です（定理16の固定点の存在の形）。

### 証明の概略

1. 述語の定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectFixedPointExists_of_originalConditions"></a>

## 定理 `subjectFixedPointExists_of_originalConditions`

### 式

$$\text{subjectFixedPointExists}$$

### Lean のコメント（日本語訳）

> 定理16の原文の層条件を満たす単点逆系に、Fan–Glicksberg の固定点定理を適用する。自己写像は各層の恒等写像で、得られる主体は、その逆極限の固定点である。

### 補題の説明

単点の逆系は、コンパクト・凸・アフィンな射影など、定理16の条件をすべて満たすので、**Core の固定点存在定理**が適用できます。

### 証明の概略

1. キャリアが全体（`Set.univ`）でコンパクト・非空・凸であることを確認。
2. 射影が（`Unit` なので）アフィン・恒等・合成可能・連続であることを `Subsingleton.elim` で確認。
3. Core の固定点存在定理（Fan–Glicksberg）を適用。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalRepLayer"></a>

## 定義 `GoalRepLayer`

### 式

$$\mathbb N$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゴール表象の逆系の層の添字（自然数）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepTCZ"></a>

## 定義 `goalRepTCZ`

### 式

$$\mathrm{TCZ}_i=[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の TCZ を区間 \([0,1]\) にしたもの。ゴールの確率を載せるためです。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepProjection"></a>

## 定義 `goalRepProjection`

### 式

$$\pi_{\beta\alpha}=\mathrm{id}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層間の射影は恒等写像。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepFeedback"></a>

## 定義 `goalRepFeedback`

### 式

$$F_i(x)=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層のフィードバックは定数 \(1/2\)（二値ゴールの一様事前分布）。

### 証明の概略

1. 定義のみ（\(1/2\in[0,1]\)）。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepPoint"></a>

## 定義 `goalRepPoint`

### 式

$$p=(\tfrac12,\tfrac12,\dots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

全座標が \(1/2\) の点（固定点の候補）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepLayerSystem_has_fixedPoint_of_theorem16_conditions"></a>

## 定理 `goalRepLayerSystem_has_fixedPoint_of_theorem16_conditions`

### 式

$$\exists x\in\varprojlim,\ F(x)=x$$

### Lean のコメント（日本語訳）

> 区間 TCZ・恒等射影・定数フィードバックが、定理16の層条件を満たすため、既存の、原文条件付きの固定点定理を適用できる。

### 補題の説明

区間版の逆系（ゴール確率を保持できる）にも、定理16の固定点定理が適用できます。

### 証明の概略

1. コンパクト・凸・アフィンな射影・連続性を確認し、Core の固定点存在定理を適用。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepPoint_mem_inverseLimit"></a>

## 定理 `goalRepPoint_mem_inverseLimit`

### 式

$$p\in\varprojlim$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

点 \(p\) が逆極限に属する（射影が恒等なので各層で \(p_i=p_j\)）。

### 証明の概略

1. `affineInverseLimitSet` の定義を展開し、射影が恒等であることから。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubject"></a>

## 定義 `goalRepSubject`

### 式

$$\mathrm{subject}=p\in\varprojlim$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

主体として、点 \(p\) を逆極限の元（部分型）として取ったもの。

### 証明の概略

1. `goalRepPoint_mem_inverseLimit` で部分型の元にする。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubject_fixed"></a>

## 定理 `goalRepSubject_fixed`

### 式

$$F(\mathrm{subject})=\mathrm{subject}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

主体が固定点であること（フィードバックは定数 \(1/2\)、主体の座標も \(1/2\)）。

### 証明の概略

1. `Subtype.ext` と `funext` で各座標が \(1/2\) で一致。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalRepSubjectState"></a>

## 定義 `GoalRepSubjectState`

### 式

$$\mathrm{State}=\varprojlim$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

主体の状態空間：ゴール表象の逆極限。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalProbabilityRepresentation"></a>

## 定義 `GoalProbabilityRepresentation`

### 式

$$\mathrm{Rep}=[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ゴール確率の表象：区間 \([0,1]\) の点。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepLayerSelfMap"></a>

## 定義 `goalRepLayerSelfMap`

### 式

$$F_i=\text{定数 }1/2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の自己写像（`goalRepFeedback`）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepLayerSelfMap_commutes"></a>

## 定理 `goalRepLayerSelfMap_commutes`

### 式

$$\pi_{\beta\alpha}\circ F_\alpha=F_\beta\circ\pi_{\beta\alpha}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**射影との可換性**：層をまたいだ整合性です（どちらも定数 \(1/2\) なので成り立つ）。

### 証明の概略

1. 射影が恒等写像で、フィードバックが定数であることから、両辺とも \(1/2\)。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectSelfMap"></a>

## 定義 `goalRepSubjectSelfMap`

### 式

$$\text{主体状態の自己写像}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

逆極限全体の自己写像（各層のフィードバックから誘導）。

### 証明の概略

1. 定義：`inducedAffineInverseLimitMap`（各層のフィードバック `goalRepLayerSelfMap` から誘導される逆極限上の写像。層間の可換性 `goalRepLayerSelfMap_commutes` を添える）。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectSelfMap_continuous"></a>

## 定理 `goalRepSubjectSelfMap_continuous`

### 式

$$\text{連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自己写像の連続性。

### 証明の概略

1. `inducedAffineInverseLimitMap_continuous`（Core）を適用。各層の写像が定数写像なので連続（`continuous_const`）。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresent"></a>

## 定義 `goalRepSubjectRepresent`

### 式

$$\mathrm{represent}(s)=s_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

主体の状態から、ゴール確率の表象（第 0 座標）を取り出す写像。

### 証明の概略

1. 定義：`⟨s.1 0, s.2.1 0⟩`（第 0 座標が \([0,1]\) に入る）。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresent_continuous"></a>

## 定理 `goalRepSubjectRepresent_continuous`

### 式

$$\text{連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 0 座標を取る写像の連続性（積位相での射影）。

### 証明の概略

1. `continuous_apply` と部分型の連続性。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresentation"></a>

## 定義 `goalRepSubjectRepresentation`

### 式

$$\mathrm{SelfRepresentation}(\mathrm{State},\mathrm{Rep})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

**自己表象**の構造（Core の `SelfRepresentation`）：関係 \(s=\mathrm{represent}(r)\)（閉集合）、表象写像（連続）、表象が関係を満たすこと。

### 証明の概略

1. 関係の閉性は `isClosed_eq`、表象写像の連続性は上の補題、`represents` は `rfl`。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepRepresentationFeedback"></a>

## 定義 `goalRepRepresentationFeedback`

### 式

$$f(r)=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

表象空間でのフィードバック（定数 \(1/2\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepRepresentationFeedback_continuous"></a>

## 定理 `goalRepRepresentationFeedback_continuous`

### 式

$$\text{連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定数写像なので連続。

### 証明の概略

1. `continuous_const`。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresentation_equivariant"></a>

## 定理 `goalRepSubjectRepresentation_equivariant`

### 式

$$\mathrm{represent}(F(s))=f(\mathrm{represent}(s))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**同変性**：表象写像が、自己写像と表象フィードバックを交換すること。

### 証明の概略

1. 両辺とも \(1/2\)。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectSelfMap_fixedPoint_is_subject"></a>

## 定理 `goalRepSubjectSelfMap_fixedPoint_is_subject`

### 式

$$F(\mathrm{subject})=\mathrm{subject}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆極限全体の自己写像でも、主体が固定点であること。

### 証明の概略

1. `Subtype.ext` と `funext` で、各座標 \(i\) の値を比べる。
2. `goalRepSubjectSelfMap`・`inducedAffineInverseLimitMap`・`goalRepFeedback`（定数 \(1/2\)）・`goalRepSubject`・`goalRepPoint`（全座標 \(1/2\)）を展開して `simp`（4 行）。

----

<a id="Tomabechi.Theorem19_Counterexample.internalGoalProbabilityFromRepresentation"></a>

## 定義 `internalGoalProbabilityFromRepresentation`

### 式

$$p(g)=\begin{cases}r&(g=\text{true})\\1-r&(g=\text{false})\end{cases}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

表象 \(r\in[0,1]\) から、**内部のゴール確率**（`true` の確率 \(r\)、`false` の確率 \(1-r\)）を読み取る関数。

### 証明の概略

1. `if g then r.1 else 1 - r.1`。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubjectRepresentation_encodes_goalLaw"></a>

## 定理 `goalRepSubjectRepresentation_encodes_goalLaw`

### 式

$$p(g)=P(\text{goal}=g)\ \ (=\tfrac12)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

主体の表象が、二値ゴールの事前分布（一様）を正しく符号化していること。

### 証明の概略

1. `g` で場合分けし、\(1/2\) と一様測度の原子の値を比べる。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectGoalSelfRepresentationPremises"></a>

## 定義 `subjectGoalSelfRepresentationPremises`

### 式

$$\text{自己表象の存在}\wedge\text{連続性}\wedge\text{固定点}\wedge\text{同変性}\wedge\text{ゴール分布の符号化}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

主体の自己表象についての、前提の束です。

### 証明の概略

1. 命題の定義のみ（上の補題の連言）。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectGoalSelfRepresentationPremises_holds"></a>

## 定理 `subjectGoalSelfRepresentationPremises_holds`

### 式

$$\text{subjectGoalSelfRepresentationPremises}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上の前提がすべて成り立つこと。

### 証明の概略

1. 各成分を、上の補題で与える。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectGoalProbabilityRep"></a>

## 定義 `subjectGoalProbabilityRep`

### 式

$$p(g)=x_0\ (g=\text{true}),\ \ 1-x_0\ (g=\text{false})$$

### Lean のコメント（日本語訳）

> 定理19のゴール carrier で添字づけた、主体の内部ゴール確率の表象。

### 定義の説明

逆極限の元 \(x\) から、ゴール確率をベクトルとして読み出します。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubject_represents_binaryGoalLaw"></a>

## 定理 `goalRepSubject_represents_binaryGoalLaw`

### 式

$$p(g)=P_{\text{goal}}(\{g\})$$

### Lean のコメント（日本語訳）

> 固定点の主体の自己表象は、二値ゴールの事前分布の、各原子の確率を保持する。これは、固定点が 1 点の Unit 表象では表せなかったデータを、同じ主体の carrier へ接続する。

### 補題の説明

主体の内部確率が、二値ゴールの事前分布（\(1/2,1/2\)）に一致します。

### 証明の概略

1. `g` の場合分けと、一様測度の原子の値の計算。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubject_matches_law_goalKernel"></a>

## 定理 `goalRepSubject_matches_law_goalKernel`

### 式

$$p(g)=P(\text{goal}=g\mid\text{input})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

内部確率が、CMI の法則（`binaryContextLaw`）のゴールの条件付き分布（入力に関する）にも一致すること。

### 証明の概略

1. 入力が `Unit` なので条件付き分布は事前分布に一致。

----

<a id="Tomabechi.Theorem19_Counterexample.goalStateCode"></a>

## 定義 `goalStateCode`

### 式

$$\mathrm{code}(g)=\begin{cases}1&(g)\\0&(\neg g)\end{cases}$$

### Lean のコメント（日本語訳）

> 二値ゴールの双方は、全層 TCZ の主体の状態空間で、異なる表象の点を持つ。

### 定義の説明

ゴール値 \(g\) を、状態空間の点（0 または 1）に符号化します。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.goalStateCode_mem_subjectTCZ"></a>

## 定理 `goalStateCode_mem_subjectTCZ`

### 式

$$\mathrm{code}(g)\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

符号が TCZ（\([0,1]\)）に入ること。

### 証明の概略

1. \(0,1\in[0,1]\)。

----

<a id="Tomabechi.Theorem19_Counterexample.goalStateCode_injective"></a>

## 定理 `goalStateCode_injective`

### 式

$$\mathrm{code}\ \text{は単射}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

異なるゴール値は異なる点に符号化される。

### 証明の概略

1. \(0\ne1\)。

----

<a id="Tomabechi.Theorem19_Counterexample.goalRepSubject_internalGoalRepresentation"></a>

## 定理 `goalRepSubject_internalGoalRepresentation`

### 式

$$\mathrm{code}\ \text{単射}\wedge\mathrm{code}(g)\in\mathrm{TCZ}\wedge p(g)=P(\{g\})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

符号の単射性・TCZ への所属・内部確率の一致を、まとめたもの。

### 証明の概略

1. 上の 3 つの補題を並べる。

----

<a id="Tomabechi.Theorem19_Counterexample.subjectGoalModelPremises"></a>

## 定義 `subjectGoalModelPremises`

### 式

$$\text{固定点の存在}\wedge\text{主体が固定点}\wedge\text{内部確率の一致（2 通り）}\wedge\text{符号化}\wedge\text{自己表象の前提}$$

### Lean のコメント（日本語訳）

> 定理19に渡す主体：定理16の区間層系から固定点が存在し、選んだ同じ固定点のゴール確率表象が、二値 CMI の法則の事前分布と一致する。

### 定義の説明

定理19に渡す「主体」の前提の束（定理16の固定点と、定理19のゴール法則の接続）。

### 証明の概略

1. 命題の定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.AbstractLayer"></a>

## 定義 `AbstractLayer`

### 式

$$\mathrm{AbstractLayer}=\text{Bool}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象度の束を Bool（2 点の束）にする。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalProblem"></a>

## 定義 `GoalProblem`

### 式

$$\mathrm{GoalProblem}=\text{Unit}$$

### Lean のコメント（日本語訳）

> 許容対 `(d,π)` を、依存 Σ 型で保持する。候補では、問題の記述子と、その問題の許容方策が、それぞれ単点だが、CMI の法則は、この対が指す、同じ固定の対象に割り当てる。

### 定義の説明

問題の型は単点（`Unit`）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalPolicy"></a>

## 定義 `GoalPolicy`

### 式

$$\mathrm{GoalPolicy}(d)=\text{Unit}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各問題の許容方策の型も単点。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.GoalProblemPolicyPair"></a>

## 定義 `GoalProblemPolicyPair`

### 式

$$\Sigma d,\ \mathrm{GoalPolicy}(d)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

問題・方策の**対**を依存 Σ 型で表す。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.layerProblem"></a>

## 定義 `layerProblem`

### 式

$$\text{各層の直接問題（二値 CMI 法則）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層・各対に対する直接ゴール CMI 問題（常に同じ二値の法則）。

### 証明の概略

1. 定義：各層・各対に対して、`Theorem19_Heterogeneous.indiscreteBitDirectProblem`（入力 `Unit`・ゴール `Bool`・出力 `IndiscreteBit` の直接ゴール CMI 問題）を返す（引数は無視）。

----

<a id="Tomabechi.Theorem19_Counterexample.layerPolicy"></a>

## 定義 `layerPolicy`

### 式

$$\pi(z)=\mathrm{encode}(z_2)\in\mathrm{IndiscreteBit}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の方策：ゴール \(z_2\)（Bool）を、自明 σ 代数の出力型 `IndiscreteBit` へ符号化する（単射）。

### 証明の概略

1. 定義：`encode z.2`。

----

<a id="Tomabechi.Theorem19_Counterexample.layerPolicy_measurable"></a>

## 定理 `layerPolicy_measurable`

### 式

$$\pi\ \text{は可測}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策の可測性（`IndiscreteBit` は自明 σ 代数だが、定数でない写像も可測になるよう設計されている）。

### 証明の概略

1. `DecoderRegularityWitness.encode_measurable`（符号化 `encode` の可測性）と第 2 射影 `measurable_snd` の合成。

----

<a id="Tomabechi.Theorem19_Counterexample.layerProblem_joint_eq_binaryContextLaw"></a>

## 定理 `layerProblem_joint_eq_binaryContextLaw`

### 式

$$\text{joint}=\text{binaryContextLaw.joint}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各層の問題の同時法則が、二値 CMI 法則の同時法則に一致すること。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem19_Counterexample.layerProblem_joint_generated_by_layerPolicy"></a>

## 定理 `layerProblem_joint_generated_by_layerPolicy`

### 式

$$\text{joint}=(\mu_{\rm in}\otimes\kappa_{\rm goal}).\mathrm{map}(z\mapsto(z_1,z_2,\pi(z)))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同時法則が、**方策 \(\pi\) から生成される**こと（入力・ゴール・方策出力の三つ組の像測度）。

### 証明の概略

1. `layerProblem_joint_eq_binaryContextLaw` と、`binaryContextLaw` が `encode` で生成されること（DecoderRegularity の補題）。

----

<a id="Tomabechi.Theorem19_Counterexample.layerAdmissible"></a>

## 定義 `layerAdmissible`

### 式

$$\text{全体}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層の許容な問題・方策の対の集合は全体。

### 証明の概略

1. `Set.univ`。

----

<a id="Tomabechi.Theorem19_Counterexample.layerScore"></a>

## 定義 `layerScore`

### 式

$$\text{score}(a,q)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各層・各対のスコア（情報量）。

### 証明の概略

1. 定義：各層・各対の直接問題のスコア `(layerProblem a q).score`（KL 型 CMI を実数に直した値）。

----

<a id="Tomabechi.Theorem19_Counterexample.layerScore_eq_zero"></a>

## 定理 `layerScore_eq_zero`

### 式

$$\mathrm{score}=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

スコアが 0 であること（自明 σ 代数の出力は何も区別できないので CMI が 0）。

### 証明の概略

1. `layerProblem` と `DirectGoalCMIProblem.score` を展開し、`indiscreteBitDirectProblem_information_eq_zero`（Heterogeneous：自明 σ 代数の出力の情報量は 0）を代入する。

----

<a id="Tomabechi.Theorem19_Counterexample.layerProblemPool_nonempty"></a>

## 定理 `layerProblemPool_nonempty`

### 式

$$\mathrm{admissible}(a)\ne\emptyset$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容集合が非空（`((),())` を取る）。

### 証明の概略

1. `⟨⟨(),()⟩, Set.mem_univ _⟩`。

----

<a id="Tomabechi.Theorem19_Counterexample.layerScores_bounded"></a>

## 定理 `layerScores_bounded`

### 式

$$\mathrm{BddAbove}(\mathrm{score}''\mathrm{admissible})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

スコアの集合が上に有界（全部 0）。

### 証明の概略

1. スコアが 0 なので 0 が上界。

----

<a id="Tomabechi.Theorem19_Counterexample.layerCapacity_eq_zero"></a>

## 定理 `layerCapacity_eq_zero`

### 式

$$C_a=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各層の容量（スコアの上限）が 0 であること。

### 証明の概略

1. 上限が 0 以下：許容集合は非空（`layerProblemPool_nonempty`）で、各スコアは 0（`layerScore_eq_zero`）なので `csSup_le`。
2. 上限が 0 以上：元 \(\langle(),()\rangle\) のスコアが集合に入り、集合は上に有界（`layerScores_bounded`）なので `le_csSup`、スコアは 0（9 行）。

----

<a id="Tomabechi.Theorem19_Counterexample.P16_candidate_layer_data_and_failure"></a>

## 定理 `P16_candidate_layer_data_and_failure`

### 式

$$\text{主体の前提}\wedge\text{容量データ}\wedge\text{埋め込みの整合}\wedge\text{物理層の条件文}\wedge\text{score}<\text{goalEntropy}$$

### Lean のコメント（日本語訳）

> 全抽象度における容量データと反例の候補を、同一の構成で束ねる。主体は、定理16の区間層の固定点で、二値ゴールの法則を表象する。各層は、明示的な依存 Σ 型の `(d,π)` の singleton を持ち、問題・方策から同じ法則を生成し、層間の恒等写像が評価を保存する。

### 補題の説明

**同一のモデルで**、(i) 主体は定理16の固定点、(ii) 各層の容量データ（非空・有界・容量 0）、(iii) 層間の埋め込みが評価を保存、(iv) 物理層の条件文、(v) 反例（score < goalEntropy）が成り立つ、という束です。

### 証明の概略

1. `subjectGoalModelPremises` を `…_holds` から。
2. 容量データ：`layerProblemPool_nonempty`・`layerScores_bounded`・`layerCapacity_eq_zero`。
3. 埋め込みは恒等写像（評価・joint を保存）。
4. 物理層の条件文：容量が 0 なので成立。
5. 反例：`indiscreteBitDirectProblem_score_lt_goalEntropy`（Heterogeneous）。

----

<a id="Tomabechi.Theorem19_Counterexample.P16_candidate_package_spec"></a>

## 定義 `P16_candidate_package_spec`

### 式

$$\text{候補 package の仕様（連言）}$$

### Lean のコメント（日本語訳）

> C4 の候補 package。定理16の区間層系の固定点、同じ固定点の二値ゴール確率表象、全層の容量データ、失敗する直接問題と、可測な単射方策・生成 joint を束ねる。

### 定義の説明

反例の候補を 1 つの命題にまとめた**仕様**です：上の束に、`encode` の可測性・単射性、方策による joint の生成、`information = 0`、`goalEntropy = log 2`、`information ≠ ⊤`、各層の goalEntropy が正、を加えます。

### 証明の概略

1. 命題の定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.P16_candidate_package_with_goalProbabilityRepresentation"></a>

## 定理 `P16_candidate_package_with_goalProbabilityRepresentation`

### 式

$$\text{P16\_candidate\_package\_spec}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

仕様が実際に成り立つこと。

### 証明の概略

1. `P16_candidate_layer_data_and_failure` と、DecoderRegularity・Heterogeneous の補題（`encode_measurable`・`encode_injective`・`binaryContextLaw_generated_by_encode`・`indiscreteBitDirectProblem_information_eq_zero`・`…_goalEntropy_eq_log_two`）を並べる。

----

<a id="Tomabechi.Theorem19_Counterexample.P16ConcreteModel"></a>

## 構造体 `P16ConcreteModel`

### 式

$$(\text{subject},\text{directProblem},\text{policy},\text{problemFamily},\text{policyFamily},\text{evidence})$$

### Lean のコメント（日本語訳）

> P16 の具体的なモデルデータ。主体、直接の法則、決定論的な方策、および、各抽象層の問題・方策の族を、1 つの対象に保持する。

### 定義の説明

反例のモデルを 1 つの構造体にまとめたものです。

### 証明の概略

1. 構造体なので証明はなし。

----

<a id="Tomabechi.Theorem19_Counterexample.p16ConcreteModel"></a>

## 定義 `p16ConcreteModel`

### 式

$$\text{具体的な反例モデル}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`P16ConcreteModel` の具体的なインスタンス（主体 = `goalRepSubject`、直接問題 = `indiscreteBitDirectProblem`、方策 = `encode`、層の族 = `layerProblem`/`layerPolicy`）。

### 証明の概略

1. 各フィールドを具体的に与え、`packageEvidence` に `P16_candidate_package_with_goalProbabilityRepresentation` を渡す。

----

<a id="Tomabechi.Theorem19_Counterexample.P16ConcreteModel.OriginalPremises"></a>

## 定義 `P16ConcreteModel.OriginalPremises`

### 式

$$M=p16ConcreteModel\text{ の各フィールドが期待どおり}\wedge\text{spec}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

原文の明示的な抽象前提（モデルの各フィールドが、上の具体的なものであること、仕様が成り立つこと）。

### 証明の概略

1. 命題の定義のみ。

----

<a id="Tomabechi.Theorem19_Counterexample.P16_exists_concrete_counterexample_under_measurable_output_reading"></a>

## 定理 `P16_exists_concrete_counterexample_under_measurable_output_reading`

### 式

$$\exists M,\ M.\mathrm{OriginalPremises}\ \wedge\ \mathrm{score}\ne\mathrm{goalEntropy}$$

### Lean のコメント（日本語訳）

> C4 の存在の形：1 つの主体/法則/方策/層の族を持つ、同一のモデルで、原文の明示的な抽象前提を満たし、決定論的で単射な方策による情報達成の等式を否定する。

### 補題の説明

**反例の存在定理**：「出力は任意の可測写像でよい」という読みの下では、定理19の情報達成の等式（score = goalEntropy）は、決定論的な単射方策でも成り立たない。\(M=\)`p16ConcreteModel` が証人です。

### 証明の概略

1. `M := p16ConcreteModel` として、前提は `⟨rfl, rfl, rfl, rfl, rfl, 仕様⟩`。
2. `indiscreteBitDirectProblem_score_lt_goalEntropy`（Heterogeneous）から score < goalEntropy、よって score ≠ goalEntropy。

----


## コメント修正記録

（なし）
