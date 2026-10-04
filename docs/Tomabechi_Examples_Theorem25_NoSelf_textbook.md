# Tomabechi/Examples/Theorem25_NoSelf.lean 解説

> 対象: [`Tomabechi/Examples/Theorem25_NoSelf.lean`](../Tomabechi/Examples/Theorem25_NoSelf.lean)（定理25の Python 例（諸法無我）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理25（諸法無我）の Python 例（`examples/theorem25_no_self.py`）の Lean 根拠です。3 つの部分からなります。

- **(A) 履歴相対の固定点**：履歴 \(h\in\{0,1,2\}\) ごとの縮小写像 \(F_h(S)=(1-L)c_h+LS\)（\(L=3/5\)）。各 \(F_h\) は縮小で、唯一の固定点 \(c_h\) を持ち、\(c_0\ne c_1\) なので**全履歴に共通する固定点は存在しません**（定理25 (25.1) の量化）。一般定理 `theorem25_no_common_fixedPoint_of_historyFamily` を使います。
- **(B) 候補自性 \(\Sigma\) と条件 25-D**：外生 \(\Gamma\in\{0,1\}^2\)（一様）、候補 \(s\in\mathbb Z\)、出力 \(Y=\Gamma_1-\Gamma_2+\beta s\)。構造因果モデル `Theorem25StructuralCausalModel` の \(\mathrm{do}(\Sigma=s)\) の法則で、**\(\beta=0\) なら 25-D（法則不変）→ Atman なし**（`theorem25_secondConclusion_of_functionalCompleteness`）、**\(\beta=1\) なら 25-D が破れて Atman が成立**します。※Python の連続ノイズ版を、有限値・決定論的な形に置き換えました。
- **(C) 父・母・子の逆役割関係（25.C1）と水平グラフの連結性**：有限グラフで `decide`。

### 0.2 このファイルが証明していないこと

- 有限モデル・toy の例です。**25-D は \(\beta=0\) という設計条件**であり、一般の認知モデルから導いたものではありません（\(\beta=1\) の反例は、25-D がない場合に無我が出ないことを示す）。
- (B) は連続ノイズ → **有限値・決定論的**に変更したものです（Python 側の変更）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理25の Python 例（`examples/theorem25_no_self.py`）の Lean 根拠
>
> (A) 履歴 \(h\in\{0,1,2\}\) ごとの縮小写像 \(F_h(S)=(1-L)c_h+LS\)（\(L=3/5\)）：各 \(F_h\) は縮小で唯一の固定点 \(c_h\)、\(c_0\ne c_1\) なので全履歴共通の固定点は存在しない（定理25 (25.1) の量化）。一般定理 `theorem25_no_common_fixedPoint_of_historyFamily` を使う。
>
> (B) 候補自性 \(\Sigma\)：外生 \(\Gamma\in\{0,1\}^2\)（一様）、候補 \(s\in\mathbb Z\)、出力 \(Y=\Gamma_1-\Gamma_2+\beta s\)。構造因果モデル `Theorem25StructuralCausalModel` の \(\mathrm{do}(\Sigma=s)\) 法則で、\(\beta=0\) なら 25-D（法則不変）→ Atman なし（`theorem25_secondConclusion_of_functionalCompleteness`）、\(\beta=1\) なら 25-D が破れて Atman が成立。※ Python の連続ノイズ版を、有限値・決定論的な形に置き換えた（対応表参照）。
>
> (C) 父・母・子の逆役割関係（25.C1）と水平グラフの連結性：有限グラフで `decide`。

### 0.4 節見出しのコメント（日本語訳）

> ## (A) 履歴相対の固定点
>
> ## (B) 候補自性 \(\Sigma\) と条件 25-D（有限値 SCM）
>
> ## (C) 父・母・子の逆役割関係と水平グラフの連結性（有限グラフ）

名前空間は `Tomabechi.Examples.Theorem25`（`open Tomabechi.Theorem16_25`）。

---

<a id="Tomabechi.Examples.Theorem25.c"></a>

## 定義 `c`

### 式

$$c_0=(0.1,0.9),\ c_1=(0.8,0.2),\ c_2=(0.5,0.5)$$

### Lean のコメント（日本語訳）

> Python の `c = {0:[0.1,0.9], 1:[0.8,0.2], 2:[0.5,0.5]}`。

### 定義の説明

履歴ごとの「目標点」（各履歴での固定点になる）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.F"></a>

## 定義 `F`

### 式

$$F_h(S)=(1-L)\,c_h+L\,S,\quad L=\tfrac35$$

### Lean のコメント（日本語訳）

> Python の `F(h,S)=(1-L)c_h+L S`、\(L=0.6\)。

### 定義の説明

履歴 \(h\) の自己意識の更新：目標点 \(c_h\) へ向けて縮小する写像。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.F_contracting"></a>

## 定理 `F_contracting`

### 式

$$F_h\ \text{は縮小率 }\tfrac35\ \text{の縮小写像}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各履歴の更新が**縮小写像**であること（\(\|F_h(S)-F_h(S')\|=\frac35\|S-S'\|\)）。

### 証明の概略

1. \(F_h(S)-F_h(S')=L(S-S')\)（`ring`）。積空間の距離は sup（各成分の \(\max\)）なので、各成分の差が \(\frac35|x_i-y_i|\) で、全体で \(\frac35\max\)（`mul_max_of_nonneg`）。

----

<a id="Tomabechi.Examples.Theorem25.F_fixed_iff"></a>

## 定理 `F_fixed_iff`

### 式

$$F_h(S)=S\iff S=c_h$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定点の特徴づけ：履歴 \(h\) の固定点は \(c_h\) だけ。

### 証明の概略

1. \((1-L)c_h+LS=S\iff(1-L)S=(1-L)c_h\iff S=c_h\)（\(L\ne1\)）。

----

<a id="Tomabechi.Examples.Theorem25.historyFixedPoints"></a>

## 定義 `historyFixedPoints`

### 式

$$h\mapsto c_h\ \ (\text{履歴別の唯一固定点族})$$

### Lean のコメント（日本語訳）

> 履歴別の唯一固定点族（担体は全空間）。

### 定義の説明

`HistoryFixedPoints`（Core）の具体例。

### 証明の概略

1. 担体は全体（`True`）、フィードバックは `F h`、固定点は \(c_h\)。
2. 固定点性と一意性は `F_fixed_iff`（\(F_h(S)=S\iff S=c_h\)）から。

----

<a id="Tomabechi.Examples.Theorem25.no_common_fixedPoint"></a>

## 定理 `no_common_fixedPoint`

### 式

$$c_0\ne c_1\ \wedge\ \neg\exists s,\ \forall h,\ F_h(s)=s$$

### Lean のコメント（日本語訳）

> (25.1)：履歴 0 と 1 の固定点は異なり、全履歴に共通する固定点は存在しない。

### 補題の説明

**定理25.1（共通の固定状態なし）の具体例**。

### 証明の概略

1. \(c_0\ne c_1\)：第 1 成分 \(0.1\ne0.8\)（`norm_num`）。
2. 一般定理 `theorem25_no_common_fixedPoint_of_historyFamily`（Core）に、履歴 \(0,1\) の固定点の分離（上の \(c_0\ne c_1\)）を渡す。

----

<a id="Tomabechi.Examples.Theorem25.uniformGamma"></a>

## 定義 `uniformGamma`

### 式

$$\Gamma\sim\mathrm{Unif}(\{0,1\}^2)$$

### Lean のコメント（日本語訳）

> 外生 \(\Gamma\in\{0,1\}^2\) の一様確率測度。

### 定義の説明

SCM の外生ノイズ（2 つの Bool の一様な組）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.ind"></a>

## 定義 `ind`

### 式

$$\mathbb 1(b)=\begin{cases}1&(b)\\0&(\neg b)\end{cases}$$

### Lean のコメント（日本語訳）

> 真偽値の指示関数（整数）。

### 定義の説明

Bool を整数 0/1 に直す関数。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.scm"></a>

## 定義 `scm`

### 式

$$Y=\Gamma_1-\Gamma_2+\beta\,\Sigma,\quad\text{基準の候補は }\Sigma=0$$

### Lean のコメント（日本語訳）

> Python の SCM \(Y=\Gamma_1-\Gamma_2+\beta\Sigma\)（ノイズなし・有限値版）。基準の候補は \(\Sigma=0\)。

### 定義の説明

構造因果モデル：出力 \(Y\) は外生 \(\Gamma\) と候補 \(\Sigma\) から決まる。\(\beta\) が候補の影響の強さ（\(\beta=0\) で候補に依存しない）。

### 証明の概略

1. `Theorem25StructuralCausalModel` のフィールドを具体的に与える（外生は `uniformGamma`、状態は \(\Gamma\)、出力は \(Y\)、基準の候補は 0）。

----

<a id="Tomabechi.Examples.Theorem25.scm_zero_functionallyComplete"></a>

## 定理 `scm_zero_functionallyComplete`

### 式

$$\beta=0\Rightarrow\text{25-D（機能的完備性）}$$

### Lean のコメント（日本語訳）

> \(\beta=0\)：\(\mathrm{do}(\Sigma=s)\) は \((\Gamma,Y)\) の同時法則を変えない（25-D の操作的形式）。

### 補題の説明

**25-D の成立**：候補に依存しない出力なので、介入しても法則が変わらない。

### 証明の概略

1. \(\beta=0\) なら出力方程式が \(s\) に依らないので、介入後の同時法則と基準の同時法則が一致（像測度が等しい）。

----

<a id="Tomabechi.Examples.Theorem25.scm_zero_no_atman"></a>

## 定理 `scm_zero_no_atman`

### 式

$$\beta=0\Rightarrow\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> \(\beta=0\)：25-D のもとで Atman は成立しない（定理25 (25.2) の因果コア）。

### 補題の説明

**無我の因果コアの具体例**：25-D が成り立つので、Atman は存在しない。

### 証明の概略

1. `scm_zero_functionallyComplete` と `theorem25_secondConclusion_of_functionalCompleteness`（Core）。

----

<a id="Tomabechi.Examples.Theorem25.scm_one_law_changes"></a>

## 定理 `scm_one_law_changes`

### 式

$$\beta=1\Rightarrow\mathrm{intervenedLaw}(2)\ne\mathrm{baselineLaw}$$

### Lean のコメント（日本語訳）

> \(\beta=1\)：\(\mathrm{do}(\Sigma=2)\) で \(\{Y=2\}\) の確率が 0 から正に変わる（25-D が破れる）。

### 補題の説明

**25-D が破れる**例：\(\beta=1\) だと候補が出力に効くので、介入で法則が変わります。

### 証明の概略

1. 基準（\(\Sigma=0\)）では \(Y=\Gamma_1-\Gamma_2\in\{-1,0,1\}\) で \(P(Y=2)=0\)。
2. \(\mathrm{do}(\Sigma=2)\) では \(Y=\Gamma_1-\Gamma_2+2\in\{1,2,3\}\) で \(P(Y=2)=\frac12>0\)。

----

<a id="Tomabechi.Examples.Theorem25.scm_one_has_atman"></a>

## 定理 `scm_one_has_atman`

### 式

$$\beta=1\Rightarrow\mathrm{hasAtman}$$

### Lean のコメント（日本語訳）

> \(\beta=1\)：Atman（独立・固定的な候補自性＋非冗長な因果効果）が成立する。25-D なしでは無我は出ない。

### 補題の説明

**25-D なしでは無我が出ない**ことの具体例。候補は外生の \(\Gamma\) と独立で、介入で法則が変わる。

### 証明の概略

1. `scm_one_law_changes` で非冗長な因果効果。
2. 独立・固定的な個体化の条件を確認し、`hasAtman` の定義を満たす。

----

<a id="Tomabechi.Examples.Theorem25.Person"></a>

## 定義 `Person`

### 式

$$\mathrm{Person}=\mathrm{Fin}\,6$$

### Lean のコメント（日本語訳）

> 頂点：0=祖父、1=父、2=母、3=子、4=叔母、5=祖母（Python の `people` と同じ）。

### 定義の説明

家族の登場人物 6 人。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.FatherOf"></a>

## 定義 `FatherOf`

### 式

$$\mathrm{FatherOf}(f,c)\iff(f,c)\in\{(0,1),(1,3)\}$$

### Lean のコメント（日本語訳）

> Python の `father_of = {(祖父,父),(父,子)}`。

### 定義の説明

「\(f\) は \(c\) の父」の関係。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.MotherOf"></a>

## 定義 `MotherOf`

### 式

$$\mathrm{MotherOf}(m,c)\iff(m,c)\in\{(2,3),(5,4)\}$$

### Lean のコメント（日本語訳）

> Python の `mother_of = {(母,子),(祖母,叔母)}`。

### 定義の説明

「\(m\) は \(c\) の母」の関係。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.HasFather"></a>

## 定義 `HasFather`

### 式

$$\mathrm{HasFather}(c,f)\iff\mathrm{FatherOf}(f,c)$$

### Lean のコメント（日本語訳）

> 逆役割ラベル：`HasFather c f ⇔ FatherOf f c`（25.C1、同一関係の逆向き記述）。

### 定義の説明

同じ関係を**逆の向き**で述べたもの（父-子 と 子-父）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.fatherOf_iff_hasFather"></a>

## 定理 `fatherOf_iff_hasFather`

### 式

$$\mathrm{FatherOf}(f,c)\iff\mathrm{HasFather}(c,f)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**(25.C1)**：役割ラベルの逆向きの記述は、同じ関係を表す。

### 証明の概略

1. `Iff.rfl`。

----

<a id="Tomabechi.Examples.Theorem25.adj"></a>

## 定義 `adj`

### 式

$$\text{無向の隣接関係（父母子の辺＋叔母-父の辺）}$$

### Lean のコメント（日本語訳）

> 水平関係グラフの隣接（父母子の辺に、叔母と父の関係の辺を 1 本加えたもの。無向化）。

### 定義の説明

人物の間の関係グラフの隣接。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem25.relation_graph_connected"></a>

## 定理 `relation_graph_connected`

### 式

$$\forall v,\ \text{祖父 }0\to v\ \text{の有限経路が存在}$$

### Lean のコメント（日本語訳）

> (25.C2)：水平関係グラフは連結（祖父から全員へ有限の経路がある）。

### 補題の説明

**関係グラフの連結性**：全員が、祖父から辿れる。

### 証明の概略

1. 隣接 \(0\!-\!1,\ 1\!-\!3,\ 1\!-\!4,\ 4\!-\!5,\ 3\!-\!2\)（`simp [adj]`）を示し、各頂点 \(v\) へ祖父 0 から具体的な経路（\(0\to1\to3\to2\)、\(0\to1\to4\to5\) など）を `Relation.ReflTransGen`（`tail`）で与える。

----

<a id="Tomabechi.Examples.Theorem25.child_has_father_and_mother"></a>

## 定理 `child_has_father_and_mother`

### 式

$$\exists f,m,\ \mathrm{FatherOf}(f,3)\wedge\mathrm{MotherOf}(m,3)$$

### Lean のコメント（日本語訳）

> (25.C4)：出生をもつ子（3）には父と母がいる。

### 補題の説明

子（3）には父（1）と母（2）がいる。

### 証明の概略

1. \(f=1\)、\(m=2\) を代入（`FatherOf 1 3` は \((1,3)=(1,3)\)、`MotherOf 2 3` は \((2,3)=(2,3)\) で `rfl`）。

----


## コメント修正記録

（なし）
