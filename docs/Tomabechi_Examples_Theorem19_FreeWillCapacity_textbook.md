# Tomabechi/Examples/Theorem19_FreeWillCapacity.lean 解説

> 対象: [`Tomabechi/Examples/Theorem19_FreeWillCapacity.lean`](../Tomabechi/Examples/Theorem19_FreeWillCapacity.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理19（自由意思の容量）の Python 例 `examples/theorem19_free_will_capacity.py` の Lean 根拠です。有限のゴール \(G\in\mathrm{Fin}\,4\)（一様）、文脈 \(X=\mathrm{Unit}\)、決定論的方策 \(\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,n\)（出力アルファベットの大きさ \(n\)）を考え、プロジェクト既存の有限条件付き相互情報量 \(I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)\) を使って、自由意思容量
$$F(n)=\max_{\varphi}\,I(G;\varphi(G))$$
を定義します。このファイルが証明するのは次です。

- \(H(G\mid X)=\log4\)。
- **上界と達成**：任意の方策で \(I\le H(G\mid X)=\log4\)。**単射な方策**で \(I=H\)（`theorem21_finite_information_capacity`）。したがって \(F(4)=\log4\)。出力が 1 個なら \(I=0\)、\(F(1)=0\)。
- **中間の容量値**：\(F(2)=\log2\)、\(F(3)=\tfrac32\log2\)。出力が 2 個・3 個のとき、\(\mathrm{Fin}\,4\) からの写像（それぞれ 16 個・81 個）を**全部列挙**して最大値を求め、「2 個ずつに分ける」方策（\(2+2\)）、「\(2,1,1\) に分ける」方策が上界を達成することを示す。
- **単調性**（定理19の評価を保つ単射）：出力アルファベットの包含 \(\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,(n+1)\) で \(F(n)\le F(n+1)\)。端点正規化 \(f=(F-F(1))/(F(4)-F(1))\) は \(f(1)=0\)、\(f(4)=1\)。
- **ゴールと独立なランダム出力**：出力がゴールに依存しない確率的出力なら、一般の測度論的条件付き相互情報量（KL ダイバージェンスで定義）は**厳密に 0**。具体例（二点分布 \((1/3,2/3)\)）と、任意の有限確率出力分布 \(\nu\) について証明する。
- **反例**（粗い観測）：\(y(g)=(0.1,0.4,0.6,0.9)\) は集合として単射だが、解像度 \(b\) の区間分割で観測すると、\(b=1\)（自明 σ 代数）で \(I=0<\log4\)、\(b=2\) で \(I=\log2\)、\(b=10\) で \(I=\log4\)。単射であっても、観測の粒度が粗いと情報は落ちる。

### 0.2 このファイルが証明していないこと

- **有限・決定論的方策**（または、独立なランダム出力の場合）に限る特殊な場合で、一般の問題族・可測出力での容量値（`Theorem19_Heterogeneous`、`Theorem19_Counterexample`）の代替ではありません。
- ランダム出力については「ゴールと独立なら情報は 0」を示しただけで、**一般の確率的カーネルの容量（最大値）の計算はしていません**。\(F(2)\)・\(F(3)\) の値は決定論的方策の範囲での最大値です（確率的方策を含めた最大値ではありません）。
- 反例は「粗い観測では情報が落ちる」という例で、原文の定理19の反例ではありません（原文の仮定を満たさないモデルの例です）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理19の Python 例（`examples/theorem19_free_will_capacity.py`）の Lean 根拠
>
> 有限ゴール \(G\in\mathrm{Fin}\,4\)（一様）、文脈 \(X=\mathrm{Unit}\)、決定論的方策 \(\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,n\)（出力アルファベットの大きさ \(n\)）。`finiteConditionalMutualInformation`（\(I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)\)、プロジェクト既存の有限 CMI）を使い、自由意思容量 \(F(n)=\max_\varphi I\) を定義する。
>
> * \(H(G\mid X)=\log4\)。
> * 上界 \(I\le H(G\mid X)\)、単射方策で \(I=H\)（`theorem21_finite_information_capacity`）、したがって \(F(4)=\log4\)。出力が 1 個なら \(I=0\)、\(F(1)=0\)。
> * ゴールと独立な非退化二値確率出力の一般測度 CMI は 0。2 出力・3 出力の有限容量は 4 値方策の全分割を列挙して、それぞれ \(F(2)=\log2\)、\(F(3)=\tfrac32\log2\)。
> * 単調性（定理19の評価保存単射）：出力アルファベットの包含 \(\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,(n+1)\) で \(F(n)\le F(n+1)\)。
> * 端点正規化 \(f=(F-F(1))/(F(4)-F(1))\) は \(f(1)=0\)、\(f(4)=1\)。
> * 反例（`Theorem19_Counterexample.lean` の反例モデルの精神）：\(y(g)=(0.1,0.4,0.6,0.9)\) は集合として単射だが、解像度 \(b\) の区間分割で観測すると \(b=1\)（自明 σ 代数）で \(I=0<\log4\)、\(b=2\) で \(I=\log2\)、\(b=10\) で \(I=\log4\)。
>
> 範囲外：一般の問題族・可測出力の容量値（`Theorem19_Heterogeneous`、`Theorem19_Counterexample`）。

### 0.4 節見出しのコメント（日本語訳）

> 反例：単射だが解像度の粗い観測／ゴールと独立な確率的出力（この例ではゴールを一様な `Fin 4`、出力を非退化な二点分布とし、出力核をゴールに依存しない定数核にする。同時法則を条件付き独立参照測度そのもので構成するため、KL 自己比較の値 0 を既存の一般測度 CMI API で得る。）

名前空間は `Tomabechi.Examples.Theorem19`（`open Tomabechi.Theorem21`）。`set_option maxHeartbeats 1000000` は計算予算の設定。

----

<a id="Tomabechi.Examples.Theorem19.mass"></a>

## 定義 `mass`

### 式

$$P(G=g\mid x)=\tfrac14$$

### Lean のコメント（日本語訳）

> 文脈 `Unit` 上のゴール事前（一様 \(1/4\)）。

### 定義の説明

4 値のゴールの一様な事前分布です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.mass_nonneg"></a>

## 補題 `mass_nonneg`

### 式

$$P(G=g\mid x)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率が非負。

### 証明の概略

1. \(1/4\ge0\)。

----

<a id="Tomabechi.Examples.Theorem19.mass_total"></a>

## 補題 `mass_total`

### 式

$$\sum_x\sum_gP(G=g\mid x)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率の総和が 1（\(4\times\frac14\)）。

### 証明の概略

1. 有限和の計算。

----

<a id="Tomabechi.Examples.Theorem19.entropy_eq_log_four"></a>

## 補題 `entropy_eq_log_four`

### 式

$$H(G\mid X)=\log4$$

### Lean のコメント（日本語訳）

> ゴールの条件付きエントロピーは \(H(G\mid X)=\log4\)。

### 補題の説明

一様な 4 値のゴールのエントロピーは \(\log4\)。

### 証明の概略

1. `finiteConditionalEntropyGivenInput` の定義を展開し、一様性から計算。

----

<a id="Tomabechi.Examples.Theorem19.cmi"></a>

## 定義 `cmi`

### 式

$$I_\varphi=I(G;\varphi(G)\mid X)$$

### Lean のコメント（日本語訳）

> 方策 \(\varphi\) の CMI（文脈なし）。

### 定義の説明

方策 \(\varphi\) の出力がゴールについて持つ情報量（有限 CMI）。

### 証明の概略

1. 定義：`finiteConditionalMutualInformation mass (fun _ g => φ g)`。

----

<a id="Tomabechi.Examples.Theorem19.cap"></a>

## 定義 `cap`

### 式

$$F(n+1)=\max_{\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,(n+1)}I_\varphi$$

### Lean のコメント（日本語訳）

> 自由意思容量 \(F(n+1)=\max_{\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,(n+1)}I(G;\varphi(G))\)（出力アルファベットの大きさ \(n+1\)）。

### 定義の説明

**自由意思の容量**：出力アルファベットの大きさ \(n+1\) の決定論的方策の CMI の最大値（有限集合なので `sup'` が最大値）。

### 証明の概略

1. 定義：`Finset.univ.sup'`。

----

<a id="Tomabechi.Examples.Theorem19.cmi_le_log_four"></a>

## 補題 `cmi_le_log_four`

### 式

$$I_\varphi\le\log4$$

### Lean のコメント（日本語訳）

> 上界：任意の方策で \(I\le H(G\mid X)=\log4\)。

### 補題の説明

情報量はゴールのエントロピー以下。

### 証明の概略

1. `finiteConditionalMutualInformation_le_entropy`（既存：有限 CMI \(\le H(G\mid X)\)）に `entropy_eq_log_four` を代入。

----

<a id="Tomabechi.Examples.Theorem19.cap_le_log_four"></a>

## 補題 `cap_le_log_four`

### 式

$$F(n)\le\log4$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

容量の上界（`sup'` の各項に `cmi_le_log_four`）。

### 証明の概略

1. `Finset.sup'_le`。

----

<a id="Tomabechi.Examples.Theorem19.cmi_injective"></a>

## 補題 `cmi_injective`

### 式

$$\varphi\ \text{単射}\Rightarrow I_\varphi=\log4$$

### Lean のコメント（日本語訳）

> 単射な方策（Python の「出力が 4 個以上」）で \(I=H(G\mid X)=\log4\)。

### 補題の説明

**情報達成**：方策がゴールを可逆に符号化（単射）するなら、出力はゴールの情報をすべて持つ。

### 証明の概略

1. `theorem21_finite_information_capacity`（単射で \(I=H\)）を、一様な事前分布で適用し、`entropy_eq_log_four` で書き換える。

----

<a id="Tomabechi.Examples.Theorem19.cap_one"></a>

## 補題 `cap_one`

### 式

$$F(1)=0$$

### Lean のコメント（日本語訳）

> 出力が 1 個（\(n=1\)）なら \(I=0\)：零容量。

### 補題の説明

出力が 1 通りしかなければ、ゴールについて何も分からないので容量 0。

### 証明の概略

1. 任意の方策 \(\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,1\) で CMI = 0（条件付きエントロピー \(H(G\mid X,Y)=H(G\mid X)\)、出力が常に同じ）。
2. `sup'` の各項が 0 なので 0。

----

<a id="Tomabechi.Examples.Theorem19.cap_four"></a>

## 補題 `cap_four`

### 式

$$F(4)=\log4$$

### Lean のコメント（日本語訳）

> 4 個の出力があれば、容量は \(\log4\)（上界と単射方策）。

### 補題の説明

出力が 4 通りあれば、恒等写像（単射）で上界 \(\log4\) を達成。

### 証明の概略

1. 上界は `cap_le_log_four`。
2. 恒等写像 \(\mathrm{id}:\mathrm{Fin}\,4\to\mathrm{Fin}\,4\) は単射なので `cmi_injective` で \(\log4\)、`le_sup'` で下から。

----

<a id="Tomabechi.Examples.Theorem19.cmi_castSucc"></a>

## 補題 `cmi_castSucc`

### 式

$$I_{\iota\circ\varphi}=I_\varphi\quad(\iota:\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,(n+1))$$

### Lean のコメント（日本語訳）

> CMI は出力のラベル付けに依らない（ファイバーだけで決まる）。\(\mathrm{Fin}\,n\hookrightarrow\mathrm{Fin}\,(n+1)\) で保存される。

### 補題の説明

出力のラベルを付け替えても（単射な埋め込みで）情報量は変わりません。

### 証明の概略

1. CMI は各出力値のファイバー（同じ出力を持つゴールの集合）だけで決まる。`Fin.castSucc` はファイバーを保つ。

----

<a id="Tomabechi.Examples.Theorem19.cap_mono"></a>

## 補題 `cap_mono`

### 式

$$F(n)\le F(n+1)$$

### Lean のコメント（日本語訳）

> 定理19の単調性（評価値を保存する単射の埋め込み）：\(F(n)\le F(n+1)\)。

### 補題の説明

**容量の単調性**：出力アルファベットを増やしても容量は減らない。

### 証明の概略

1. 任意の \(\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,n\) を `Fin.castSucc` で埋め込んだ方策が、同じ CMI を持つ（`cmi_castSucc`）。
2. よって \(F(n)\le F(n+1)\)。

----

<a id="Tomabechi.Examples.Theorem19.python_layers_monotone_with_endpoints"></a>

## 補題 `python_layers_monotone_with_endpoints`

### 式

$$F(1)\le F(2)\le F(3)\le F(4),\ F(1)=0,\ F(4)=\log4$$

### Lean のコメント（日本語訳）

> Python の層列 \(m_\alpha=[1,2,3,4,4]\) に対応する容量列は単調で、端点は \(0\) と \(\log4\)。

### 補題の説明

Python の層列に対応する容量列の単調性と端点の値。

### 証明の概略

1. `cap_mono` を 3 回、`cap_one`、`cap_four`。

----

<a id="Tomabechi.Examples.Theorem19.normalization_endpoints"></a>

## 補題 `normalization_endpoints`

### 式

$$\frac{F(1)-F(1)}{F(4)-F(1)}=0,\ \ \frac{F(4)-F(1)}{F(4)-F(1)}=1$$

### Lean のコメント（日本語訳）

> 端点の正規化 \(f=(F-F(1))/(F(4)-F(1))\)：\(f(1)=0\)、\(f(4)=1\)（\(\log4>0\)）。

### 補題の説明

正規化した容量 \(f\) の端点の値。分母 \(\log4-0>0\) が必要です。

### 証明の概略

1. `cap_one`・`cap_four` と、\(\log4>0\)（`Real.log_pos`）で除法を計算。

----

<a id="Tomabechi.Examples.Theorem19.bins1"></a>

## 定義 `bins1`

### 式

$$\mathrm{bins}_1(g)=0$$

### Lean のコメント（日本語訳）

> 解像度 \(b\) の区間分割による観測：Python の `idx=min(int(y b), b-1)`、\(y=(0.1,0.4,0.6,0.9)\)。

### 定義の説明

解像度 1（区間 1 個）の観測：すべてのゴールが同じ出力。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.bins2"></a>

## 定義 `bins2`

### 式

$$\mathrm{bins}_2=(0,0,1,1)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

解像度 2 の観測：\(y=(0.1,0.4,0.6,0.9)\) を 2 区間に分けると、前半 2 つが 0、後半 2 つが 1。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.bins10"></a>

## 定義 `bins10`

### 式

$$\mathrm{bins}_{10}=(1,4,6,9)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

解像度 10 の観測：4 つの値がすべて異なる区間に入る。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.bins1_info_zero"></a>

## 補題 `bins1_info_zero`

### 式

$$I(\mathrm{bins}_1)=0\ \wedge\ 0<\log4-I$$

### Lean のコメント（日本語訳）

> \(b=1\)（自明 σ 代数）：集合として単射な \(y\) でも、観測される情報は \(I=0<\log4=H(G\mid X)\)。

### 補題の説明

**反例**：値の組 \(y\) は集合として単射でも、解像度 1 の観測では情報が全く得られない。

### 証明の概略

1. 解像度 1 の分割では、すべての値が同じ出力に写る（`Subsingleton.elim`）。
2. 条件付きエントロピー \(H(G\mid X,Y)\) が \(H(G\mid X)\) に等しくなり、定義の展開と `simp` で \(I=0\)。
3. \(\log4>0\) なので \(\log4-I>0\)。

----

<a id="Tomabechi.Examples.Theorem19.bins10_info_full"></a>

## 補題 `bins10_info_full`

### 式

$$I(\mathrm{bins}_{10})=\log4$$

### Lean のコメント（日本語訳）

> \(b=10\)：区間が十分細かければ（\(y\) を分離）\(I=\log4\)。

### 補題の説明

解像度が十分高ければ、情報はすべて保たれる。

### 証明の概略

1. `bins10` は単射（値 1,4,6,9 がすべて異なる）なので `cmi_injective`。

----

<a id="Tomabechi.Examples.Theorem19.bins2_info"></a>

## 補題 `bins2_info`

### 式

$$I(\mathrm{bins}_2)=\log2$$

### Lean のコメント（日本語訳）

> \(b=2\)：\(I=\log2\)（2 つのブロック \(\{0,1\},\{2,3\}\)）。

### 補題の説明

解像度 2 では、4 値のゴールが 2 つのブロックに分けられ、情報は \(\log2\)（1 ビット）。

### 証明の概略

1. 各ブロックの確率 \(1/2\)、ブロック内の条件付きエントロピー \(\log2\) から \(H(G\mid X,Y)=\log2\)、よって \(I=\log4-\log2=\log2\)。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMass"></a>

## 定義 `randomOutputMass`

### 式

$$q(0)=\tfrac13,\quad q(1)=\tfrac23$$

### Lean のコメント（日本語訳）

> 二点出力の非退化分布 \((1/3,2/3)\)。

### 定義の説明

ゴールと独立に出力される、偏りのある 2 値のランダム出力の分布。どちらの値も確率が正（非退化）です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMass_nonneg"></a>

## 補題 `randomOutputMass_nonneg`

### 式

$$q(y)\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率は非負。

### 証明の概略

1. `y=0` か否かで場合分けして `norm_num`。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMass_sum"></a>

## 補題 `randomOutputMass_sum`

### 式

$$\sum_{y}q(y)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

総和が 1（\(1/3+2/3\)）。

### 証明の概略

1. `Fin 2` の和を展開して `norm_num`。

----

<a id="Tomabechi.Examples.Theorem19.randomGoalMeasure"></a>

## 定義 `randomGoalMeasure`

### 式

$$\mu_G=\tfrac14\sum_{g\in\mathrm{Fin}\,4}\delta_g$$

### Lean のコメント（日本語訳）

> 一様なゴール分布を有限確率測度にする。

### 定義の説明

一様な `Fin 4` のゴール分布を、測度論の言葉（`Measure`）で表したもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.randomGoalMeasure_probability"></a>

## 補題 `randomGoalMeasure_probability`

### 式

$$\mu_G(\mathrm{Fin}\,4)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全質量が 1 の確率測度。

### 証明の概略

1. `Theorem19_22.finiteGoalMeasureOfMass_isProbability`（質量が非負で総和 1 なら確率測度）に、各質量 \(\frac14\ge0\) と総和 \(=1\) を `norm_num` で与える。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMeasure"></a>

## 定義 `randomOutputMeasure`

### 式

$$\nu=\tfrac13\delta_0+\tfrac23\delta_1$$

### Lean のコメント（日本語訳）

> ゴールと独立な出力分布を有限確率測度にする。

### 定義の説明

`randomOutputMass` を測度にしたもの。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMeasure_probability"></a>

## 補題 `randomOutputMeasure_probability`

### 式

$$\nu(\mathrm{Fin}\,2)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率測度であること。

### 証明の概略

1. `finiteGoalMeasureOfMass_isProbability`（\(q\ge0\)、\(\sum q=1\)）に `randomOutputMass_nonneg`、`randomOutputMass_sum` を与える。

----

<a id="Tomabechi.Examples.Theorem19.randomOutputMeasure_nondegenerate"></a>

## 補題 `randomOutputMeasure_nondegenerate`

### 式

$$\nu(\{0\})=\tfrac13,\quad\nu(\{1\})=\tfrac23$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二点の質量がどちらも正で、「非退化」であること。（退化した出力、つまり常に同じ値、なら独立なのは当たり前なので、非自明な例にするための確認です。）

### 証明の概略

1. `finiteGoalMeasureOfMass_singleton`（1 点の質量が \(q\) に等しい）で `simp`。

----

<a id="Tomabechi.Examples.Theorem19.independentRandomOutputLaw"></a>

## 定義 `independentRandomOutputLaw`

### 式

$$\text{joint}=\text{dirac}\otimes(\mu_G\otimes\nu)\ \ \text{（ゴールと出力が独立な同時法則）}$$

### Lean のコメント（日本語訳）

> 独立確率出力の条件付き相互情報量データ。`joint` を条件付き独立参照測度と同じ構成にすることで、KL 自己比較となる。

### 定義の説明

一般の測度論的 CMI の枠組み（`Theorem22.ConditionalMutualInformationLaw`）に、「入力は 1 点（`Unit`）、ゴールは一様、出力は \(\nu\)、ゴールと出力は独立」のデータを渡して作る構造体です。同時法則 `joint` を、参照測度（周辺分布の積）と**全く同じ式**で作るので、あとで KL ダイバージェンスが「同じ測度どうし」の比較になり 0 になります。

### 証明の概略

1. 入力・ゴール核・出力核を定数核（`Kernel.const`）で作る。
2. 同時法則を `input ⊗ₘ ((goalKernel ∥ₖ outputKernel) ∘ₖ copy)` と定める。
3. 周辺の整合性（ゴール周辺・出力周辺）を、積核の周辺化の公式（`Kernel.fst_prod`、`Kernel.snd_prod` など）で示す。

----

<a id="Tomabechi.Examples.Theorem19.independent_random_output_cmi_zero"></a>

## 補題 `independent_random_output_cmi_zero`

### 式

$$\mathrm{KL}\bigl(\text{joint}\,\|\,\text{reference}\bigr)=0$$

### Lean のコメント（日本語訳）

> 非退化な確率的出力でも、ゴールと独立なら測度 CMI は厳密に 0。

### 補題の説明

ゴールと独立な出力は、たとえランダムで非退化でも、ゴールの情報を**まったく運びません**（\(I=0\)）。上の構成で `joint` と参照測度が同じなので、KL ダイバージェンスの自己比較 \(\mathrm{KL}(\mu\|\mu)=0\) です。

### 証明の概略

1. `joint = referenceMeasure`（定義から `rfl`）。
2. `InformationTheory.klDiv_self`。

----

<a id="Tomabechi.Examples.Theorem19.independentRandomOutputFiniteLaw"></a>

## 定義 `independentRandomOutputFiniteLaw`

### 式

$$\mathrm{KL}<\infty$$

### Lean のコメント（日本語訳）

> 上の独立例は有限 KL 条件も満たすので、既存の一般測度 CMI-law に入る。

### 定義の説明

KL が有限（実は 0）という条件を添えて、一般 API（`FiniteConditionalMutualInformationLaw`）の元にしたもの。

### 証明の概略

1. KL が 0 なので有限（`norm_num`）。

----

<a id="Tomabechi.Examples.Theorem19.independent_random_output_finite_score_zero"></a>

## 補題 `independent_random_output_finite_score_zero`

### 式

$$\mathrm{finiteKLDivergenceScore}=0$$

### Lean のコメント（日本語訳）

> 有限 CMI-law が返す KL スコアも 0。

### 補題の説明

一般 API が返す「スコア」（KL の実数値）が 0。

### 証明の概略

1. 定義を展開し、`independent_random_output_cmi_zero`。

----

<a id="Tomabechi.Examples.Theorem19.independentOutputLawFor"></a>

## 定義 `independentOutputLawFor`

### 式

$$\text{任意の有限確率測度 }\nu\text{ に対し、joint}=\mu_G\otimes\nu\text{（独立）}$$

### Lean のコメント（日本語訳）

> 任意の有限確率出力測度 \(\nu\) に対する、ゴールと独立な確率カーネルの law。出力値の分布を選ばず、同じ確率測度をすべての \(g\) に割り当てる。

### 定義の説明

前の具体例（二点分布）を一般化して、**任意の有限の出力空間 \(Y\)** と**任意の確率測度 \(\nu\)** に対して、独立出力の law を作ります。

### 証明の概略

`independentRandomOutputLaw` と同じ構成で、出力核を `Kernel.const Unit ν` にする。

----

<a id="Tomabechi.Examples.Theorem19.independent_output_kl_zero_for"></a>

## 補題 `independent_output_kl_zero_for`

### 式

$$\mathrm{KL}\bigl(\text{joint}\,\|\,\text{reference}\bigr)=0$$

### Lean のコメント（日本語訳）

> 任意の有限確率出力分布 \(\nu\) は独立カーネルとなり、CMI の KL 値は 0。

### 補題の説明

任意の有限確率出力分布について、**ゴールと独立な出力の情報量は 0**。

### 証明の概略

1. 構成から `joint = referenceMeasure`（`rfl`）。
2. 確率測度に対する `klDiv_self`。

----

<a id="Tomabechi.Examples.Theorem19.independentOutputFiniteLawFor"></a>

## 定義 `independentOutputFiniteLawFor`

### 式

$$\mathrm{KL}<\infty$$

### Lean のコメント（日本語訳）

> 任意の \(\nu\) に対し、出力核・joint・参照測度・有限 KL 条件をすべて備えた law。

### 定義の説明

一般 API の元（KL 有限の条件つき）にしたもの。

### 証明の概略

1. `independent_output_kl_zero_for` で KL が 0 なので有限。

----

<a id="Tomabechi.Examples.Theorem19.independent_output_finite_score_zero_for"></a>

## 補題 `independent_output_finite_score_zero_for`

### 式

$$\mathrm{finiteKLDivergenceScore}=0$$

### Lean のコメント（日本語訳）

> 任意の有限確率出力分布に対する一般測度 CMI スコアは 0。

### 補題の説明

上と同じ内容を、一般 API のスコアの形で述べたもの。

### 証明の概略

1. 定義を展開して `independent_output_kl_zero_for`。

----

<a id="Tomabechi.Examples.Theorem19.tuplePolicy2"></a>

## 定義 `tuplePolicy2`

### 式

$$\varphi=(a,b,c,d):\ \mathrm{Fin}\,4\to\mathrm{Fin}\,2$$

### Lean のコメント（日本語訳）

> `Fin 4` 上の任意の方策を 4 個の出力値で表す列挙用表現。

### 定義の説明

\(\mathrm{Fin}\,4\to\mathrm{Fin}\,2\) の写像は、4 つの値 \((\varphi(0),\varphi(1),\varphi(2),\varphi(3))\) で決まる 16 通り。これを網羅するための書き方です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.cmi_two_le_log_two_tuple"></a>

## 補題 `cmi_two_le_log_two_tuple`

### 式

$$I(\varphi)\le\log2\qquad(\varphi\ \text{16 通りすべて})$$

### Lean のコメント（日本語訳）

> 二出力の 16 個の等号分割を尽くすと、情報量は \(\log2\) 以下。

### 補題の説明

出力が 2 個の方策 16 個のそれぞれについて情報量を計算して、すべて \(\log2\) 以下であることを確かめます。分割のタイプは \((4,0)\)（全部同じ）、\((3,1)\)、\((2,2)\) で、\(I=0\)、\(\log4-\tfrac34\log3\)、\(\log2\) になります。

### 証明の概略

1. \(a,b,c,d\) の全 16 通りを `fin_cases` で分け、情報量の定義（条件付きエントロピーの差）を展開して `simp`。
2. 必要な対数の評価：\(\log4=2\log2\)、\(4\log2\le3\log3\)（\(16\le27\)）など。`nlinarith` で閉じる。

----

<a id="Tomabechi.Examples.Theorem19.cmi_two_le_log_two"></a>

## 補題 `cmi_two_le_log_two`

### 式

$$\forall\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,2,\ I(\varphi)\le\log2$$

### Lean のコメント（日本語訳）

> 任意の二値方策は 4 個の値のタプルに書き直せるため、上の分類がすべての方策を覆う。

### 補題の説明

任意の 2 値方策を 4 つの値の組として書き直せるので、上の 16 通りの結果がすべての方策に適用されます。

### 証明の概略

1. \(\varphi=(\varphi(0),\dots,\varphi(3))\) を `funext` と `fin_cases` で示し、`cmi_two_le_log_two_tuple`。

----

<a id="Tomabechi.Examples.Theorem19.cap_two"></a>

## 補題 `cap_two`

### 式

$$F(2)=\log2$$

### Lean のコメント（日本語訳）

> 二つずつに分ける方策が上界を達成するので \(F(2)=\log2\)。

### 補題の説明

出力が 2 個のときの容量は \(\log2\)（1 ビット分）。4 つのゴールを 2 つずつに分ける方策 `bins2`（既出の解像度 2 の区間分割。\(b=2\) で \(I=\log2\)）が上界を達成します。

### 証明の概略

1. 上界は `cmi_two_le_log_two`。
2. 下界は既出の `bins2_info`（\(I(\texttt{bins2})=\log2\)）を `Finset.le_sup'` で最大値以下に置く。

----

<a id="Tomabechi.Examples.Theorem19.tuplePolicy3"></a>

## 定義 `tuplePolicy3`

### 式

$$\varphi=(a,b,c,d):\ \mathrm{Fin}\,4\to\mathrm{Fin}\,3$$

### Lean のコメント（日本語訳）

> `Fin 3` 上の方策を 4 つの出力値で表す列挙用表現。

### 定義の説明

\(\mathrm{Fin}\,4\to\mathrm{Fin}\,3\) の写像 81 通りを網羅する表現。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem19.cmi_three_le_log_three_tuple"></a>

## 補題 `cmi_three_le_log_three_tuple`

### 式

$$I(\varphi)\le\tfrac32\log2\qquad(\varphi\ \text{81 通りすべて})$$

### Lean のコメント（日本語訳）

> 三出力の 81 個の写像を列挙すると、CMI は \((3/2)\log2\) 以下。

### 補題の説明

81 個の方策すべてについて計算します。分割のタイプは \((4,0,0)\)、\((3,1,0)\)、\((2,2,0)\)、\((2,1,1)\) で、最大は \((2,1,1)\) の \(\tfrac32\log2\)。

### 証明の概略

1. \(a,b,c,d\) の全 81 通りを `fin_cases`、定義を展開して `simp`。
2. 対数の評価（\(\log3\) を含む不等式 \(4\log2\le3\log3\) など）を `nlinarith` で。

----

<a id="Tomabechi.Examples.Theorem19.cmi_three_tuple211"></a>

## 補題 `cmi_three_tuple211`

### 式

$$I\bigl((0,1,2,2)\bigr)=\tfrac32\log2$$

### Lean のコメント（日本語訳）

> 代表元 \((0,1,2,2)\) は \((2,1,1)\) 分割なので最大値を達成する。

### 補題の説明

2 つの値を同じ出力に、残り 2 つを別々の出力に写す方策が \(\tfrac32\log2\) を達成。\(I=H(G)-H(G\mid Y)=\log4-\tfrac12\log2=\tfrac32\log2\)。

### 証明の概略

1. 条件付きエントロピーを有限和として展開し、\(\log4=2\log2\)、\(\log(1/2)=-\log2\) などで整理（`norm_num`、`ring`）。

----

<a id="Tomabechi.Examples.Theorem19.cmi_three_le_log_three"></a>

## 補題 `cmi_three_le_log_three`

### 式

$$\forall\varphi:\mathrm{Fin}\,4\to\mathrm{Fin}\,3,\ I(\varphi)\le\tfrac32\log2$$

### Lean のコメント（日本語訳）

> 任意の三値方策を 4 つの値で列挙するので上界はすべての方策に成り立つ。

### 補題の説明

81 通りの結果をすべての 3 値方策に拡張。

### 証明の概略

1. \(\varphi\) を 4 つの値の組に書き直し（`funext`）、`cmi_three_le_log_three_tuple`。

----

<a id="Tomabechi.Examples.Theorem19.cap_three"></a>

## 補題 `cap_three`

### 式

$$F(3)=\tfrac32\log2$$

### Lean のコメント（日本語訳）

> \((2,1,1)\) 方策が上界を達成し、\(F(3)=\tfrac32\log2\) となる。

### 補題の説明

出力が 3 個のときの容量は \(\tfrac32\log2\)。出力が 2 個のとき（\(\log2\)）と 4 個のとき（\(\log4=2\log2\)）の間の値で、増え方は一様ではありません。

### 証明の概略

1. 上界：`cmi_three_le_log_three`（`sup'_le`）。
2. 下界：代表元 \((0,1,2,2)\) の値 `cmi_three_tuple211` を `le_sup'` で最大値以下に置く。

----

## コメント修正記録

- ファイル冒頭コメントの「反例（P16 の精神）」を「反例（`Theorem19_Counterexample.lean` の反例モデルの精神）」に修正（作業用の計画番号を公開用の参照に置換。宣言は不変）。
