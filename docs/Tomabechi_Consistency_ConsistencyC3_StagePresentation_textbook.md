# Tomabechi/Consistency/ConsistencyC3_StagePresentation.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC3_StagePresentation.lean`](../Tomabechi/Consistency/ConsistencyC3_StagePresentation.lean)（共通の層の表象を持つ、元の H-stage の組み立てと、定理19・21・22・23-B の接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**元の H-stage**（段階の谷の入力）を、**共通の層の表象**つきで組み立てるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「段階の谷と情報」（C3）の土台です。

* **共通の表象**：原子 \(n\in\mathbb N\cup\{\top\}\) を \(\tfrac n{n+1}\)（頂は 1）に送る単射・単調な写像。
* **各段の谷**：中心 \(\mathrm{rep}(n+1)\) の二次の谷。平均場は、中心にある Dirac 測度の核を**積分したもの**（積分表示）。滞在時間 \(4(n+2)(n+3)\)、隣り合う中心の間隔 \(\tfrac1{(n+2)(n+3)}\)。端点で整合する谷の列。
* **定理21の四つの結論**（直接の KL による条件付き相互情報量を含む）が、**同じ平均場入力・同じ上位層の情報法則**で成り立つ。ゴールは一様な二値（エントロピー \(\log2\)）、物理層は決定的（エントロピー 0）。
* **定理19の容量**：許容問題（物理の問題と上位の問題）と、層の容量 \(\mathcal F(a)\)：底で 0、頂で正、層の順序について単調。
* **定理23-B の切り替え**：元の（緩和していない）条件 23-B の結論を、完全な証明書 `HStageSwitchingCertificate` として保存。

### 0.2 このファイルが証明していないこと

* 二次の谷の具体的な列です。原文の基礎的な条件から谷の入力を導いたわけではありません。
* 層ごとに同じ（上位層の）情報法則を使います。層ごとに異なる情報量を割り当てるわけではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 各段の原子法則はその段の中心にある Dirac 確率測度とする。原子型・順序・proper source layer・単調表象は全段で共通にし、段ごとの再構成核を積分すると二次谷の臨場感場になる。これは元の H-stage を組み立てる最初の部品である。

---

<a id="Tomabechi.Consistency.C3.Atom"></a>

## 定義 `Atom`

### 式

$$
\mathbb N\cup\{\top\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の「原子」の型です。自然数に最上位元 \(\top\) を加えた順序集合 `WithTop ℕ` です。原子の型・順序・「源となる層」・単調な表象は、全段で共通にします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.representation"></a>

## 定義 `representation`

### 式

$$
n\mapsto\tfrac{n}{n+1},\quad\top\mapsto1
$$

### Lean のコメント（日本語訳）

> 共通表象：自然数段は1未満で単調に増え、最上位元だけを1へ送る。

### 定義の説明

**共通の表象**です。自然数の段 \(n\) を \(\tfrac n{n+1}\)（1 未満で単調に増える）に、最上位元 \(\top\) だけを 1 に送ります。実数の直線の上に、層を並べる座標になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.representation_lt_top"></a>

## 補題 `representation_lt_top`

### 式

$$
\tfrac{n}{n+1}<1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

自然数の段の表象は 1 未満です。

### 証明の概略

1. \(n<n+1\) から `div_lt_one`。

----

<a id="Tomabechi.Consistency.C3.representation_injective"></a>

## 補題 `representation_injective`

### 式

$$
\text{表象は単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

表象は単射です（異なる原子は異なる実数に送られる）。

### 証明の概略

1. 場合分け：\(\top\) と \(\top\)、\(\top\) と自然数、自然数同士。
2. \(\top\) は 1、自然数は 1 未満なので区別される。自然数同士は \(\tfrac m{m+1}=\tfrac n{n+1}\Rightarrow m=n\)。

----

<a id="Tomabechi.Consistency.C3.representation_monotone"></a>

## 補題 `representation_monotone`

### 式

$$
a\le b\Rightarrow\mathrm{rep}(a)\le\mathrm{rep}(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

表象は単調です。

### 証明の概略

1. 場合分け。\(\top\) が上にある場合は \(\mathrm{rep}<1\)（`representation_lt_top`）。自然数同士は \(\tfrac n{n+1}\) の単調性。

----

<a id="Tomabechi.Consistency.C3.averagePresentation"></a>

## 定義 `averagePresentation`

### 式

$$
\text{段 }n\text{ の平均場提示（原子法則は中心の Dirac 測度）}
$$

### Lean のコメント（日本語訳）

> 段nにおける平均場提示。平均場核は原子に関して定数だが、supportLubと中心表象は共通束上の実際のn番目の値を取る。

### 定義の説明

段 \(n\) の**平均場の提示**です。段の原子の法則は、その段の中心にある Dirac 確率測度（一点に質量 1）です。平均場の核は原子に関して定数ですが、台の LUB（`supportLub`）と中心の表象は、共通の順序の上の実際の \(n\) 番目の値をとります。原子は \(n+1\)、最上位は \(\top\)、源の層は \(\{n+1\}\) です。

### 証明の概略

1. 原子の型・順序を `Atom` にとり、位相は離散、可測空間は最大にする。
2. 原子は \(p=n+1\)、測度は \(p\) の Dirac 測度、最上位は \(\top\)（\(\top\) は源の層に入らない）。
3. 平均場の核（二次の谷）を、積分したものが二次谷の臨場感場になるように定める。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_center"></a>

## 補題 `averagePresentation_center`

### 式

$$
\text{中心表象}(\mathrm{supportLub})=\mathrm{rep}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

提示の中心の表象は、\(\mathrm{rep}(n+1)\) です。

### 証明の概略

1. 定義の展開（`rfl` に近い）。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_integral"></a>

## 補題 `averagePresentation_integral`

### 式

$$
\int(\text{核})\,d\mu=-\tfrac12\bigl(x-\mathrm{rep}(n+1)\bigr)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平均場の核を測度で積分すると、中心 \(\mathrm{rep}(n+1)\) の二次の谷 \(-\tfrac12(x-\text{中心})^2\) になります。

### 証明の概略

1. 測度は Dirac 測度なので、積分は一点の値（`integral_dirac`）。
2. 核の値を代入して整理する。

----

<a id="Tomabechi.Consistency.C3.packageQuadraticStage"></a>

## 定義 `packageQuadraticStage`

### 式

$$
\text{二次谷を、積分表示つきの H-stage 入力に包み直す}
$$

### Lean のコメント（日本語訳）

> 二次の谷を、元の（厳密な部分準位つきの）H-stage の入力として包み直す。解析的なフィールドはそのまま写す。段の平均場は `averagePresentation n` の核の積分で、中心はその段の LUB の共通の順序表象である。

### 定義の説明

二次の谷を、**元の（厳密な部分準位つきの）H-stage の入力**に包み直します。解析的なフィールドはそのままコピーし、段の平均場は `averagePresentation n` の核の積分、中心はその段の LUB の共通の順序表象です。H-stage の「平均場の積分表示・中心と LUB の対応」を満たす入力になります。

### 証明の概略

1. 元の二次谷（`quadraticStage`）のフィールド（中心・半径・利得・曲率・背景・勾配など）をそのまま使う。
2. 平均場は提示の積分（`averagePresentation_integral`）、中心は LUB の表象（`averagePresentation_center`）として与える。
3. 残りの条件（C²、勾配表現、障壁、部分準位）は元の二次谷から。

----

<a id="Tomabechi.Consistency.C3.packageQuadraticStage_toStageValleySpec"></a>

## 補題 `packageQuadraticStage_toStageValleySpec`

### 式

$$
\text{包み直した入力}\mapsto\text{元の二次谷}
$$

### Lean のコメント（日本語訳）

> 包み直した入力は、作るときに使った二次の段にちょうど戻る。したがって、平均場の提示を加えても、その有効ポテンシャル・部分準位・凍結した力学は変わらない。

### 補題の説明

包み直した入力を元の「谷の仕様」に戻すと、作るときに使った二次谷にちょうど戻ります。したがって、平均場の提示を加えても、有効ポテンシャル・部分準位・凍結した力学は変わりません。

### 証明の概略

1. 両辺のフィールドを比べる（構造体の外延性）。

----

<a id="Tomabechi.Consistency.C3.packageQuadraticStage_uses_original_sublevel_barrier"></a>

## 補題 `packageQuadraticStage_uses_original_sublevel_barrier`

### 式

$$
\overline{\mathrm{sublevel}}\subseteq B(\mathrm{center},r)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

包み直した入力は、**元の部分準位の障壁**（部分準位集合の閉包が球の内部に入る）を使っています。緩和した条件ではありません。

### 証明の概略

1. 二次谷の部分準位は閉球 \(\bar B(c,d)\)、半径は \(d+1\)。

----

<a id="Tomabechi.Consistency.C3.centerGap"></a>

## 定義 `centerGap`

### 式

$$
\frac{1}{(n+2)(n+3)}
$$

### Lean のコメント（日本語訳）

> 隣り合う自然数層の間の、共通の記号での中心の間隔。

### 定義の説明

共通の記号での、隣り合う自然数層の中心の間隔です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.representation_center_gap"></a>

## 補題 `representation_center_gap`

### 式

$$
\mathrm{rep}(n+2)-\mathrm{rep}(n+1)=\frac1{(n+2)(n+3)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

隣り合う中心の差は、間隔 `centerGap` に等しい。

### 証明の概略

1. \(\tfrac{n+2}{n+3}-\tfrac{n+1}{n+2}=\tfrac1{(n+2)(n+3)}\)（通分して整理）。

----

<a id="Tomabechi.Consistency.C3.centerGap_pos"></a>

## 補題 `centerGap_pos`

### 式

$$
>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心の間隔は正です。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Consistency.C3.stageDuration"></a>

## 定義 `stageDuration`

### 式

$$
4(n+2)(n+3)
$$

### Lean のコメント（日本語訳）

> 多項式的に増える滞在時間は、縮んでいく層の間隔に伴う対数的な許容誤差に対して十分長い。

### 定義の説明

段 \(n\) の**滞在時間**です。多項式的に増え、層の間隔が縮むことに伴う対数的な許容誤差に対して十分長い時間です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.stageDuration_pos"></a>

## 補題 `stageDuration_pos`

### 式

$$
>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

滞在時間は正です。

### 証明の概略

1. `positivity`。

----

<a id="Tomabechi.Consistency.C3.gapThreshold"></a>

## 定義 `gapThreshold`

### 式

$$
\mathrm{gap}^2/4
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

間隔から決める閾値 \(\theta\)（間隔の二乗の 4 分の 1）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.errorTolerance"></a>

## 定義 `errorTolerance`

### 式

$$
\mathrm{gap}/4
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の終わりに許す誤差の許容値（間隔の 4 分の 1）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.errorTolerance_pos"></a>

## 補題 `errorTolerance_pos`

### 式

$$
>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容誤差は正です。

### 証明の概略

1. 間隔が正。

----

<a id="Tomabechi.Consistency.C3.stageTime"></a>

## 定義 `stageTime`

### 式

$$
\sum_{k<n}\mathrm{dur}(k)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段 \(n\) の開始時刻です。それまでの段の滞在時間の和です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.stageTime_recurrence"></a>

## 補題 `stageTime_recurrence`

### 式

$$
T_{n+1}=T_n+\mathrm{dur}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻は、前の開始時刻に滞在時間を足したものです。

### 証明の概略

1. 有限和の一項追加（`sum_range_succ`）。

----

<a id="Tomabechi.Consistency.C3.stageDuration_lower_bound"></a>

## 補題 `stageDuration_lower_bound`

### 式

$$
1\le\mathrm{dur}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

滞在時間は 1 以上です。

### 証明の概略

1. \(4(n+2)(n+3)\ge24\ge1\)（`nlinarith`）。

----

<a id="Tomabechi.Consistency.C3.stageTime_unbounded"></a>

## 補題 `stageTime_unbounded`

### 式

$$
\forall B\ \exists n,\ B<T_n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻は上に有界でありません（段の切り替えが無限に続く）。

### 証明の概略

1. \(n>B\) を取る。各段の滞在時間は 1 以上なので、\(T_n\ge n>B\)。

----

<a id="Tomabechi.Consistency.C3.layerU"></a>

## 定義 `layerU`

### 式

$$
U_n=n+1\in\mathrm{Atom}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段 \(n\) の「到達済みの層」です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.layerV"></a>

## 定義 `layerV`

### 式

$$
V_n=n+1\in\mathrm{Atom}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段 \(n\) の「新しい層」です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.layerU_update"></a>

## 補題 `layerU_update`

### 式

$$
U_{n+1}=U_n\sqcup V_{n+1}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達済みの層は、新しい層との結びで更新されます。

### 証明の概略

1. 両辺が \(n+2\)（`simp`）。

----

<a id="Tomabechi.Consistency.C3.layerU_below_top"></a>

## 補題 `layerU_below_top`

### 式

$$
U_n<\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達済みの層は、頂より真に下です。

### 証明の概略

1. 自然数は \(\top\) より小さい。

----

<a id="Tomabechi.Consistency.C3.layerV_new"></a>

## 補題 `layerV_new`

### 式

$$
\neg\,(V_{n+1}\le U_n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

新しい層は、到達済みの層には含まれません（本当に新しい）。

### 証明の概略

1. 含まれるとすると \(n+2\le n+1\)（矛盾、`omega`）。

----

<a id="Tomabechi.Consistency.C3.firstValley"></a>

## 定義 `firstValley`

### 式

$$
\text{最初の谷（中心}=\mathrm{rep}(1)\text{）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最初の段の二次の谷です。中心は \(\mathrm{rep}(1)\)、初期値・開始時刻は 0。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.nextValley"></a>

## 定義 `nextValley`

### 式

$$
\text{次の谷（中心}=\mathrm{rep}(n+2)\text{）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

次の段の二次の谷です。中心は \(\mathrm{rep}(n+2)\)、初期値・開始時刻は引数です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.valleySequence"></a>

## 定義 `valleySequence`

### 式

$$
\text{端点で整合する谷の列}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最初の谷と次の谷から、**端点で整合する**谷の列を作ります（次の段の初期値は、前の段の軌道の終端）。滞在時間と開始時刻は上で定義したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.valleySequence_shape"></a>

## 補題 `valleySequence_shape`

### 式

$$
\text{段 }n\text{ の谷は二次谷}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

谷の列の段 \(n\) は、中心 \(\mathrm{rep}(n+1)\) の二次の谷です。

### 証明の概略

1. \(n\) についての帰納法。0 は最初の谷、\(n+1\) は次の谷の定義。

----

<a id="Tomabechi.Consistency.C3.valleySequence_center"></a>

## 補題 `valleySequence_center`

### 式

$$
\text{center}_n=\mathrm{rep}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

谷の列の段 \(n\) の中心は \(\mathrm{rep}(n+1)\) です。

### 証明の概略

1. \(n\) についての帰納法。

----

<a id="Tomabechi.Consistency.C3.hStageSequence"></a>

## 定義 `hStageSequence`

### 式

$$
\text{各 LUB 層に一つの完全な元の H-stage}
$$

### Lean のコメント（日本語訳）

> LUB の各層に、完全な元の H-stage を一つずつ。移行は、端点で整合する谷の列から引き継ぎ、平均場・平均場の提示・順序の表象は、二次の谷のデータを変えずに付ける。

### 定義の説明

**LUB の各層に、完全な元の H-stage を一つずつ**対応させる列です。段の移行は、端点で整合する谷の列から引き継ぎ、平均場・平均場の提示・順序の表象は、二次の谷のデータを変えずに付けます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_toStageValleySpec"></a>

## 補題 `hStageSequence_toStageValleySpec`

### 式

$$
\text{H-stage 列}\to\text{谷の仕様}=\text{谷の列}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

H-stage の列を谷の仕様に戻すと、谷の列に一致します。

### 証明の概略

1. `packageQuadraticStage_toStageValleySpec` と `valleySequence_shape`。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_center"></a>

## 補題 `hStageSequence_center`

### 式

$$
\text{center}=\mathrm{rep}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

H-stage の段 \(n\) の中心は \(\mathrm{rep}(n+1)\) です。

### 証明の概略

1. 定義の展開（`rfl`）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_sublevel_barrier"></a>

## 補題 `hStageSequence_sublevel_barrier`

### 式

$$
\overline{\mathrm{sublevel}}\subseteq B(\mathrm{center},r)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段で、部分準位集合の閉包が球の内部に入ります（元の H-stage の障壁）。

### 証明の概略

1. `packageQuadraticStage_uses_original_sublevel_barrier`。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_start"></a>

## 補題 `hStageSequence_start`

### 式

$$
\text{startTime}_n=T_n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段 \(n\) の開始時刻は \(T_n\)（`stageTime`）です。

### 証明の概略

1. 端点で整合する列の開始時刻の補題（`endpointCompatibleStageSequence_startTime`）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_minimizer"></a>

## 補題 `hStageSequence_minimizer`

### 式

$$
\text{minimizer}_n=\mathrm{rep}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の谷の最小点は、中心 \(\mathrm{rep}(n+1)\) です。

### 証明の概略

1. 谷の仕様に戻し、二次谷の最小点の補題（`chooseQuadraticStage_minimizer`）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_transition"></a>

## 補題 `hStageSequence_transition`

### 式

$$
\text{initial}_{n+1}=\text{orbit}_n(T_n+\mathrm{dur}(n))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期値は、前の段の軌道の、滞在の終わりの値です（端点の整合）。

### 証明の概略

1. 谷の列の定義から（端点で整合する列）。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_sourceLayer"></a>

## 補題 `averagePresentation_sourceLayer`

### 式

$$
\text{sourceLayer}=\{n+1\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

提示の源の層は一点集合 \(\{n+1\}\) です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_measureSupport"></a>

## 補題 `averagePresentation_measureSupport`

### 式

$$
\text{measureSupport}=\{n+1\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

測度の台は一点集合 \(\{n+1\}\) です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_supportLub"></a>

## 補題 `averagePresentation_supportLub`

### 式

$$
\text{supportLub}=n+1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

台の LUB は \(n+1\) です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.averagePresentation_abstractTop"></a>

## 補題 `averagePresentation_abstractTop`

### 式

$$
\text{abstractTop}=\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

提示の抽象的な頂は \(\top\) です。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_atomType"></a>

## 補題 `hStageSequence_atomType`

### 式

$$
\text{H-stage の原子の型}=\mathrm{Atom}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

H-stage の列の原子の型は、`Atom` です（全段で共通）。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.branchContext"></a>

## 定義 `branchContext`

### 式

$$
\text{branch}=\text{symbolSupport}=\{n+1\}
$$

### Lean のコメント（日本語訳）

> 各段の枝と記号の台は、共通の抽象的な順序の中の、表象された一層だけの集合である。

### 定義の説明

各段の「枝」と「記号の台」は、共通の抽象的な順序の上の、一層だけの集合 \(\{n+1\}\) です（定理21の枝の文脈）。

### 証明の概略

1. 枝・記号の台は \(\{n+1\}\)。非空。\(\top\) は枝に入らない。台の LUB は台自身。

----

<a id="Tomabechi.Consistency.C3.inputMass"></a>

## 定義 `inputMass`

### 式

$$
\mu(g)=\tfrac12\ (g\in\{\text{false},\text{true}\})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二値のゴール \(g\) の質量です。各ゴールに \(1/2\) ずつ（一様）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.inputAction"></a>

## 定義 `inputAction`

### 式

$$
a(x,g)=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

行為（出力）は、ゴールをそのまま返します（恒等）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.inputMass_value"></a>

## 補題 `inputMass_value`

### 式

$$
\mu(g)=\tfrac12
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゴールの質量は \(1/2\) です。

### 証明の概略

1. 二値の測度の一点集合の値（`binaryGoalMeasure_singleton`）。

----

<a id="Tomabechi.Consistency.C3.inputMass_nonneg"></a>

## 補題 `inputMass_nonneg`

### 式

$$
\mu(g)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

質量は非負です。

### 証明の概略

1. \(1/2\ge0\)。

----

<a id="Tomabechi.Consistency.C3.inputMass_sum"></a>

## 補題 `inputMass_sum`

### 式

$$
\sum_g\mu(g)=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

質量の和は 1 です。

### 証明の概略

1. \(\tfrac12+\tfrac12=1\)。

----

<a id="Tomabechi.Consistency.C3.inputMass_measurable"></a>

## 補題 `inputMass_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

質量は入力について可測です。

### 証明の概略

1. 入力は一点なので、定数関数（`fun_prop`）。

----

<a id="Tomabechi.Consistency.C3.inputAction_measurable"></a>

## 補題 `inputAction_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

行為は入力について可測です。

### 証明の概略

1. 定数関数。

----

<a id="Tomabechi.Consistency.C3.inputAction_injective"></a>

## 補題 `inputAction_injective`

### 式

$$
\text{質量が正のゴールで行為が一致}\Rightarrow\text{ゴールが一致}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

行為はゴールの単射です（質量が正のゴールについて）。行為からゴールが復元できます。

### 証明の概略

1. 行為はゴールそのもの。

----

<a id="Tomabechi.Consistency.C3.inputEntropy_eq_log_two"></a>

## 補題 `inputEntropy_eq_log_two`

### 式

$$
H(G\mid X)=\log2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

条件付きゴールエントロピーは \(\log2\) です（一様な二値のゴール）。

### 証明の概略

1. 入力は Dirac 測度なので積分は一点の値。\(-\tfrac12\log\tfrac12\times2=\log2\)。

----

<a id="Tomabechi.Consistency.C3.inputEntropy_pos"></a>

## 補題 `inputEntropy_pos`

### 式

$$
H(G\mid X)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゴールのエントロピーは正です（情報が空虚でない）。

### 証明の概略

1. \(\log2>0\)。

----

<a id="Tomabechi.Consistency.C3.physicalMass"></a>

## 定義 `physicalMass`

### 式

$$
\mu(g)=\begin{cases}0&g=\text{true}\\1&g=\text{false}\end{cases}
$$

### Lean のコメント（日本語訳）

> 物理底層に割り当てる決定的ゴール法則。ここではBoolの一方だけに確率1を置くので、物理層の条件付きゴールエントロピーは厳密に0となる。

### 定義の説明

物理の底の層に割り当てる、**決定的なゴールの法則**です。`false` だけに確率 1 を置くので、物理層の条件付きゴールエントロピーは厳密に 0 になります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.physicalEntropy_eq_zero"></a>

## 補題 `physicalEntropy_eq_zero`

### 式

$$
H_{\mathrm{phys}}(G\mid X)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の条件付きゴールエントロピーは 0 です。

### 証明の概略

1. Dirac 測度の積分は一点の値。決定的な分布のエントロピーは 0。

----

<a id="Tomabechi.Consistency.C3.physicalLayerLaw"></a>

## 定義 `physicalLayerLaw`

### 式

$$
\text{ゴールも出力も決定的な法則}
$$

### Lean のコメント（日本語訳）

> 物理層の法則は、ゴールも出力も決定的である。その結合法則は、そのまま条件付き独立の参照法則なので、スコア 0 の有限な CMI の法則である。

### 定義の説明

物理層の法則です。**ゴールも出力も決定的**です。その結合法則は、そのまま条件付き独立の参照法則になっているので、スコア 0 の有限な条件付き相互情報量（CMI）の法則です。

### 証明の概略

1. 入力は Dirac 測度、ゴールの核・出力の核はともに定数核（`false` の Dirac）。
2. 確率測度・マルコフ核・可測性を確認する。

----

<a id="Tomabechi.Consistency.C3.physicalLayerLaw_goalMass_matches"></a>

## 補題 `physicalLayerLaw_goalMass_matches`

### 式

$$
\text{ゴールの質量}=\text{physicalMass}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の法則のゴールの質量は、`physicalMass` に一致します。

### 証明の概略

1. `false`・`true` の場合分けで計算する。

----

<a id="Tomabechi.Consistency.C3.physicalLayerLaw_joint_eq_reference"></a>

## 補題 `physicalLayerLaw_joint_eq_reference`

### 式

$$
\text{joint}=\text{reference}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の結合分布は、参照分布に等しい。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.physicalLayerFiniteLaw"></a>

## 定義 `physicalLayerFiniteLaw`

### 式

$$
\text{有限な CMI の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

物理層の法則を、有限な条件付き相互情報量の法則として束ねたものです（確率測度・マルコフ核の型クラスを整える）。

### 証明の概略

1. 物理層の法則に、確率測度・マルコフ核の証拠を与える。

----

<a id="Tomabechi.Consistency.C3.physicalLayerFiniteLaw_score_zero"></a>

## 補題 `physicalLayerFiniteLaw_score_zero`

### 式

$$
\mathrm{KL}(\text{joint}\,\|\,\text{ref})=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の KL ダイバージェンス（CMI のスコア）は 0 です。

### 証明の概略

1. joint \(=\) reference（前の補題）。自分自身との KL は 0（`klDiv_self`）。

----

<a id="Tomabechi.Consistency.C3.C3CMIPair"></a>

## 構造体 `C3CMIPair`

### 式

$$
(\text{joint},\ \text{reference})
$$

### Lean のコメント（日本語訳）

> 容量の例は、結合分布と参照分布の完全な組を保持するので、埋め込みを、結果の実数のスコアが等しいことだけでなく、法則が等しいことで監査できる。

### 定義の説明

容量の例は、結合分布と参照分布の**組全体**を保持します。これで、埋め込みを、結果の実数のスコアが等しいことだけでなく、法則そのものが等しいことで監査できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.physicalCMIPair"></a>

## 定義 `physicalCMIPair`

### 式

$$
(\text{物理層の joint},\ \text{物理層の reference})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

物理層の CMI の組です。

### 証明の概略

1. 物理層の法則の joint と、直接の CMI の参照分布（`directCMIReference`）を並べる。

----

<a id="Tomabechi.Consistency.C3.upperJoint"></a>

## 定義 `upperJoint`

### 式

$$
\text{上位層の joint（一様なゴールを、そのまま行為にする）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の結合分布です。一様なゴール（質量 \(1/2\)）を、そのまま行為に写す、ゴール・行為が生成する結合分布です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.upperJoint_isProbability"></a>

## 補題 `upperJoint_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の結合分布は確率測度です。

### 証明の概略

1. 質量が非負・和が 1・可測。生成する結合分布の確率測度性の補題を使う。

----

<a id="Tomabechi.Consistency.C3.upperCMIPair"></a>

## 定義 `upperCMIPair`

### 式

$$
(\text{上位層の joint},\ \text{上位層の reference})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の CMI の組です。

### 証明の概略

1. 上位層の joint と、その参照分布を並べる。

----

<a id="Tomabechi.Consistency.C3.cmiPairForProblem"></a>

## 定義 `cmiPairForProblem`

### 式

$$
q\mapsto\begin{cases}\text{上位の組}&q=\text{true}\\\text{物理の組}&q=\text{false}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

問題 \(q\)（真偽）に対応する CMI の組です。`true` が上位層の問題、`false` が物理層の問題。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.cmiPairScore"></a>

## 定義 `cmiPairScore`

### 式

$$
\mathrm{KL}(\text{joint}\,\|\,\text{reference})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

CMI の組のスコアです。結合分布の、参照分布に対する KL ダイバージェンス（実数に直したもの）で、条件付き相互情報量に当たります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.physicalCMIPair_score_zero"></a>

## 補題 `physicalCMIPair_score_zero`

### 式

$$
\text{score}(\text{物理})=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の組のスコアは 0 です。

### 証明の概略

1. 直接の CMI の KL は既存の CMI の KL に等しい（`directCMI_kl_eq_existing`）。物理層の有限な法則のスコアが 0。

----

<a id="Tomabechi.Consistency.C3.physicalCMIPair_kl_finite"></a>

## 補題 `physicalCMIPair_kl_finite`

### 式

$$
\mathrm{KL}<\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理層の KL は有限です（\(\infty\) でない）。

### 証明の概略

1. KL は 0（joint \(=\) reference）で、\(\infty\) ではない。

----

<a id="Tomabechi.Consistency.C3.physicalCMIPairFiniteLaw"></a>

## 定義 `physicalCMIPairFiniteLaw`

### 式

$$
\text{有限な KL の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

物理層の組を、有限な KL の法則として束ねたものです。

### 証明の概略

1. joint・reference・有限性を並べる。

----

<a id="Tomabechi.Consistency.C3.stageInformation"></a>

## 定義 `stageInformation`

### 式

$$
\text{定理21の四つの結論（直接の KL の CMI を含む）}
$$

### Lean のコメント（日本語訳）

> 直接の KL の CMI を含む、定理21の四つの結論は、すべて同じ平均場入力の原子の法則と、同じ上位層の情報法則を使う。

### 定義の説明

定理21の**四つの結論**（直接の KL による条件付き相互情報量を含む）が、**同じ平均場入力の原子の法則**と、**同じ上位層の情報法則**を使って成り立ちます。

### 証明の概略

1. 段 \(n\) の包み直した H-stage の入力に、定理21の一般入口 `meanField_stage_theorem21_four_conclusions_directKL` を適用する。
2. 枝の文脈・質量・行為・原子の列（\(n+1\) の定数列）・行為の可測性と、質量・行為の性質（非負・和 1・単射）を渡す。

----

<a id="Tomabechi.Consistency.C3.stageInformation_uses_hStageSequence"></a>

## 補題 `stageInformation_uses_hStageSequence`

### 式

$$
\text{包み直した入力}=\text{hStageSequence}\ n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理21の適用で使った平均場の入力は、H-stage の列の段 \(n\) そのものです。

### 証明の概略

1. 定義の展開（同じ式）。

----

<a id="Tomabechi.Consistency.C3.upperCMIPair_score_log_two"></a>

## 補題 `upperCMIPair_score_log_two`

### 式

$$
\text{score}(\text{上位})=\log2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の組のスコアは \(\log2\) です（ゴールの情報が完全に伝わる）。

### 証明の概略

1. `stageInformation 0` の最後の結論（情報の結論）を取り出す。
2. ゴール・行為が生成する結合分布の直接 CMI のスコアは、条件付きゴールエントロピーに等しい。それが \(\log2\)（`inputEntropy_eq_log_two`）。

----

<a id="Tomabechi.Consistency.C3.upperCMIPair_kl_finite"></a>

## 補題 `upperCMIPair_kl_finite`

### 式

$$
\mathrm{KL}<\infty
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上位層の KL は有限です。

### 証明の概略

1. \(\infty\) だとすると、スコア（実数に直した値）が 0 となり、\(\log2=0\) で矛盾。

----

<a id="Tomabechi.Consistency.C3.upperCMIPairFiniteLaw"></a>

## 定義 `upperCMIPairFiniteLaw`

### 式

$$
\text{有限な KL の法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の組を、有限な KL の法則として束ねたものです。

### 証明の概略

1. joint・reference・有限性を並べる。

----

<a id="Tomabechi.Consistency.C3.c3ProblemAdmissible"></a>

## 定義 `c3ProblemAdmissible`

### 式

$$
\text{許容問題}(a)=\begin{cases}\{\text{false}\}&a=0\\\text{全体}&a\ne0\end{cases}
$$

### Lean のコメント（日本語訳）

> 物理の問題は、順序のどの層でも成り立つ。別の上位の問題は、定理21の `μ/mass/action` が生成する結合・参照の組をそのまま持つ。その許容性だけが、物理の底より上で始まる。

### 定義の説明

物理の問題は、順序のどの層でも許容されます。別の上位の問題は、定理21の `μ/mass/action` が生成する結合・参照の組をそのまま持ち、**物理の底より上でだけ**許容されます。原子 \(0\)（底）では物理の問題（`false`）だけ、それ以外では二つの問題が許容されます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.c3Problem_false_admissible"></a>

## 補題 `c3Problem_false_admissible`

### 式

$$
\text{false}\in\text{許容問題}(a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

物理の問題（`false`）は、どの層でも許容されます。

### 証明の概略

1. 場合分け（`a = 0` かどうか）。

----

<a id="Tomabechi.Consistency.C3.c3CapacityScore"></a>

## 定義 `c3CapacityScore`

### 式

$$
\text{score}(a,q)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

原子 \(a\) の問題 \(q\) のスコアです（問題に対応する組のスコア）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.c3ProblemScores_bounded"></a>

## 補題 `c3ProblemScores_bounded`

### 式

$$
\{\text{score}\}\ \text{は上に有界}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

スコアの集合は上に有界です（上界 \(\log2\)）。

### 証明の概略

1. 物理は 0、上位は \(\log2\)。\(0\le\log2\)。

----

<a id="Tomabechi.Consistency.C3.c3LayerCapacity"></a>

## 定義 `c3LayerCapacity`

### 式

$$
\mathcal F(a)=\sup_{q\in\text{許容問題}(a)}\text{score}(a,q)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層 \(a\) の**容量**です（許容問題のスコアの上限）。定理19の容量 \(\mathcal F(\alpha)\) に当たります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.c3ProblemPair_preserved"></a>

## 補題 `c3ProblemPair_preserved`

### 式

$$
a\le b\Rightarrow\text{組は保存される}
$$

### Lean のコメント（日本語訳）

> 恒等の埋め込みは、各完全な CMI の組の二つの測度の両方を保つ。

### 補題の説明

恒等の埋め込みは、各 CMI の組の二つの測度の両方を保存します（層が上がっても、許容問題の組は変わらない）。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.c3ProblemJoint_preserved"></a>

## 補題 `c3ProblemJoint_preserved`

### 式

$$
\text{joint の保存}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

結合分布が保存されます。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.c3ProblemReference_preserved"></a>

## 補題 `c3ProblemReference_preserved`

### 式

$$
\text{reference の保存}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

参照分布が保存されます。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.C3.c3LayerCapacity_nondecreasing"></a>

## 補題 `c3LayerCapacity_nondecreasing`

### 式

$$
a\le b\Rightarrow\mathcal F(a)\le\mathcal F(b)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

容量は層の順序について**単調非減少**です（上の層ほど容量が大きい）。

### 証明の概略

1. 各層に許容問題（`false`）がある。スコアは上に有界。
2. 恒等の埋め込みが、スコアを保存することを使う（`dependentCapacity_nondecreasing_of_scorePreservingEmbedding`）。

----

<a id="Tomabechi.Consistency.C3.c3LayerCapacity_bottom_eq_zero"></a>

## 補題 `c3LayerCapacity_bottom_eq_zero`

### 式

$$
\mathcal F(\bot)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

底（物理層）の容量は 0 です。

### 証明の概略

1. 底の許容問題は `false` だけで、スコア 0。像が \(\{0\}\)、上限は 0。

----

<a id="Tomabechi.Consistency.C3.c3LayerCapacity_top_positive"></a>

## 補題 `c3LayerCapacity_top_positive`

### 式

$$
\mathcal F(\top)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂の容量は正です（\(\log2\) 以上）。

### 証明の概略

1. 頂で `true` は許容され、スコア \(\log2\)。上限はそれ以上（`le_csSup`）。\(\log2>0\)。

----

<a id="Tomabechi.Consistency.C3.layerU_monotone"></a>

## 補題 `layerU_monotone`

### 式

$$
n\le m\Rightarrow U_n\le U_m
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達済みの層は、段の順序について単調です。

### 証明の概略

1. 自然数のキャストの単調性。

----

<a id="Tomabechi.Consistency.C3.c3LayerCapacity_along_stages_monotone"></a>

## 補題 `c3LayerCapacity_along_stages_monotone`

### 式

$$
n\mapsto\mathcal F(U_n)\ \text{は単調}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段に沿った容量 \(\mathcal F(U_n)\) は、単調非減少です。

### 証明の概略

1. `layerU` の単調性と、容量の単調性の合成。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_initial_recurrence"></a>

## 補題 `hStageSequence_initial_recurrence`

### 式

$$
x^{\mathrm{init}}_{n+1}=c_n+\bigl(x^{\mathrm{init}}_n-c_n\bigr)\,e^{-\mathrm{dur}(n)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期値は、前の中心 \(c_n\) に向かって、滞在時間 \(\mathrm{dur}(n)\) だけ指数的に縮んだ値です。

### 証明の概略

1. 次の段の初期値は、前の段の軌道の終端（`hStageSequence_transition`）。
2. 二次谷の凍結した軌道は、中心への指数的な縮み（`quadraticFrozenOrbit_eq_witness_orbit`）。
3. 式を整理する。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_initial_between_centers"></a>

## 補題 `hStageSequence_initial_between_centers`

### 式

$$
0\le x^{\mathrm{init}}_n\le c_n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の初期値は、0 以上、その段の中心以下です。

### 証明の概略

1. \(n\) についての帰納法。0 は初期値 0。
2. \(n+1\) では、前の初期値が前の中心以下（かつ 0 以上）から、縮みの式で、次の中心の間に入る。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_amplitude_le_one"></a>

## 補題 `hStageSequence_amplitude_le_one`

### 式

$$
\text{decayAmplitude}\le1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の減衰の振幅は 1 以下です。

### 証明の概略

1. 谷の仕様と二次谷の減衰振幅の式（`quadraticStage_decayAmplitude`）で書き換える。
2. 中心 \(<1\) と初期値の評価から 1 以下。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_wait_bound"></a>

## 補題 `hStageSequence_wait_bound`

### 式

$$
\max\bigl(0,\tfrac1{\text{rate}}\log\tfrac{\text{amp}}{\text{tol}}\bigr)\le\mathrm{dur}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

必要な待ち時間（許容誤差まで縮むのに要る時間）は、滞在時間以下です。つまり、滞在時間が、各段の終わりで許容誤差まで縮むのに足ります。

### 証明の概略

1. 減衰率は 1。振幅は 1 以下（前の補題）。
2. 許容誤差 \(=\text{gap}/4\)、\(\log(4/\text{gap})\le\mathrm{dur}\) を、\(4(n+2)(n+3)\) との比較で示す。

----

<a id="Tomabechi.Consistency.C3.stageTheta"></a>

## 定義 `stageTheta`

### 式

$$
\theta_0=0,\ \theta_{k+1}=\mathrm{gap}_k^2/4
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の閾値 \(\theta\) です。段 0 は 0、段 \(k+1\) は間隔の二乗の 4 分の 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.stageTheta_nonneg"></a>

## 補題 `stageTheta_nonneg`

### 式

$$
\theta_n\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閾値は非負です。

### 証明の概略

1. 場合分け。0 か `positivity`。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_gap_threshold"></a>

## 補題 `hStageSequence_gap_threshold`

### 式

$$
\theta_{n+1}<\tfrac{(\ldots)}{2}\,\lVert x^*_{n+1}-x^*_n\rVert^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の閾値 \(\theta_{n+1}\) は、次の谷の最小点と前の最小点の距離の二乗に、曲率で決まる係数を掛けたものより小さいです（谷が十分に離れていること）。

### 証明の概略

1. 最小点は中心（`hStageSequence_minimizer`）で、隣の中心の差は `centerGap`。
2. 曲率・利得を代入して、閾値 \(=\text{gap}^2/4\) と比べる。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_segment_in_next_ball"></a>

## 補題 `hStageSequence_segment_in_next_ball`

### 式

$$
[x^*_n,x^*_{n+1}]\subseteq\bar B(c_{n+1},r_{n+1})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

前の最小点と次の最小点を結ぶ線分は、次の段の閉球に入ります。

### 証明の概略

1. 最小点は中心。中心は \(\mathrm{rep}\) で単調。線分の端が \(c_n\) と \(c_{n+1}\)。
2. 次の段の半径は \(d+1\)（初期値と中心の距離 \(+1\)）で、\(c_n\) までの距離はそれ以下。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_condition23B"></a>

## 定義 `hStageSequence_condition23B`

### 式

$$
\text{原文の条件 23-B の、緩和していない結論}
$$

### Lean のコメント（日本語訳）

> 同じ平均場の列が、21/22/23-B の切り替えの核が使う H-stage の仮定を供給する。核は、明示した共通の表象と滞在の予定に対して、元の（緩和していない）条件 23-B の結論を返す。

### 定義の説明

同じ平均場の列が、21・22・23-B の**切り替えの核**が使う H-stage の仮定を供給します。核は、明示した共通の表象と滞在の予定に対して、**元の（緩和していない）条件 23-B の結論**を返します。

### 証明の概略

1. 定理23の切り替えの核 `meanField_stage_specs_and_switches_give_condition23B_core` に、層の列・H-stage 列・表象・閾値・間隔・滞在時間・許容誤差と、これまでの補題（更新・単調・新しさ・中心・障壁・開始時刻・移行・待ち時間など）を渡す。

----

<a id="Tomabechi.Consistency.C3.hStageSequenceStageSpecs"></a>

## 定義 `hStageSequenceStageSpecs`

### 式

$$
\text{H-stage 列の谷の仕様}
$$

### Lean のコメント（日本語訳）

> 元のスカラーの 23-B の出力に名前をつけた形。完全な切り替えの証明書を、核の入れ子の連言を毎回開かずに、保存・確認できるようにする。

### 定義の説明

元のスカラーの 23-B の出力に名前をつけたもの（その 1）です。切り替えの完全な証明書を、核の入れ子の連言を毎回開かずに、保存・確認できるようにします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.hStageSequenceValleys"></a>

## 定義 `hStageSequenceValleys`

### 式

$$
\text{選んだ谷（最小点・軌道）の列}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の谷（最小点と凍結した軌道）を選んだ列です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.hStageSequenceTCZ"></a>

## 定義 `hStageSequenceTCZ`

### 式

$$
\text{段ごとの TCZ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の TCZ です。有効ポテンシャルが閾値 \(\theta_n\) 以下の、段の球の中の点の集合（中心まわり）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.hStageSequenceStitchedTrajectory"></a>

## 定義 `hStageSequenceStitchedTrajectory`

### 式

$$
\text{段を継ぎ合わせた軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の軌道を、滞在時間ごとに継ぎ合わせた**正準の軌道**です（全時間で定義）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.HStageSwitchingCertificate"></a>

## 構造体 `HStageSwitchingCertificate`

### 式

$$
\text{23-B の切り替えの完全な証明書}
$$

### Lean のコメント（日本語訳）

> 元の H-stage の列についての、完全な明示的な 23-B の出力。この証明書は、下流で使うすべての切り替えの結論を記録する。

### 定義の説明

元の H-stage の列についての、**23-B の完全な明示的な出力**です。下流で使う切り替えのすべての結論を記録します。内容は次のとおりです。(1) 層の進行：到達済みの層は頂より下で単調、狭義増加。開始時刻は上に有界でなく、狭義増加。(2) 隣り合う中心は異なる。(3) 隣り合う谷の最小点は異なる（距離が正）。(4) 各段の TCZ は閉集合で、空でなく、隣り合う TCZ は異なる。(5) 継ぎ合わせた軌道は、各滞在の間は谷の軌道に一致し、終端は最小点から許容誤差以内。(6) すべての有限時刻は、どれかの滞在の中にある。(7) どんな時刻・どんな段より後にも、切り替えがある。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C3.hStageSequence_switching_certificate"></a>

## 定理 `hStageSequence_switching_certificate`

### 式

$$
\mathrm{HStageSwitchingCertificate}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

H-stage の列が、23-B の切り替えの完全な証明書を満たします。

### 証明の概略

1. 切り替えの核の出力（`hStageSequence_condition23B`）の入れ子の連言を分解し、名前つきの形に直して、各フィールドに入れる（`simpa`）。

----

<a id="Tomabechi.Consistency.C3.c3_sharedWitness"></a>

## 定理 `c3_sharedWitness`

### 式

$$
\text{容量は単調}\ \wedge\ \mathcal F(\bot)=0\ \wedge\ \mathcal F(\top)>0
$$

### Lean のコメント（日本語訳）

> 法則を保つ単調な容量を、その物理の端点と正の端点とあわせて集めた、確認用の一つの証明書。`stageInformation` と `hStageSequence_condition23B` は、同じ列についての、別の段の証人である。

### 補題の説明

法則を保つ単調な容量と、その物理の端点（0）・正の端点（頂で正）を集めた、**一つの確認用の証明書**です。`stageInformation` と `hStageSequence_condition23B` は、同じ列についての、別の段の証人です。

### 証明の概略

1. `c3LayerCapacity_nondecreasing`・`c3LayerCapacity_bottom_eq_zero`・`c3LayerCapacity_top_positive` を並べる。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
