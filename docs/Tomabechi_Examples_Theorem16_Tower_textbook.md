# Tomabechi/Examples/Theorem16_Tower.lean 解説

> 対象: [`Tomabechi/Examples/Theorem16_Tower.lean`](../Tomabechi/Examples/Theorem16_Tower.lean)（定理16の Python 例（縮小性による一意性・幾何収束）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Tychonoff の定理 | コンパクト空間の（無限）積はコンパクト。 |
| Schauder–Tychonoff 不動点定理 | コンパクト凸集合上の連続な自己写像に固定点がある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理16の Python 例の、**縮小性による一意性・幾何収束**の節の Lean 根拠です。塔 \(K_n=[0,1]^{n+1}\)（射影は末尾の座標を落とす）、下三角のフィードバック
$$F_k(x)=(1-L)\,c_k+L\,\frac{x_k+x_{k-1}}{2}\quad(x_{-1}:=0,\ L=\tfrac7{10},\ c_k\in[0,1]\text{ は任意の有界列})$$
を扱います。

- **縮小・一意性・幾何収束（逆極限＝列空間）**：逆極限 \(\varprojlim[0,1]^{n+1}\) を、\([0,1]\) に値をもつ有界列の空間 `SeqSpace`（sup 距離で完備）として扱い、\(F\) が `SeqSpace` を保存し、**縮小率 \(7/10\) の縮小写像**であることを証明します。表象 \(M(S)=S_0\)（連続、\(\mathrm{Rep}=[0,1]\) はコンパクト Hausdorff）は同変 \(M\circ F=F_{\rm Rep}\circ M\)。一般定理 `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction` から、**一意な固定点 \(S^\ast\)** が存在し、\(F_{\rm Rep}(MS^\ast)=MS^\ast\)、\((MS^\ast,S^\ast)\in\mathfrak R\)、\(d(F^nS_0,S^\ast)\le(7/10)^n\,d(S_0,S^\ast)\) が成り立ちます。
- **層整合性**：各層 \(n\) の固定点方程式は先頭 \(n+1\) 本の方程式で、解は一意（帰納法）。したがって層ごとの固定点は互いに射影で一致します（Python の `consistency`）。

### 0.2 このファイルが証明していないこと

- 位相論的な存在節（Tychonoff + Schauder 型の逆極限定理）は、縮小性があれば Banach で代替できるため、この例では**縮小性の側の主張**を使います。原文の層条件（`theorem16_fixedPoint_exists_of_originalLayerConditions`）を塔で満たすことの証明は、別ファイル `Theorem16_TowerLayers.lean` です。
- 特殊な塔（下三角・線形）の例であり、一般の認知モデルの層別作用素ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理16の Python 例（`examples/theorem16_inverse_limit_fixed_point.py`）の Lean 根拠
>
> 塔 \(K_n=[0,1]^{n+1}\)（射影＝末尾の座標を落とす）、下三角のフィードバック \(F_k(x)=(1-L)c_k+L(x_k+x_{k-1})/2\)（\(x_{-1}:=0\)、\(L=7/10\)、\(c_k\in[0,1]\) は任意の有界列）。
>
> * **縮小と一意性・幾何収束（逆極限＝列空間）：** 逆極限を、\([0,1]\) に値をもつ有界列の空間 `SeqSpace`（sup 距離で完備）として扱い、\(F\) が `SeqSpace` を保存し縮小率 \(7/10\) の縮小写像であることを証明する。表象 \(M(S)=S_0\)（連続、\(\mathrm{Rep}=[0,1]\) はコンパクト Hausdorff）は同変 \(M\circ F=F_{\rm Rep}\circ M\)。一般定理 `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction` から、一意な固定点 \(S^\ast\) が存在し、\(F_{\rm Rep}(MS^\ast)=MS^\ast\)、\((MS^\ast,S^\ast)\in\mathfrak R\)、\(d(F^nS_0,S^\ast)\le(7/10)^nd(S_0,S^\ast)\)。
> * **層整合性：** 各層 \(n\) の固定点方程式は先頭 \(n+1\) 本の方程式であり、解は一意（帰納法）。したがって層ごとの固定点は互いに射影で一致する（Python の `consistency`）。
> * 位相論的な存在節（Tychonoff＋Schauder 型の逆極限定理）は、縮小性があれば Banach で代替できるため、この例では縮小性側の主張を使う。原文の層条件（`theorem16_fixedPoint_exists_of_originalLayerConditions`）を塔で満たすことの証明は別ファイル（対応表の「部分」）。

### 0.4 節見出しのコメント（日本語訳）

> ## 層整合性：下三角方程式の解は一意

名前空間は `Tomabechi.Examples.Theorem16Tower`。

---

<a id="Tomabechi.Examples.Theorem16Tower.prev"></a>

## 定義 `prev`

### 式

$$\mathrm{prev}(x,k)=\begin{cases}0&(k=0)\\x_{k-1}&(k\ge1)\end{cases}$$

### Lean のコメント（日本語訳）

> 前の座標 \(x_{k-1}\)（\(k=0\) では 0）。

### 定義の説明

下三角のフィードバックで使う「1 つ前の座標」です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16Tower.Fseq"></a>

## 定義 `Fseq`

### 式

$$F_k(x)=(1-L)c_k+L\,\frac{x_k+x_{k-1}}2,\quad L=\tfrac7{10}$$

### Lean のコメント（日本語訳）

> Python の `F`：\(F_k(x)=(1-L)c_k+L(x_k+x_{k-1})/2\)、\(L=7/10\)。

### 定義の説明

列 \(x\) に作用する下三角のフィードバック。\(k\) 番目の座標は、\(k\) 番目と \(k-1\) 番目の座標にしか依存しません。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16Tower.SeqSpace"></a>

## 定義 `SeqSpace`

### 式

$$\mathrm{SeqSpace}=\{x:\mathbb N\to_b\mathbb R\mid\forall k,\ x_k\in[0,1]\}$$

### Lean のコメント（日本語訳）

> \([0,1]\) に値をもつ有界列の空間（逆極限）。

### 定義の説明

逆極限を表す**列空間**。有界列の sup 距離を入れます。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16Tower.evalContinuous"></a>

## 定理 `evalContinuous`

### 式

$$f\mapsto f(k)\ \text{は連続（1-Lipschitz）}$$

### Lean のコメント（日本語訳）

> 評価 \(f\mapsto f(k)\) は連続（1-リプシッツ）。

### 補題の説明

有界列の座標の評価は、sup 距離について 1-Lipschitz なので連続です。

### 証明の概略

1. `BoundedContinuousFunction.dist_coe_le_dist`（座標の距離は sup 距離以下）で Lipschitz。

----

<a id="Tomabechi.Examples.Theorem16Tower.instance@L43"></a>

## インスタンス `instance@L43`

### 式

$$\mathrm{SeqSpace}\ \text{は完備}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

列空間 `SeqSpace` が**完備距離空間**であること。Banach の不動点定理に必要です。

### 証明の概略

1. 有界連続関数の空間は完備。部分集合 \(\{\forall k,\ x_k\in[0,1]\}\) は閉集合（各座標の評価が連続）なので、閉部分集合も完備。

----

<a id="Tomabechi.Examples.Theorem16Tower.instance@L52"></a>

## インスタンス `instance@L52`

### 式

$$\mathrm{SeqSpace}\ne\emptyset$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

列空間が空でないこと（零列を取る）。

### 証明の概略

1. \(0\in[0,1]\)。

----

<a id="Tomabechi.Examples.Theorem16Tower.M"></a>

## 定義 `M`

### 式

$$M(S)=S_0\in[0,1]$$

### Lean のコメント（日本語訳）

> 表象 \(M(S)=S_0\)（\(\mathrm{Rep}=[0,1]\)）。

### 定義の説明

主体の状態（列）から、その第 0 座標を取り出す表象。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16Tower.M_continuous"></a>

## 定理 `M_continuous`

### 式

$$M\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

表象が連続であること（`evalContinuous` から）。

### 証明の概略

1. `evalContinuous 0` と部分型の連続性。

----

<a id="Tomabechi.Examples.Theorem16Tower.selfRep"></a>

## 定義 `selfRep`

### 式

$$\mathrm{SelfRepresentation}(\mathrm{SeqSpace},[0,1])\ \text{with relation}=\mathrm{graph}(M)$$

### Lean のコメント（日本語訳）

> 自己表象データ（関係は \(M\) のグラフ）。

### 定義の説明

`Theorem16_25_Core` の `SelfRepresentation` を、\(M\) のグラフを関係として構成したもの。

### 証明の概略

1. 関係の閉性は `isClosed_eq`、表象の連続性は `M_continuous`、`represents` は `rfl`。

----

<a id="Tomabechi.Examples.Theorem16Tower.Fseq_mem"></a>

## 定理 `Fseq_mem`

### 式

$$x\in\mathrm{SeqSpace}\Rightarrow F_k(x)\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

フィードバックが `SeqSpace` を保存する（値が \([0,1]\) に入る）。

### 証明の概略

1. \(F_k=(1-L)c_k+L\frac{x_k+x_{k-1}}2\) は \(c_k,x_k,x_{k-1}\in[0,1]\) の凸結合なので \([0,1]\) に入る（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem16Tower.F"></a>

## 定義 `F`

### 式

$$F:\mathrm{SeqSpace}\to\mathrm{SeqSpace}$$

### Lean のコメント（日本語訳）

> \(F\) を `SeqSpace` 上の写像として実現（`mkOfDiscrete` で有界列にする）。

### 定義の説明

`Fseq` を、有界列の空間の写像として実現したもの。値が \([0,1]\) に入るので有界で、離散位相上の関数は自動的に連続です。

### 証明の概略

1. `BoundedContinuousFunction.mkOfDiscrete` で `Fseq` を有界列にする。有界性は値が \([0,1]\) に入ることから。

----

<a id="Tomabechi.Examples.Theorem16Tower.F_apply"></a>

## 定理 `F_apply`

### 式

$$(F x)_k=F_k(x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`F` の第 \(k\) 座標が `Fseq` に一致すること。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Examples.Theorem16Tower.F_contracting"></a>

## 定理 `F_contracting`

### 式

$$\mathrm{ContractingWith}\ \tfrac7{10}\ F$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**縮小率 \(7/10\) の縮小写像**：\(d(Fx,Fy)\le\frac7{10}d(x,y)\)（sup 距離）。

### 証明の概略

1. 各座標で \(|F_k(x)-F_k(y)|=\frac7{20}\bigl|(x_k-y_k)+(x_{k-1}-y_{k-1})\bigr|\)。
2. 三角不等式と \(|x_k-y_k|,\ |x_{k-1}-y_{k-1}|\le d(x,y)\) で \(\le\frac7{10}d(x,y)\)。
3. 座標ごとの評価から sup 距離の評価（`BoundedContinuousFunction.dist_le`）。

----

<a id="Tomabechi.Examples.Theorem16Tower.FRep"></a>

## 定義 `FRep`

### 式

$$F_{\rm Rep}(r)=(1-L)c_0+\frac{L\,r}2$$

### Lean のコメント（日本語訳）

> 表象の空間でのフィードバック \(F_{\rm Rep}(r)=(1-L)c_0+Lr/2\)。

### 定義の説明

表象空間 \([0,1]\) 上のフィードバック（第 0 座標の式）。

### 証明の概略

1. 定義のみ（値が \([0,1]\) に入ることを `nlinarith` で確認）。

----

<a id="Tomabechi.Examples.Theorem16Tower.FRep_continuous"></a>

## 定理 `FRep_continuous`

### 式

$$F_{\rm Rep}\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アフィン写像なので連続。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem16Tower.equivariant"></a>

## 定理 `equivariant`

### 式

$$M\circ F=F_{\rm Rep}\circ M$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**同変性**：表象写像がフィードバックと可換。\(F_0(x)=(1-L)c_0+L\frac{x_0+0}2\)（\(\mathrm{prev}=0\)）だからです。

### 証明の概略

1. `Subtype.ext` と、`F_apply`・`Fseq`・`prev` の展開（\(k=0\) で `prev` は 0）。

----

<a id="Tomabechi.Examples.Theorem16Tower.theorem16_tower"></a>

## 定理 `theorem16_tower`

### 式

$$\exists!\,s,\ F(s)=s\ \wedge\ F_{\rm Rep}(Ms)=Ms\ \wedge\ (Ms,s)\in\mathfrak R\ \wedge\ \forall x,n,\ d(F^nx,s)\le(\tfrac7{10})^nd(x,s)$$

### Lean のコメント（日本語訳）

> 定理16（縮小条件節）：一意な固定点 \(S^\ast\)、同変表象の固定点、幾何収束。

### 補題の説明

**塔での定理16**（縮小条件の節）：一意な固定点の存在、表象の固定点、幾何収束。

### 証明の概略

1. 一般定理 `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction`（Core）を、`FRep_continuous`・`equivariant`・`F_contracting`、および Banach 固定点の存在（`ContractingWith.fixedPoint`）で適用。

----

<a id="Tomabechi.Examples.Theorem16Tower.LayerEq"></a>

## 定義 `LayerEq`

### 式

$$\forall k\le n,\ y_k=F_k(y)$$

### Lean のコメント（日本語訳）

> 層 \(n\) の固定点方程式（先頭 \(n+1\) 本）。

### 定義の説明

層 \(n\) の方程式（\(k\le n\) の座標だけ）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16Tower.layer_unique"></a>

## 定理 `layer_unique`

### 式

$$y,z\ \text{が層 }n\text{ の解}\Rightarrow\forall k\le n,\ y_k=z_k$$

### Lean のコメント（日本語訳）

> 層 \(n\) の固定点は、先頭 \(n+1\) 座標で一意。

### 補題の説明

**層ごとの固定点の一意性**（下三角なので、第 0 座標から順に決まる）。

### 証明の概略

1. \(k\) についての帰納法。
2. \(k=0\)：\(y_0=(1-L)c_0+\frac{L}2y_0\) から \(y_0\) が決まる。
3. \(k\to k+1\)：\(y_{k+1}=(1-L)c_{k+1}+\frac L2(y_{k+1}+y_k)\) で \(y_k\) が既知なら \(y_{k+1}\) が決まる。

----

<a id="Tomabechi.Examples.Theorem16Tower.layerEq_mono"></a>

## 定理 `layerEq_mono`

### 式

$$n\le m,\ y\ \text{が層 }m\text{ の解}\Rightarrow y\ \text{は層 }n\text{ の解}$$

### Lean のコメント（日本語訳）

> 一般の \(n\le m\) で、層 \(m\) の解を層 \(n\) へ制限すると、層 \(n\) の解（射影の整合性）。

### 補題の説明

**射影整合性**：上の層の解は、下の層の解でもある。

### 証明の概略

1. \(k\le n\le m\) なので `hy k (hk.trans h)`。

----

<a id="Tomabechi.Examples.Theorem16Tower.fixedPoint_satisfies_all_layers"></a>

## 定理 `fixedPoint_satisfies_all_layers`

### 式

$$F(s)=s\Rightarrow\forall n,\ \mathrm{LayerEq}(n,s)$$

### Lean のコメント（日本語訳）

> 固定点 \(S^\ast\) は、全層の方程式を満たし、各層の（一意な）固定点に一致する。

### 補題の説明

塔全体の固定点が、**各層の固定点でもある**（Python の `consistency`）。

### 証明の概略

1. \(F(s)=s\) から各座標 \(s_k=F_k(s)\)。特に \(k\le n\) で成り立つ。

----


## コメント修正記録

（なし）
