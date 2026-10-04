# Tomabechi/Examples/Theorem16_TowerLayers.lean 解説

> 対象: [`Tomabechi/Examples/Theorem16_TowerLayers.lean`](../Tomabechi/Examples/Theorem16_TowerLayers.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Tychonoff の定理 | コンパクト空間の（無限）積はコンパクト。 |
| Schauder–Tychonoff 不動点定理 | コンパクト凸集合上の連続な自己写像に固定点がある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem16_Tower.lean` の補完です。同じ塔を、**定理16の原文の層条件**に適用し、さらに**原文の逆極限空間の固定点と、sup 距離の列空間の固定点が同じものだ**ことを示します。

- 塔 \(I=\mathbb N\)、層空間 \(E_n=\mathbb R^{n+1}\)、候補集合 \(K_n=[0,1]^{n+1}\)（非空・コンパクト・凸）、射影 \(p_{\beta\alpha}\)＝先頭 \(\beta+1\) 座標への制限（連続アフィン、\(p_{\alpha\alpha}=\mathrm{id}\)、\(p_{\gamma\beta}\circ p_{\beta\alpha}=p_{\gamma\alpha}\)）。
- 層別フィードバック \(f_n(x)_k=(1-L)c_k+L\,(x_k+x_{k-1})/2\)（\(L=7/10\)、\(c_k\in[0,1]\) は任意、\(x_{-1}:=0\)）。射影と可換で連続。

このファイルは次の 3 つを与えます。

1. **存在**（Tychonoff＋Schauder 型の存在節）：一般定理 `theorem16_fixedPoint_exists_of_originalLayerConditions` の全前提を満たし、逆極限（積空間の部分集合）の上に固定点が存在する（`tower_fixedPoint_exists`）。
2. **座標の同定**：逆極限の要素 \(x=(x_n)_n\)（各 \(x_n\in\mathbb R^{n+1}\) で射影整合）の「各層の最後の座標」を並べた列 `flatten x` を取ると、\(x_n\) の \(k\) 番目の座標は `flatten x` の第 \(k\) 項に一致する。逆向き `fromSeqSpace` もあり、`SeqSpace`（\([0,1]\) 値の有界列、sup 距離）との**型の同値** `inverseLimitSeqEquiv` が得られる。フィードバックと固定点もこの対応で保たれる。
3. **一意性と同一性**：`SeqSpace` 側の縮小写像（縮小率 \(7/10\)）の固定点の一意性を借りて、逆極限側の固定点が**ただ一つ**（`tower_fixedPoint_exists_unique`）で、それを `flatten` した列が `SeqSpace` 側の唯一の固定点そのものである（`tower_fixedPoint_has_same_coordinates`）ことを示す。

つまり、積位相の逆極限（存在節の舞台）と sup 距離の列空間（縮小節の舞台）という**別々の空間で証明された 2 つの固定点が同一**であることの Lean 証明です。

### 0.2 このファイルが証明していないこと

- 特殊な塔（下三角・線形）についての結果で、一般の認知モデルの層別作用素ではありません。
- `inverseLimitSeqEquiv` は**型の同値**（座標の対応）であって、位相同型（距離や位相の一致）ではありません。逆極限の位相は積位相、`SeqSpace` は sup 距離で、これらは一致しません。
- 幾何収束（反復の指数収束）の証明は `Theorem16_Tower.lean` にあり、このファイルでは逆極限側の反復については扱いません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理16の Python 例の「原文の層条件」への適用（`Theorem16_Tower.lean` の補完）
>
> 塔 \(I=\mathbb N\)、層空間 \(E_n=\mathbb R^{n+1}\)（Pi 型）、候補集合 \(K_n=[0,1]^{n+1}\)（非空コンパクト凸）、射影 \(p_{\beta\alpha}\)＝先頭 \(\beta+1\) 座標への制限（連続アフィン、\(p_{\alpha\alpha}=\mathrm{id}\)、\(p_{\gamma\beta}\circ p_{\beta\alpha}=p_{\gamma\alpha}\)）、層別フィードバック \(f_n(x)_k=(1-L)c_k+L(x_k+x_{k-1})/2\)（\(L=7/10\)、\(c_k\in[0,1]\) 任意、\(x_{-1}:=0\)、射影と可換・連続）。一般定理 `theorem16_fixedPoint_exists_of_originalLayerConditions` の全前提（有限層整合性は上界層から導出）を満たし、逆極限（積空間の部分集合）上に固定点が存在する（Tychonoff + Schauder 型の存在節）。幾何収束は `Theorem16_Tower.lean`（縮小性）。このファイルの後半では、逆極限の要素の各層の最後の座標を並べた列（`flatten`）で逆極限と `SeqSpace` を型として同一視し（位相同型ではない）、フィードバックと固定点がこの対応で保たれること、逆極限側の固定点が一意で `SeqSpace` 側の唯一の固定点と座標列として一致することを示す。

### 0.4 節見出しのコメント（日本語訳）

> 逆極限と有界列の座標同定：逆極限の層 \(n\) の最後の座標を列の第 \(n\) 項と読む。射影整合性により、層 \(n\) の他の座標もこの列の対応する項に一致する。この同定は位相同型を主張するものではなく、固定点の座標列を比較するための代数的な対応である。

名前空間は `Tomabechi.Examples.Theorem16TowerLayers`（`open Tomabechi.Theorem16_25`、`Tomabechi.Examples.Theorem16Tower`、`BoundedContinuousFunction`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.E"></a>

## 定義 `E`

### 式

$$E_n=\mathbb R^{n+1}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層 \(n\) の空間（\(n+1\) 個の実数の組）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.K"></a>

## 定義 `K`

### 式

$$K_n=[0,1]^{n+1}$$

### Lean のコメント（日本語訳）

> 層 \(n\) の候補集合を \(K_n=[0,1]^{n+1}\) とする。

### 定義の説明

層 \(n\) の候補集合：単位立方体。非空・コンパクト・凸です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.proj"></a>

## 定義 `proj`

### 式

$$p_{\beta\alpha}(x)=(x_0,\dots,x_\beta)$$

### Lean のコメント（日本語訳）

> 射影（先頭 \(\beta+1\) 座標）。

### 定義の説明

上の層 \(\alpha\) から下の層 \(\beta\) へ、先頭の座標だけを残す射影。

### 証明の概略

1. 定義のみ（`Fin.castLE`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.proj_refl"></a>

## 補題 `proj_refl`

### 式

$$p_{nn}=\mathrm{id}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同じ層への射影は恒等。

### 証明の概略

1. `funext` と `Fin.castLE` の自明な性質。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.proj_comp"></a>

## 補題 `proj_comp`

### 式

$$p_{\gamma\beta}\circ p_{\beta\alpha}=p_{\gamma\alpha}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影の合成が射影になる（推移性）。

### 証明の概略

1. `funext` と座標の計算。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.proj_maps"></a>

## 補題 `proj_maps`

### 式

$$p_{\beta\alpha}(K_\alpha)\subset K_\beta$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

射影が候補集合を保つ。

### 証明の概略

1. 座標は \([0,1]\) の値のまま。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.prevF"></a>

## 定義 `prevF`

### 式

$$\mathrm{prev}(x,k)=x_{k-1}\ (k\ge1),\ 0\ (k=0)$$

### Lean のコメント（日本語訳）

> 前の座標 \(x_{k-1}\)（\(k=0\) では 0）。

### 定義の説明

`Fin (n+1)` 上の「前の座標」。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.boundedC"></a>

## 定義 `boundedC`

### 式

$$c\ \text{を有界連続関数 }(\mathbb N\to_b\mathbb R)\text{ として読む}$$

### Lean のコメント（日本語訳）

> 同じ係数列を有界連続関数空間にも載せる。\(\mathbb N\) は離散なので連続性は自動である。

### 定義の説明

係数列 \(c_k\in[0,1]\) を、有界連続関数 \(\mathbb N\to\mathbb R\) の元として包み直したもの。`Theorem16_Tower.lean` の列空間側の写像 `F` はこの形の係数を受け取ります。\(\mathbb N\) は離散位相なので、任意の関数は連続、\([0,1]\) に値をとるので有界（定数 1）です。

### 証明の概略

定義のみ（`BoundedContinuousFunction.mkOfDiscrete`）。有界性の証明は、任意の 2 値の距離が 1 以下（両者が \([0,1]\) の元）であることから。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.boundedC_mem"></a>

## 補題 `boundedC_mem`

### 式

$$(\texttt{boundedC}\ c)(k)\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

包み直しても各項は元の \(c_k\) のままで、\([0,1]\) に入ります。

### 証明の概略

1. `boundedC` の定義を展開して `hc k`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.Fn"></a>

## 定義 `Fn`

### 式

$$f_n(x)_k=(1-L)c_k+L\,\frac{x_k+\mathrm{prev}(x,k)}2$$

### Lean のコメント（日本語訳）

> 層 \(n\) のフィードバック。

### 定義の説明

層ごとの下三角フィードバック。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.Fn_mem"></a>

## 補題 `Fn_mem`

### 式

$$x\in K_n\Rightarrow f_n(x)\in K_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

フィードバックが候補集合を保つ（凸結合なので値が \([0,1]\)）。

### 証明の概略

1. 各座標が \(c_k,x_k,\mathrm{prev}\in[0,1]\) の凸結合（`nlinarith`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.f"></a>

## 定義 `f`

### 式

$$f_n:K_n\to K_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`Fn` を候補集合（部分型）上の自己写像として実現したもの。

### 証明の概略

1. 定義のみ（`Fn_mem` で値の所属を与える）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.prevF_proj"></a>

## 補題 `prevF_proj`

### 式

$$\mathrm{prev}(x,\iota k)=\mathrm{prev}(p\,x,k)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

「前の座標」が射影と可換であること（層整合性の部品）。

### 証明の概略

1. \(k=0\) か \(k\ge1\) かで場合分けして座標を比べる。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.Fn_proj"></a>

## 補題 `Fn_proj`

### 式

$$p_{\beta\alpha}\circ f_\alpha=f_\beta\circ p_{\beta\alpha}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**フィードバックと射影の可換性**：定理16の層条件の 1 つです。

### 証明の概略

1. 各座標で `prevF_proj` を使って式が一致することを示す。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.continuous_prevF"></a>

## 補題 `continuous_prevF`

### 式

$$x\mapsto\mathrm{prev}(x,k)\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

「前の座標」の連続性。

### 証明の概略

1. `k=0` なら定数、そうでなければ座標の射影。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.continuous_Fn"></a>

## 補題 `continuous_Fn`

### 式

$$f_n\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

フィードバックの連続性。

### 証明の概略

1. 各座標が連続関数の線形結合（`fun_prop`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.continuous_f"></a>

## 補題 `continuous_f`

### 式

$$f_n|_{K_n}\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

部分型上でも連続。

### 証明の概略

1. `Continuous.subtype_mk`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.tower_fixedPoint_exists"></a>

## 補題 `tower_fixedPoint_exists`

### 式

$$\exists x\in\varprojlim,\ \tilde f(x)=x$$

### Lean のコメント（日本語訳）

> 原文の層条件を満たす塔の上で、逆極限に固定点が存在する。

### 補題の説明

**定理16の存在節**：塔の逆極限（積空間の部分集合）に、フィードバックから誘導される写像の固定点が存在する。

### 証明の概略

1. `theorem16_fixedPoint_exists_of_originalLayerConditions`（Core）の前提（非空・コンパクト・凸、射影のアフィン性・恒等・合成・連続性・候補集合を保つこと、フィードバックの連続性・可換性）を上の補題で満たして適用。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.flatten"></a>

## 定義 `flatten`

### 式

$$\mathrm{flatten}(x)_n=x_n(\text{最後の座標})\in\mathbb R$$

### Lean のコメント（日本語訳）

> 逆極限要素から、各層の最後の座標を読む列。

### 定義の説明

逆極限の要素 \(x=(x_n)_n\) は、各層 \(n\) の点 \(x_n\in\mathbb R^{n+1}\) の列です。各 \(x_n\) の**最後の座標**（第 \(n\) 番目）を取り出して並べると、実数列が 1 本できます。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.layer_coord_eq_flatten"></a>

## 補題 `layer_coord_eq_flatten`

### 式

$$x_n(k)=\mathrm{flatten}(x)_k\qquad(k\le n)$$

### Lean のコメント（日本語訳）

> 射影整合性により、層 \(n\) の各座標は flatten の同じ番号の項である。

### 補題の説明

層 \(n\) の \(k\) 番目の座標は、層 \(k\) の最後の座標と一致する。これは**射影整合性**（層 \(n\) の点を層 \(k\) へ射影すると層 \(k\) の点になる）の言い換えで、逆極限の要素が結局 1 本の列で決まることを意味します。

### 証明の概略

1. 整合性 \(p_{kn}(x_n)=x_k\) を、最後の座標 \(k\) で評価する。
2. `proj` が先頭座標への制限なので、\(x_n\) の第 \(k\) 座標＝\(x_k\) の最後の座標。`Fin.castLE` の同一視を示す。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.flatten_mem_Icc"></a>

## 補題 `flatten_mem_Icc`

### 式

$$\mathrm{flatten}(x)_n\in[0,1]$$

### Lean のコメント（日本語訳）

> 逆極限要素の flatten は、すべての座標が単位区間に入る。

### 補題の説明

逆極限の要素は各層で候補集合 \(K_n=[0,1]^{n+1}\) に入っているので、列も \([0,1]\) 値です。

### 証明の概略

1. 逆極限の定義から \(x_n\in K_n\)。最後の座標は \([0,1]\) の元。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.toSeqSpace"></a>

## 定義 `toSeqSpace`

### 式

$$x\longmapsto(\mathrm{flatten}(x)_n)_n\in\mathrm{SeqSpace}$$

### Lean のコメント（日本語訳）

> 逆極限要素を、有界連続関数空間上の \([0,1]\) 値列へ持ち上げる。

### 定義の説明

`flatten` した列を、`SeqSpace`（\([0,1]\) 値の有界列、sup 距離）の元として扱えるようにしたもの。

### 証明の概略

定義のみ（`mkOfDiscrete` と `flatten_mem_Icc`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.toSeqSpace_apply"></a>

## 補題 `toSeqSpace_apply`

### 式

$$(\texttt{toSeqSpace}\ x)_n=\mathrm{flatten}(x)_n$$

### Lean のコメント（日本語訳）

> `toSeqSpace` は座標を変えずに保存する。

### 補題の説明

包み直しただけで値は同じ。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.flatten_fixedPoint"></a>

## 補題 `flatten_fixedPoint`

### 式

$$x=\Phi(x)\ \Rightarrow\ \forall k:\ \mathrm{flatten}(x)_k=F_{\mathrm{seq}}(\mathrm{flatten}(x))_k$$

### Lean のコメント（日本語訳）

> 逆極限上の固定点は flatten 後も同じ下三角固定点方程式を満たす。

### 補題の説明

逆極限側の固定点（\(\Phi\) は各層のフィードバックから誘導された写像）の座標列は、`Theorem16_Tower.lean` の列空間側の固定点方程式 \(s_k=(1-L)c_k+L(s_k+s_{k-1})/2\) を満たします。

### 証明の概略

1. 固定点の仮定の第 \(k\) 層・最後の座標 \(j\) を取る。
2. \(k=0\) では前座標が 0（`prevF`）の場合を別に扱う。\(k\ge1\) では、`layer_coord_eq_flatten` で \(x_k(j)=\mathrm{flatten}(x)_k\) と前座標 \(x_k(k-1)=\mathrm{flatten}(x)_{k-1}\) に置き換える。
3. `Fn`・`Fseq` の定義を展開して一致させる。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.fromSeqSpace"></a>

## 定義 `fromSeqSpace`

### 式

$$s\longmapsto\bigl(x_n=(s_0,\dots,s_n)\bigr)_n$$

### Lean のコメント（日本語訳）

> 有界列から各層への有限制限を作る逆向きの写像。

### 定義の説明

列 \(s\) から、層 \(n\) の点を \((s_0,\dots,s_n)\)（先頭 \(n+1\) 項）として作ります。射影整合性（先頭座標への制限と合う）と \([0,1]\) への所属は自明に成り立つので、逆極限の要素になります。

### 証明の概略

1. 層 \(n\) の \(i\) 番目の座標を \(s_i\) と定義。
2. 所属：各座標 \(s_i\in[0,1]\)（`s.2 i`）。整合性：`simp [proj]`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.flatten_fromSeqSpace"></a>

## 補題 `flatten_fromSeqSpace`

### 式

$$\mathrm{flatten}(\texttt{fromSeqSpace}\ s)_n=s_n$$

### Lean のコメント（日本語訳）

> flatten と有限制限は座標ごとに互いに逆である。

### 補題の説明

列→層の点→列、で元に戻る（片側の逆）。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.layer_fromSeqSpace"></a>

## 補題 `layer_fromSeqSpace`

### 式

$$(\texttt{fromSeqSpace}\ s)_n(i)=s_i$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`fromSeqSpace` の層 \(n\) の座標は列の対応項。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.fromSeqSpace_flatten"></a>

## 補題 `fromSeqSpace_flatten`

### 式

$$\texttt{fromSeqSpace}(\texttt{toSeqSpace}\ x)=x$$

### Lean のコメント（日本語訳）

> 射影整合列の全ての層座標は flatten で復元されるので、逆写像も座標ごとに一致する。

### 補題の説明

逆極限の要素 \(x\) → 列 → 層の点、で元の \(x\) に戻る（もう片側の逆）。`layer_coord_eq_flatten` がまさにこの内容です。

### 証明の概略

1. 要素の等しさを層・座標ごとに示す（`Subtype.ext`、`funext`）。
2. `layer_coord_eq_flatten` で \(x_n(i)=\mathrm{flatten}(x)_i\)。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.fromSeqSpace_fixedPoint"></a>

## 補題 `fromSeqSpace_fixedPoint`

### 式

$$F(s)=s\ \Rightarrow\ \Phi(\texttt{fromSeqSpace}\ s)=\texttt{fromSeqSpace}\ s$$

### Lean のコメント（日本語訳）

> 列空間の固定点を各有限層へ制限すると、逆極限上の固定点になる。

### 補題の説明

`SeqSpace` 側の固定点を層ごとに切り出すと、逆極限側の固定点になります（逆向き）。

### 証明の概略

1. 層 \(n\)・座標 \(i\) ごとに等しさを示す。固定点の仮定 \(F(s)=s\) の第 \(i\) 座標を取り、`Fn`・`prevF`・`Fseq` の定義を展開して `simpa` で一致させる。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.toSeqSpace_fromSeqSpace"></a>

## 補題 `toSeqSpace_fromSeqSpace`

### 式

$$\texttt{toSeqSpace}(\texttt{fromSeqSpace}\ s)=s$$

### Lean のコメント（日本語訳）

> 有界列へ写してから有限制限を取ると、元の列に戻る。

### 補題の説明

`flatten_fromSeqSpace` を `SeqSpace` の元の等式にしたもの。

### 証明の概略

1. `Subtype.ext` と `BoundedContinuousFunction.ext` で、各座標 \(n\) について比べる。
2. 両辺とも定義から \(s_n\) で `rfl`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.flatten_inducedMap"></a>

## 補題 `flatten_inducedMap`

### 式

$$\mathrm{flatten}(\Phi(x))_k=F_{\mathrm{seq}}(\mathrm{flatten}(x))_k$$

### Lean のコメント（日本語訳）

> 逆極限上のフィードバックと列空間のフィードバックは flatten で可換する。

### 補題の説明

逆極限側のフィードバック \(\Phi\)（各層 \(f_n\) から誘導）と、列空間側の \(F\) が、`flatten` を通して**同じ更新**を与えます。固定点でなくても成り立つ一般の可換性です。

### 証明の概略

1. \(\Phi(x)\) の第 \(k\) 層の最後の座標を `Fn` の定義で展開する。
2. 層をまたぐ座標の対応（`layer_coord_eq_flatten`）で、\(x_k\) と前座標 \(x_{k-1}\) を `flatten x` の項に置き換え、`Fseq` の定義と一致させる（\(k=0\) は前座標 0 の場合）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.toSeqSpace_feedback"></a>

## 補題 `toSeqSpace_feedback`

### 式

$$\texttt{toSeqSpace}(\Phi(x))=F(\texttt{toSeqSpace}\ x)$$

### Lean のコメント（日本語訳）

> `toSeqSpace` はフィードバックを列空間の `F` へ移す。

### 補題の説明

`flatten_inducedMap` を `SeqSpace` の元の等式として書いたもの。

### 証明の概略

1. `Subtype.ext` と `BoundedContinuousFunction.ext`、`flatten_inducedMap`。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.fromSeqSpace_feedback"></a>

## 補題 `fromSeqSpace_feedback`

### 式

$$\Phi(\texttt{fromSeqSpace}\ s)=\texttt{fromSeqSpace}(F(s))$$

### Lean のコメント（日本語訳）

> 列空間のフィードバックを有限制限すると、各層のフィードバックと一致する。

### 補題の説明

逆向きの可換性。

### 証明の概略

1. 層 \(n\)・座標 \(i\) ごとに、`Fn` と `F` の定義を展開して一致を確かめる（`simp`）。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.toSeqSpace_fixedPoint"></a>

## 補題 `toSeqSpace_fixedPoint`

### 式

$$\Phi(x)=x\ \Rightarrow\ F(\texttt{toSeqSpace}\ x)=\texttt{toSeqSpace}\ x$$

### Lean のコメント（日本語訳）

> 逆極限固定点を列へ写すと、sup 距離空間側の縮小写像固定点になる。

### 補題の説明

積位相の逆極限で得た固定点は、sup 距離の列空間でも固定点。

### 証明の概略

1. 固定点の仮定 \(\Phi(x)=x\) に `toSeqSpace` を施し、`toSeqSpace_feedback` で左辺を \(F(\texttt{toSeqSpace}\,x)\) に書き換える。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.fixedPoint_iff"></a>

## 補題 `fixedPoint_iff`

### 式

$$\Phi(x)=x\iff F(\texttt{toSeqSpace}\ x)=\texttt{toSeqSpace}\ x$$

### Lean のコメント（日本語訳）

> 二つの固定点表現の間で、固定点であることが同値に保存される。

### 補題の説明

片側だけでなく**同値**。2 つの固定点の概念が、座標の対応で一致します。

### 証明の概略

1. （→）`toSeqSpace_fixedPoint`。
2. （←）\(x=\texttt{fromSeqSpace}(\texttt{toSeqSpace}\,x)\)（`fromSeqSpace_flatten`）と書き換え、`fromSeqSpace_feedback` で \(\Phi\) を \(F\) の側に移し、仮定 \(F(\texttt{toSeqSpace}\,x)=\texttt{toSeqSpace}\,x\) を代入する。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.inverseLimitSeqEquiv"></a>

## 定義 `inverseLimitSeqEquiv`

### 式

$$\text{逆極限}\ \simeq\ \mathrm{SeqSpace}\quad(x\mapsto\mathrm{flatten}(x),\ s\mapsto\texttt{fromSeqSpace}\ s)$$

### Lean のコメント（日本語訳）

> 逆極限部分型と sup 距離の列空間は、座標対応による型同値をなす。これは位相同型を含意しない。

### 定義の説明

逆極限の要素と \([0,1]\) 値の有界列の間の 1 対 1 対応。**型の同値**だけで、位相同型ではありません（積位相と sup 距離は一致しない）。

### 証明の概略

`toSeqSpace` と `fromSeqSpace` を使い、左逆（`fromSeqSpace_flatten`）と右逆（`toSeqSpace_fromSeqSpace`）を与える。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.tower_fixedPoint_unique"></a>

## 補題 `tower_fixedPoint_unique`

### 式

$$\Phi(x)=x,\ \Phi(y)=y\ \Rightarrow\ x=y$$

### Lean のコメント（日本語訳）

> 縮小条件のもとで、層空間上の固定点は一意である。固定点の存在自体は `tower_fixedPoint_exists` で既に与えられている。

### 補題の説明

逆極限側の固定点は**高々一つ**。一意性は、逆極限側ではなく `SeqSpace` 側の縮小写像（縮小率 \(7/10\)）から借ります。

### 証明の概略

1. 両方を `toSeqSpace_fixedPoint` で `SeqSpace` 側の固定点にする。
2. `F_contracting`（縮小写像）の `fixedPoint_unique'` で、それらが等しい。
3. 各層・各座標が `flatten` に一致する（`layer_coord_eq_flatten`）ので、\(x\) と \(y\) が等しい。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.tower_fixedPoint_exists_unique"></a>

## 補題 `tower_fixedPoint_exists_unique`

### 式

$$\exists!\,x:\ \Phi(x)=x$$

### Lean のコメント（日本語訳）

> 原文の層条件から得た存在定理と縮小条件を合わせ、逆極限固定点が一意となる。

### 補題の説明

存在（`tower_fixedPoint_exists`：Tychonoff＋Schauder 型）と一意性（`tower_fixedPoint_unique`：縮小性）を合わせて、**逆極限にちょうど 1 つの固定点**。

### 証明の概略

1. 存在は `tower_fixedPoint_exists`。
2. 他の固定点 \(y\) があれば `tower_fixedPoint_unique` で \(y=x\)。

----

<a id="Tomabechi.Examples.Theorem16TowerLayers.tower_fixedPoint_has_same_coordinates"></a>

## 補題 `tower_fixedPoint_has_same_coordinates`

### 式

$$\Phi(x)=x\ \Rightarrow\ \texttt{toSeqSpace}\ x=\text{（}F\text{ の唯一の固定点）}$$

### Lean のコメント（日本語訳）

> 逆極限固定点を flatten したものは、sup 距離側で得た唯一の固定点そのもの。

### 補題の説明

**主結論**：存在節（積位相の逆極限）で得た固定点と、縮小節（sup 距離の列空間）の固定点は、座標列として同じものです。

### 証明の概略

1. `toSeqSpace x` が `F` の固定点（`toSeqSpace_fixedPoint`）。
2. 縮小写像の固定点の一意性（`fixedPoint_unique'`）で、`ContractingWith.fixedPoint` と一致。

----

## コメント修正記録

- 2026-10-04: 冒頭コメントの最後の一文「一意性・幾何収束は `Theorem16_Tower.lean`（縮小性）」は、このファイルが後半で逆極限の固定点の一意性と `SeqSpace` 側の固定点との同一性まで示すようになった現在は不十分だったので、`.lean` のコメントに追加内容を補った（コメントのみ。宣言・証明・公理は不変）。本書 0.3 は修正後の文を訳している。
