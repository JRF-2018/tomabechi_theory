# Tomabechi/Dynamics/MeanFieldReconstruction.lean 解説

> 対象: [`Tomabechi/Dynamics/MeanFieldReconstruction.lean`](../Tomabechi/Dynamics/MeanFieldReconstruction.lean)（定理21の分岐支持・有限再構成測度・有限平均場核の積分と微分）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の「**入力分布で平均した再構成カーネル**」と「**情報の枝（branch）の順序構造**」の解析的な部品を集めたファイルです。

- 論文は、再構成カーネルを確率測度での**積分**として書きます。このファイルは、その積分の
  **微分を積分の中に入れる**（積分記号下の微分）ための条件、平均した曲率（Hessian）の評価、そして有限個の重みつきの特別な場合（**Dirac 測度の混合**）を扱います。
- 後半は、情報の枝の順序論的な仮定（記号の台の最小上界＝「アドレス」が、最上位 \(\top\) を含まない真部分集合の枝に入っている）を、
  実際の測度の台に結びつけます。

### 0.2 構成

| 節 | 内容 |
| --- | --- |
| 順序論的な台のコンテキスト | `Theorem21BranchContext`（構造体）と、測度の台・有限分布からその構成 |
| 有限の再構成測度 | 重み付き Dirac 測度、確率測度であること、台＝正の重みの原子の集合、積分＝重み付き和 |
| 一般の測度での微分 | 積分記号下の微分（優関数つき）、平均 Hessian の連続性、曲率の下界が平均で保たれること |
| 条件のパッケージ化 | 一般測度・有限混合のそれぞれで、定理21の局所谷定理が要求する解析条件を一括して導く |

### 0.3 このファイルが証明していないこと

- 一般の測度での微分の交換は、**優関数（積分可能な上界）などの条件を明示的な仮定**として受け取ります。これらの条件を論文のカーネルから導く作業は、ここにはありません。
- 台の最小上界（アドレス）が枝に入ることは、構成補題の**仮定**です（定理21の本質的な仮定）。それを導くものではありません。
- 一般の測度の場合の \(C^1\) 正則性は、平均勾配が \(C^1\) であること（または平均 Hessian の連続性）を使います。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の分岐支持と有限再構成平均場**
>
> 旧 `Theorem21.lean` の分岐支持コンテキスト、有限再構成測度、有限平均場核の積分・微分 API。強凸最適化と ODE 存在論から独立させ、宣言 namespace・名前と証明本文を保持する。

（もとのコメントが日本語なのでそのまま写しています。）

節見出しのコメントは英語で、次の意味です。

> **有限台の再構成カーネルへの特殊化。** 論文は再構成カーネルを確率測度に関する積分として書く。以下の代数的な補題は、台が有限の測度（和が 1 の非負の重みで表す）を扱う。一般の積分の下での微分は主張しない。

> **順序論的な台のコンテキスト。** 公刊された定理21は、記号の台の最小上界が、真の情報の枝の内側にあることも指定している。以下のコンテキストは、その順序に関する仮定を形式化する。一般の測度に対する構成子と、有限の離散的な構成子の両方が、順序の台を実際の測度の台に結びつける。

名前空間は `Tomabechi.Theorem21`。`open RealInnerProductSpace`、`open Filter`、`open scoped Topology NNReal ContDiff`。

---

<a id="Tomabechi.Theorem21.Theorem21BranchContext"></a>

## 構造体 `Theorem21BranchContext`

### 式

$$\text{branch}\subset L,\ \ \text{symbolSupport}\neq\varnothing,\ \ \top\notin\text{branch},\ \ \text{IsLUB}(\text{support},\ \sup\text{support}),\ \ \sup\text{support}\in\text{branch}$$

### Lean のコメント（日本語訳）

> 定理21の偏った情報の枝に付随する、順序論的なデータ。

### 定義の説明

完備束 \(L\)（抽象化の束）の中で、「情報の枝」と「記号の台」と、その**最小上界（アドレス）**を束ねた構造体です。6 つのフィールド：枝 `branch`、記号の台 `symbolSupport`、台が空でないこと、最上位 \(\top\) が枝に入らないこと（枝は束全体より真に小さい＝「空」に達しない）、台の最小上界が `sSup` で表されること、そのアドレスが枝に属すること。

### 証明の概略

1. 構造体なので証明はない（フィールドを与えることで構成する）。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.fromMeasureSupport"></a>

## 定義 `fromMeasureSupport`

### 式

$$\mu\ \text{確率測度},\ \operatorname{supp}\mu\subset\text{branch},\ \ \text{branch は}\ \sup\ \text{で閉}\ \Longrightarrow\ \text{Theorem21BranchContext}$$

### Lean のコメント（日本語訳）

> 確率測度の実際の位相的な台から、枝のコンテキストを構成する。台が空でないことと、台が利用可能な枝に含まれることは明示的な仮定である。枝が上限について閉じていることから、台のアドレスは枝の中に入る。

### 定義の説明

測度 \(\mu\) の台を記号の台とし、枝が「上限で閉じている」ことから、台の上限（アドレス）が枝に入るとします。

### 証明の概略

1. `symbolSupport := μ.support`、アドレスは `hbranch_sSup` を台に適用して枝に入る。`IsLUB` は `isLUB_sSup`。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.probability_measure_support_nonempty"></a>

## 補題 `probability_measure_support_nonempty`

### 式

$$\text{遺伝的 Lindelöf 空間上の確率測度}\ \mu\ \Longrightarrow\ \operatorname{supp}\mu\neq\varnothing$$

### Lean のコメント（日本語訳）

> 遺伝的 Lindelöf 空間上の確率測度は、空でない位相的な台をもつ。

### 補題の説明

全質量が 1（0 でない）なので、台は空になりえません。（遺伝的 Lindelöf：任意の部分空間が Lindelöf という性質。測度の台の議論に必要。）

### 証明の概略

1. Mathlib の `Measure.nonempty_support`（全質量が 0 でないなら台が非空）を適用する。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.fromProbabilityMeasure"></a>

## 定義 `fromProbabilityMeasure`

### 式

$$\mu\ \text{確率測度},\ \operatorname{supp}\mu\subset\text{branch}\ \Longrightarrow\ \text{Theorem21BranchContext}$$

### Lean のコメント（日本語訳）

> 台のコンテキストを確率測度に特殊化する。遺伝的 Lindelöf の状態空間では、台が空でないことは、全質量が 1 であることから出る。

### 定義の説明

`fromMeasureSupport` の「台が空でない」という仮定を、確率測度の仮定から自動的に満たすようにした版です。

### 証明の概略

1. `probability_measure_support_nonempty` を使って `fromMeasureSupport` に渡す。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.fromBranchMeasure"></a>

## 定義 `fromBranchMeasure`

### 式

$$\mu\ \text{が枝}\ \text{branch}\ \text{上の確率測度}\ \Longrightarrow\ \text{Theorem21BranchContext}$$

### Lean のコメント（日本語訳）

> 記号の分布が枝自身の上で定義されているときの、順序のコンテキストの構成。その台は部分型から外側の完備束へ写されるので、台が枝に含まれることは自動的に成り立つ。

### 定義の説明

測度が最初から枝の上（部分型 \(\text{branch}\)）にあるなら、台は枝の点の像なので、「台⊂枝」は自明です。

### 証明の概略

1. 台を `Subtype.val` で \(L\) へ写した像を記号の台とする。像が枝に入ることは部分型の性質。アドレスは枝の上限閉性から（13 行）。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.fromBranchMeasureOfLUB"></a>

## 定義 `fromBranchMeasureOfLUB`

### 式

$$\mu\ \text{が枝上の確率測度},\ \ \sup(\operatorname{supp}\mu)\in\text{branch}\ \Longrightarrow\ \text{Theorem21BranchContext}$$

### Lean のコメント（日本語訳）

> 台の最小上界が枝に属することが分かっているとき、枝上の測度から枝のコンテキストを構成する。これは定理21が使う順序の条件をそのまま述べたもので、枝が無関係な部分集合の上限について閉じていることは要求しない。

### 定義の説明

上の構成では「枝が一般の上限で閉じている」と強く仮定しましたが、本来必要なのは「**台の上限だけが枝に入る**」ことです。この版は必要最小限の仮定を述べます。

### 証明の概略

1. 台の像を記号の台、`haddress` をアドレスの所属条件として、フィールドを直接与える。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.branch_isProperSubset"></a>

## 補題 `branch_isProperSubset`

### 式

$$\text{branch}\subsetneq L$$

### Lean のコメント（日本語訳）

> 最上位の元を除くことで、利用可能な枝は、抽象化の束全体の真部分集合になる。

### 補題の説明

最上位 \(\top\)（論文の「空」）が枝に入らないので、枝は束全体ではありません。

### 証明の概略

1. 枝⊆全体は自明。全体⊆枝と仮定すると \(\top\) が枝に入り、`top_not_in_branch` に矛盾。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.address_ne_top"></a>

## 補題 `address_ne_top`

### 式

$$\sup\text{symbolSupport}\neq\top$$

### Lean のコメント（日本語訳）

> 台の最小上界は枝に属し、枝は大域的な最上位を除くので、その最上位より真に下にある。

### 補題の説明

記号の台のアドレスは、最上位 \(\top\) ではありません（枝に入っているから）。

### 証明の概略

1. \(\sup=\top\) と仮定すると、アドレスが枝に入ることから \(\top\in\text{branch}\)。矛盾。

----

<a id="Tomabechi.Theorem21.Theorem21BranchContext.address_le_of_support_le"></a>

## 補題 `address_le_of_support_le`

### 式

$$\forall a\in\text{support},\ a\le u\ \Longrightarrow\ \sup\text{support}\le u$$

### Lean のコメント（日本語訳）

> 台の最小上界は、その台のどの上界よりも下にある。

### 補題の説明

最小上界の定義そのもの（最小性）です。

### 証明の概略

1. `IsLUB` の最小性（`support_lub.2`）を適用する。

----

<a id="Tomabechi.Theorem21.finiteReconstructionKernel"></a>

## 定義 `finiteReconstructionKernel`

### 式

$$K(x)=\sum_a w_a\,k_a(x)$$

### Lean のコメント（日本語訳）

> 有限の重みつきの再構成カーネル。

### 定義の説明

論文の再構成カーネル（積分）の有限和版です。\(w_a\) は原子 \(a\) の重み、\(k_a(x)\) は原子ごとのカーネルです。

### 証明の概略

1. 定義：`∑ a, weight a * kernel a x`。

----

<a id="Tomabechi.Theorem21.finitePositiveWeightSupport"></a>

## 定義 `finitePositiveWeightSupport`

### 式

$$\{a\mid w_a>0\}$$

### Lean のコメント（日本語訳）

> 有限の重みつきの入力分布の代数的な台は、厳密に正の質量をもつ原子からなる。

### 定義の説明

重みが正の原子の集合です（測度の台に対応）。

### 証明の概略

1. 定義：集合 `{a | 0 < weight a}`。

----

<a id="Tomabechi.Theorem21.finite_positive_weight_support_nonempty"></a>

## 補題 `finite_positive_weight_support_nonempty`

### 式

$$w_a\ge0,\ \sum_a w_a=1\ \Longrightarrow\ \{a\mid w_a>0\}\neq\varnothing$$

### Lean のコメント（日本語訳）

> 正規化された非負の有限分布は、空でない代数的な台をもつ。

### 補題の説明

重みの和が 1 なら、必ず正の重みが 1 つはあります。

### 証明の概略

1. 背理法：すべての重みが 0（非負かつ「正でない」）なら和が 0 で、和が 1 に矛盾。

----

<a id="Tomabechi.Theorem21.finiteWeightedBranchContext"></a>

## 定義 `finiteWeightedBranchContext`

### 式

$$w\ \text{確率分布},\ \ \text{embedding}:A\to L,\ \ w_a>0\Rightarrow\text{embedding}(a)\in\text{branch}\ \Longrightarrow\ \text{Theorem21BranchContext}$$

### Lean のコメント（日本語訳）

> 有限の確率分布と抽象化の写像から、順序論的な枝のコンテキストを構成する。台が空でないことと最小上界は導かれる。得られるアドレスが枝に属することは、本質的な枝の仮定として残る。

### 定義の説明

有限個の原子（記号）に重みがあり、各原子が抽象化の束 \(L\) の元に写るとき、その像の上限（アドレス）が枝に入るという構成です。

### 証明の概略

1. 台が空でないこと（直前の補題）、像の上限が最小上界であること。
2. 正の重みの原子の像が枝に入り、枝が上限で閉じることからアドレスが枝に入る（13 行）。

----

<a id="Tomabechi.Theorem21.finiteReconstructionMeasure"></a>

## 定義 `finiteReconstructionMeasure`

### 式

$$\mu_w=\sum_a w_a\,\delta_a$$

### Lean のコメント（日本語訳）

> 重みつきの Dirac 測度で表された、有限の離散的な確率の入力。

### 定義の説明

有限個の原子に重み \(w_a\) をのせた測度（Dirac 測度の混合）です。有限和 \(\sum_a w_a g(a)\) は、この測度に関する積分になります。

### 証明の概略

1. 定義：`Measure.sum (fun a => ENNReal.ofReal (weight a) • Measure.dirac a)`（4 行）。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_measure_isProbabilityMeasure"></a>

## 補題 `finite_reconstruction_measure_isProbabilityMeasure`

### 式

$$w_a\ge0,\ \sum w_a=1\ \Longrightarrow\ \mu_w\ \text{は確率測度}$$

### Lean のコメント（日本語訳）

> 正規化された非負の重みは、有限の離散的な入力測度を確率測度にする。

### 補題の説明

全質量 \(\mu_w(\text{全体})=\sum_a w_a=1\) を確認します。

### 証明の概略

1. `isProbabilityMeasure_iff`（全質量が 1）に直し、`Measure.sum_fintype` で和に展開、Dirac 測度の全質量が 1 であることから \(\sum\text{ofReal}(w_a)=1\)。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_measure_apply_singleton"></a>

## 補題 `finite_reconstruction_measure_apply_singleton`

### 式

$$\mu_w(\{a\})=w_a$$

### Lean のコメント（日本語訳）

> 有限の Dirac 混合では、原子の質量は、割り当てられた重みである。

### 補題の説明

1 点集合の測度が、その点の重みになります。

### 証明の概略

1. 和の測度の定義を展開し、`dirac_apply` で他の原子からの寄与が 0 になることを使う（8 行）。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_measure_support_eq_positive_weight_support"></a>

## 補題 `finite_reconstruction_measure_support_eq_positive_weight_support`

### 式

$$\operatorname{supp}\mu_w=\{a\mid w_a>0\}$$

### Lean のコメント（日本語訳）

> 有限の離散的な入力空間では、再構成測度の位相的な台は、まさに正の重みをもつ原子の集合である。

### 補題の説明

測度の台（近傍がすべて正の測度をもつ点の集合）が、正の重みの原子の集合に一致します。離散位相では、1 点が開集合なので議論が簡単になります。

### 証明の概略

1. 台の特徴づけ `mem_support_iff_forall`：どの近傍も正の測度。
2. （→）1 点集合 \(\{a\}\) は近傍なので \(\mu\{a\}=w_a>0\)。
3. （←）近傍 \(U\) は \(a\) を含み \(\mu(U)\ge\mu\{a\}=w_a>0\)。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_order_support_eq"></a>

## 補題 `finite_reconstruction_order_support_eq`

### 式

$$\text{embedding}(\operatorname{supp}\mu_w)=\text{embedding}(\{w>0\})$$

### Lean のコメント（日本語訳）

> 有限測度の台を抽象化の写像で押し出しても、`finiteWeightedBranchContext` が使うのと同じ順序の台が得られる。

### 補題の説明

測度の台の像と、代数的な台（正の重み）の像が同じになるという、直前の補題の系です。

### 証明の概略

1. 直前の補題を書き換える（4 行）。

----

<a id="Tomabechi.Theorem21.integral_finite_reconstruction_measure"></a>

## 補題 `integral_finite_reconstruction_measure`

### 式

$$\int k\,d\mu_w=\sum_a w_a\,k(a)$$

### Lean のコメント（日本語訳）

> 有限の離散的な入力測度に関する積分は、まさに重みつきの有限の再構成和である。

### 補題の説明

Dirac 測度の混合に対する積分が重み付き和になる、という基本公式です（スカラー値）。

### 証明の概略

1. `integral_sum_dirac`（和の測度の積分＝各 Dirac 測度の積分の和）を適用する。

----

<a id="Tomabechi.Theorem21.integral_finite_reconstruction_measure_vector"></a>

## 補題 `integral_finite_reconstruction_measure_vector`

### 式

$$\int f\,d\mu_w=\sum_a w_a\,f(a)\qquad(f:A\to F\ \text{ベクトル値})$$

### Lean のコメント（日本語訳）

> 有限次元のベクトル値関数に対する、有限の Dirac 混合の積分の恒等式。これはスカラーの再構成の恒等式を、勾配と Hessian の場に拡張する。

### 補題の説明

上の公式のベクトル値版で、勾配・Hessian にも使います。

### 証明の概略

1. 同じく `integral_sum_dirac`。

----

<a id="Tomabechi.Theorem21.integral_reconstruction_kernel_hasFDerivAt"></a>

## 補題 `integral_reconstruction_kernel_hasFDerivAt`

### 式

$$\frac{d}{dx}\int k(x,a)\,d\mu(a)=\int\nabla_xk(x,a)\,d\mu(a)\qquad(\text{優関数つき})$$

### Lean のコメント（日本語訳）

> 明示的な可積分な優関数の仮定のもとで、一般測度の再構成積分を微分する。近傍と微分の上界は、積分変数について（ほとんど至るところ）一様である。これらの仮定は、成分ごとの勾配から、積分の勾配へ移るのに必要な測度論的な条件である。

### 補題の説明

**積分記号下の微分**（Mathlib の `hasFDerivAt_integral_of_dominated_of_fderiv_le`）を、定理21の記法に合わせた補題です。勾配の大きさが積分可能な関数 `bound` で押さえられる、というのが核心の仮定です。

### 証明の概略

1. Mathlib の優収束型の微分定理に、導関数を `innerSL`（内積による線形汎関数）で書く形で適用する（15 行）。

----

<a id="Tomabechi.Theorem21.integral_reconstruction_gradient_hasFDerivAt"></a>

## 補題 `integral_reconstruction_gradient_hasFDerivAt`

### 式

$$\frac{d}{dx}\int\nabla k(x,a)\,d\mu(a)=\int\operatorname{Hess}k(x,a)\,d\mu(a)$$

### Lean のコメント（日本語訳）

> 同じ優収束による微分の定理が、勾配の場にも適用できる。成分の Hessian が積分可能な局所的な上界をもつなら、積分した再構成カーネルの勾配は、積分した Hessian を微分として持つ。

### 補題の説明

上の補題をベクトル値（勾配）に対して使い、平均の勾配の微分が平均の Hessian になることを示します。

### 証明の概略

1. 同じ優収束型の微分定理を、値が \(E\) のベクトルとして適用（5 行）。

----

<a id="Tomabechi.Theorem21.probability_integral_hessian_bound"></a>

## 補題 `probability_integral_hessian_bound`

### 式

$$\langle H(a)v,v\rangle\le-m\|v\|^2\ \ (\mu\text{-a.e.})\ \Longrightarrow\ \Bigl\langle\Bigl(\int H\,d\mu\Bigr)v,\ v\Bigr\rangle\le-m\|v\|^2$$

### Lean のコメント（日本語訳）

> 確率の平均は、ほとんど至るところ共通のゼロ勾配と、一様な負の Hessian の上界を保つ。これは、有限混合の曲率の補題の、測度版である。

### 補題の説明

曲率の評価が「ほぼ確実に成り立つ」なら、平均しても成り立ちます（確率測度なので \(\int m\,\|v\|^2d\mu=m\|v\|^2\)）。

### 証明の概略

1. \(a\mapsto\langle H(a)v,v\rangle\) が可積分であることを確認（`integrable_comp`）。
2. 積分の単調性 `integral_mono_ae`。
3. 積分と内積の可換（`ContinuousLinearMap.integral_comp_comm`）で左辺を \(\langle(\int H)v,v\rangle\) に直す。
4. 右辺の定数の積分は、確率測度なのでその定数自身。

----

<a id="Tomabechi.Theorem21.probability_integral_gradient_eq_zero"></a>

## 補題 `probability_integral_gradient_eq_zero`

### 式

$$\nabla k(a)=0\ \ (\mu\text{-a.e.})\ \Longrightarrow\ \int\nabla k\,d\mu=0$$

### Lean のコメント（日本語訳）

> ほとんど至るところ 0 の勾配を積分すると、平均の勾配は 0 になる。

### 補題の説明

ほぼ確実に 0 である関数の積分は 0 です。

### 証明の概略

1. `integral_congr_ae` で 0 関数の積分に直し、`integral_zero`。

----

<a id="Tomabechi.Theorem21.HasDominatedReconstructionKernelFDerivAt"></a>

## 定義 `HasDominatedReconstructionKernelFDerivAt`

### 式

$$\exists s\in\mathcal N(x),\ \text{bound}\in L^1:\ \ \|\nabla k(y,a)\|\le\text{bound}(a),\ \ \text{成分ごとに微分可能},\ \ \text{可測性・可積分性}$$

### Lean のコメント（日本語訳）

> スカラーの再構成積分を、状態変数について微分するための、仮定の明示的な点ごとのパッケージ。

### 定義の説明

積分記号下の微分に必要な仮定（近傍 \(s\)、積分可能な上界、成分の可測性・可積分性・成分ごとの微分可能性）を一つの命題にまとめたものです。以降の補題では、これを仮定として受け取ります。

### 証明の概略

1. 定義（述語）なので証明はない。

----

<a id="Tomabechi.Theorem21.HasDominatedReconstructionGradientFDerivAt"></a>

## 定義 `HasDominatedReconstructionGradientFDerivAt`

### 式

$$\exists s,\text{bound}\in L^1:\ \ \|\operatorname{Hess}k(y,a)\|\le\text{bound}(a),\ \ \text{成分の勾配が微分可能}$$

### Lean のコメント（日本語訳）

> 積分した勾配の場を、積分した Hessian へ微分するための、仮定の明示的な点ごとのパッケージ。

### 定義の説明

上の定義の勾配（ベクトル値）版で、Hessian の優関数を仮定にします。

### 証明の概略

1. 定義（述語）なので証明はない。

----

<a id="Tomabechi.Theorem21.HasDominatedContinuousReconstructionHessian"></a>

## 定義 `HasDominatedContinuousReconstructionHessian`

### 式

$$\exists\text{bound}\in L^1:\ \forall x,\ \|H(x,a)\|\le\text{bound}(a)\ (\text{a.e.}),\ \ x\mapsto H(x,a)\ \text{連続}\ (\text{a.e.})$$

### Lean のコメント（日本語訳）

> 平均した再構成 Hessian についての、大域的な優関数による連続性のデータ。これはカーネル水準の条件である：1 つの可積分な上界がすべての状態を制御し、ほとんどすべての成分 Hessian が状態について連続である。

### 定義の説明

状態 \(x\) によらない 1 つの積分可能な上界で押さえられ、かつ \(x\) について連続な Hessian のデータです。平均 Hessian の連続性（優収束定理）の仮定になります。

### 証明の概略

1. 定義（述語）なので証明はない。

----

<a id="Tomabechi.Theorem21.mean_reconstruction_hessian_continuous_of_dominated"></a>

## 補題 `mean_reconstruction_hessian_continuous_of_dominated`

### 式

$$\text{優関数つき・a.e.連続}\ \Longrightarrow\ x\mapsto\int H(x,a)\,d\mu(a)\ \text{は連続}$$

### Lean のコメント（日本語訳）

> 大域的な可積分な優関数と、成分 Hessian のほとんど至るところの連続性から、そのボッホナー積分の連続性が出る。

### 補題の説明

Lebesgue の優収束定理のパラメータ版（積分のパラメータ連続性）です。

### 証明の概略

1. Mathlib の `continuous_of_dominated` を適用する（5 行）。

----

<a id="Tomabechi.Theorem21.mean_hessian_curvature_of_ae"></a>

## 補題 `mean_hessian_curvature_of_ae`

### 式

$$\langle H(a)v,v\rangle\le-m\|v\|^2\ (\text{a.e.})\ \Longrightarrow\ \langle(\int H)v,v\rangle\le-m\|v\|^2$$

### Lean のコメント（日本語訳）

> ほとんどすべての再構成入力で成り立つ曲率の評価は、Hessian のボッホナー積分を通しても成り立つ。

### 補題の説明

`probability_integral_hessian_bound` と同じ内容を、別の形（二次形式を連続線形写像として扱う）で示した補題です。

### 証明の概略

1. 二次形式 \(q(H)=\langle Hv,v\rangle\) を連続線形写像 \(q\) とし、`ContinuousLinearMap.integral_comp_comm` で積分と可換にして、積分の単調性を使う。

----

<a id="Tomabechi.Theorem21.finite_input_dominated_continuous_reconstruction_hessian"></a>

## 補題 `finite_input_dominated_continuous_reconstruction_hessian`

### 式

$$X\ \text{有限},\ \ \sup_x\|H(x,a)\|<\infty\ (\forall a)\ \Longrightarrow\ \text{HasDominatedContinuousReconstructionHessian}$$

### Lean のコメント（日本語訳）

> 有限の入力空間では、各入力の Hessian が大域的に有界なら、共通の可積分な Hessian の優関数が存在する。これは、一般測度の力学の定理が使う、優関数つき連続性のパッケージを構成する。

### 補題の説明

入力が有限個なら、各入力の上界 \(C_a\) を足し合わせれば、共通の優関数になります。

### 証明の概略

1. 各 \(a\) の上界 \(C_a\) をとり、\(\text{bound}(a)=\max(C_a,0)\) とする。有限空間なので可積分。
2. 全状態で \(\|H(x,a)\|\le\text{bound}(a)\)、連続性は仮定から。

----

<a id="Tomabechi.Theorem21.finite_input_mean_reconstruction_hessian_continuous"></a>

## 補題 `finite_input_mean_reconstruction_hessian_continuous`

### 式

$$X\ \text{有限}\ \Longrightarrow\ x\mapsto\int H(x,a)\,d\mu(a)\ \text{は連続}\ (\text{優関数なし})$$

### Lean のコメント（日本語訳）

> 有限の可測な入力空間では、成分 Hessian の積分は有限の重みつき和である。したがって、成分ごとの連続性から平均 Hessian の連続性が出て、状態空間全体にわたる大域的な優関数は要らない。

### 補題の説明

有限和は連続関数の有限和なので連続です。優関数が要らない点が前の補題との違いです。

### 証明の概略

1. 積分を有限和 \(\sum_a\mu\{a\}\,H(x,a)\) に直す（`integral_fintype`）。
2. 連続関数の有限和は連続。

----

<a id="Tomabechi.Theorem21.general_reconstruction_kernel_conditions"></a>

## 補題 `general_reconstruction_kernel_conditions`

### 式

$$\text{一般測度の仮定}\ \Longrightarrow\ \text{ポテンシャル}\ C^1,\ \text{勾配}=\textstyle\int\nabla k,\ \text{Hessian}=\int H,\ \text{中心で勾配}0,\ \text{曲率}\le-m$$

### Lean のコメント（日本語訳）

> 一般測度の再構成カーネルの仮定から、状態依存の局所谷の閾値定理が使う解析条件が出る。残りの滑らかさの仮定は明示的で、領域上の積分ポテンシャルとその平均勾配の \(C^1\) 正則性である。

### 補題の説明

一般の測度の場合に、定理21の局所谷定理が要求する条件（6 つの結論の連言）をまとめて導く補題です。微分の積分記号下の交換、曲率の平均化、中心の勾配ゼロの平均化を組み合わせます。

### 証明の概略

1. 各点の微分可能性の仮定 `hkernelDiff` から、積分記号下の微分 `integral_reconstruction_kernel_hasFDerivAt` で、ポテンシャルの Fréchet 微分を得る。
2. 勾配についても `hgradientDiff` から `integral_reconstruction_gradient_hasFDerivAt` で、勾配の Fréchet 微分（Hessian）を得る。
3. 中心の勾配が 0 であること（`hmeanCenterZero`）と曲率の評価（`hmeanCurvature`）は、仮定をそのまま渡す（`C¹` 性 `hpotentialC1`・`hmeanGradientC1` も仮定。44 行の組み立て）。

----

<a id="Tomabechi.Theorem21.contDiffOn_one_of_hasFDerivAt_continuousOn_derivative"></a>

## 補題 `contDiffOn_one_of_hasFDerivAt_continuousOn_derivative`

### 式

$$U\ \text{凸・内部が非空},\ \ f'=df\ \text{が}\ U\ \text{で連続}\ \Longrightarrow\ f\in C^1(U)$$

### Lean のコメント（日本語訳）

> 内部が空でない凸集合上で連続な導関数の場があれば、各点でのフレシェ微分可能性は、その集合上の \(C^1\) 正則性に引き上げられる。

### 補題の説明

点ごとに微分可能で、導関数が連続なら \(C^1\) 級、という標準的な事実を、集合上（`ContDiffOn`）で述べたものです。凸で内部が非空な集合では微分の一意性が成り立つので、この形で使えます。

### 証明の概略

1. `uniqueDiffOn_convex` で微分の一意性を得る。
2. `contDiffOn_succ_iff_fderivWithin` で、微分可能性と導関数の連続性に書き換える。

----

<a id="Tomabechi.Theorem21.integral_reconstruction_potential_contDiffOn_one"></a>

## 補題 `integral_reconstruction_potential_contDiffOn_one`

### 式

$$\text{優関数つき微分}\ +\ \text{平均勾配が}\ C^1\ \Longrightarrow\ \textstyle x\mapsto\int k(x,a)\,d\mu\ \text{は}\ C^1(U)$$

### Lean のコメント（日本語訳）

> 積分カーネルの優収束による微分に、平均勾配の \(C^1\) 正則性を合わせると、積分ポテンシャルの \(C^1\) 正則性が示される。これにより、平均ポテンシャルの滑らかさを別に仮定する必要がなくなる。

### 補題の説明

積分ポテンシャルの導関数（`innerSL` と平均勾配）が連続なので、ポテンシャルは \(C^1\) です。

### 証明の概略

1. 各点で微分可能で、導関数が平均勾配（\(C^1\) なので連続）であることを示す。
2. `contDiffOn_one_of_hasFDerivAt_continuousOn_derivative` を適用。

----

<a id="Tomabechi.Theorem21.integral_reconstruction_mean_gradient_contDiffOn_one"></a>

## 補題 `integral_reconstruction_mean_gradient_contDiffOn_one`

### 式

$$\text{平均}\ \text{Hessian}\ \text{連続}\ +\ \text{優関数つき微分}\ \Longrightarrow\ x\mapsto\textstyle\int\nabla k\,d\mu\ \text{は}\ C^1(U)$$

### Lean のコメント（日本語訳）

> 積分した Hessian は、平均勾配に対する連続な導関数の場である。したがって、その場の連続性と優収束による微分から、平均勾配の \(C^1\) 正則性を、別に仮定せずに得られる。

### 補題の説明

上の補題の勾配版です。平均勾配の導関数は平均 Hessian で、それが連続なら平均勾配は \(C^1\)。

### 証明の概略

1. 各点で微分可能（優収束の微分）、導関数＝平均 Hessian は連続。
2. `contDiffOn_one_of_hasFDerivAt_continuousOn_derivative` を適用。

----

<a id="Tomabechi.Theorem21.finite_input_mean_gradient_contDiffOn_one"></a>

## 補題 `finite_input_mean_gradient_contDiffOn_one`

### 式

$$X\ \text{有限},\ \text{成分}\ \text{Hessian}\ \text{連続}\ \Longrightarrow\ \textstyle\int\nabla k\,d\mu\ \in C^1(U)$$

### Lean のコメント（日本語訳）

> 有限の入力での平均 Hessian の連続性と、優収束による成分ごとの微分を合わせて、平均勾配の \(C^1\) 正則性が出る。これは、局所谷の正則性の仮定に至る有限和の経路である。

### 補題の説明

有限入力なら、平均 Hessian の連続性が優関数なしで得られる（`finite_input_mean_reconstruction_hessian_continuous`）ので、直前の補題に帰着します。

### 証明の概略

1. `finite_input_mean_reconstruction_hessian_continuous` で平均 Hessian の連続性（`ContinuousOn` に弱める）。
2. `integral_reconstruction_mean_gradient_contDiffOn_one` を適用（6 行）。

----

<a id="Tomabechi.Theorem21.finiteReconstructionGradient"></a>

## 定義 `finiteReconstructionGradient`

### 式

$$\nabla K(x)=\sum_a w_a\,\nabla k_a(x)$$

### Lean のコメント（日本語訳）

> 有限の重みつきの再構成カーネルの勾配。

### 定義の説明

有限混合のカーネルの勾配は、成分の勾配の重み付き和です。

### 証明の概略

1. 定義：`∑ a, weight a • gradKernel a x`。

----

<a id="Tomabechi.Theorem21.finiteReconstructionHessian"></a>

## 定義 `finiteReconstructionHessian`

### 式

$$H_K(x)=\sum_a w_a\,H_a(x)$$

### Lean のコメント（日本語訳）

> 有限の重みつきの再構成カーネルの Hessian 作用素。

### 定義の説明

有限混合のカーネルの Hessian は、成分の Hessian の重み付き和です（連続線形写像の和）。

### 証明の概略

1. 定義：`∑ a, weight a • hessKernel a x`。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_measure_kernel_gradient_hessian_eq_weighted"></a>

## 補題 `finite_reconstruction_measure_kernel_gradient_hessian_eq_weighted`

### 式

$$\int k\,d\mu_w=K,\ \ \int\nabla k\,d\mu_w=\nabla K,\ \ \int H\,d\mu_w=H_K$$

### Lean のコメント（日本語訳）

> 有限の再構成測度については、状態依存のカーネル・勾配・Hessian を積分したものが、有限の重みつきの定義とちょうど一致する。したがって、有限測度の経路と有限和の経路は、同じモデルを記述している。

### 補題の説明

積分で書いたモデルと、有限和で書いたモデルが同じものだ、という確認です（3 つの等式の連言）。

### 証明の概略

1. 3 つの等式それぞれに `integral_finite_reconstruction_measure`（またはベクトル版）を適用する。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_kernel_hasFDerivAt"></a>

## 補題 `finite_reconstruction_kernel_hasFDerivAt`

### 式

$$D k_a(x)=\langle\nabla k_a(x),\cdot\rangle\ \Longrightarrow\ DK(x)=\langle\nabla K(x),\cdot\rangle$$

### Lean のコメント（日本語訳）

> 有限和は微分と可換なので、重みつきの再構成カーネルは、重みつきの成分勾配を微分として持つ。この補題は有限の添字型に限られる。一般の測度積分の下での微分は主張しない。

### 補題の説明

有限和の微分は、微分の有限和です。

### 証明の概略

1. `HasFDerivAt.sum` に各項の定数倍（`HasFDerivAt.const_mul`）を適用し、`innerSL` の線形性で和を整理する（10 行）。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_gradient_hasFDerivAt"></a>

## 補題 `finite_reconstruction_gradient_hasFDerivAt`

### 式

$$D\nabla k_a(x)=H_a(x)\ \Longrightarrow\ D\nabla K(x)=H_K(x)$$

### Lean のコメント（日本語訳）

> 各成分の勾配が与えられた Hessian をもつなら、有限の再構成カーネルの勾配は、重みつきの Hessian をもつ。

### 補題の説明

勾配（ベクトル値）の有限和の微分です。

### 証明の概略

1. `HasFDerivAt.sum` と `HasFDerivAt.const_smul`（8 行）。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_gradient_eq_zero"></a>

## 補題 `finite_reconstruction_gradient_eq_zero`

### 式

$$\nabla k_a(c)=0\ (\forall a)\ \Longrightarrow\ \nabla K(c)=0$$

### Lean のコメント（日本語訳）

> 有限の混合は、共通のゼロ勾配を保つ。

### 補題の説明

どの成分の勾配も中心で 0 なら、混合の勾配も 0 です。

### 証明の概略

1. 各項が 0 なので和が 0（`Finset.sum_eq_zero`）。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_hessian_bound"></a>

## 補題 `finite_reconstruction_hessian_bound`

### 式

$$w_a\ge0,\ \sum w_a=1,\ \langle H_av,v\rangle\le-m\|v\|^2\ \Longrightarrow\ \langle H_Kv,v\rangle\le-m\|v\|^2$$

### Lean のコメント（日本語訳）

> 有限の確率混合は、一様な負の Hessian の上界を保つ。これは有限台への特殊化の、二次形式の部分である。

### 補題の説明

曲率の評価を、重み付き平均でも保てます（凸結合）。

### 証明の概略

1. 重み \(w_a\ge0\) をかけて足す：\(\sum w_a\langle H_av,v\rangle\le-m\|v\|^2\sum w_a=-m\|v\|^2\)。
2. 内積の線形性（`sum_inner`, `inner_smul_left`）で左辺を \(\langle H_Kv,v\rangle\) に直す。

----

<a id="Tomabechi.Theorem21.finite_reconstruction_kernel_conditions"></a>

## 補題 `finite_reconstruction_kernel_conditions`

### 式

$$\text{成分}\ C^2,\ \text{勾配}\ \&\ \text{Hessian}\ \text{の表現},\ \text{中心で勾配}0,\ \text{曲率}\le-m\ \Longrightarrow\ \text{有限混合も同じ条件を満たす}$$

### Lean のコメント（日本語訳）

> 局所谷の定理が必要とする、有限混合の事実をまとめる。各成分のカーネルが \(C^2\) で、その微分が与えられた成分勾配で表され、その勾配が与えられた Hessian をもつなら、有限の再構成カーネルは、対応する \(C^1\)・勾配・Hessian・中心・一様な曲率の条件を満たす。これにより、有限台への特殊化を、閾値定理でそのまま使えるようにする。

### 補題の説明

有限混合の場合の「条件のパッケージ」（6 つの結論の連言）です。前の補題を組み合わせます。

### 証明の概略

1. 混合の \(C^1\) 正則性：各成分は \(C^2\)、和・定数倍は \(C^1\)。
2. `finite_reconstruction_kernel_hasFDerivAt`, `finite_reconstruction_gradient_hasFDerivAt` で微分の表現。
3. `finite_reconstruction_gradient_eq_zero`, `finite_reconstruction_hessian_bound` で中心と曲率（29 行）。

----

<a id="Tomabechi.Theorem21.finite_measure_reconstruction_kernel_conditions"></a>

## 補題 `finite_measure_reconstruction_kernel_conditions`

### 式

$$\text{有限混合の条件}\ \Longrightarrow\ \text{等価な有限 Dirac 混合の積分でも同じ条件}$$

### Lean のコメント（日本語訳）

> 有限の重みつきの局所谷のパッケージを、等価な有限 Dirac 混合の積分へ移す。これにより、一般の積分記号下の微分の仮定を使わずに、積分による定式化が得られる。

### 補題の説明

有限和のモデルで確認した条件を、積分で書いたモデルへ移します（`finite_reconstruction_measure_kernel_gradient_hessian_eq_weighted` で関数が一致するため）。

### 証明の概略

1. 有限和版 `finite_reconstruction_kernel_conditions` を適用して条件を得る。
2. 積分で書いた関数が有限和の関数と一致する（直前の補題）ので、条件を書き換えて移す（34 行）。

----


## コメント修正記録

（なし）
