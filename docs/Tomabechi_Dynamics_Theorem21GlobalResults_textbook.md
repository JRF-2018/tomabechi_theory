# Tomabechi/Dynamics/Theorem21GlobalResults.lean 解説

> 対象: [`Tomabechi/Dynamics/Theorem21GlobalResults.lean`](../Tomabechi/Dynamics/Theorem21GlobalResults.lean)（定理21の定量力学と情報結合の結果（4 結論のまとめ））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21（局所谷の定理）の**四つの結論**を、これまでの部品（強凸性・勾配流・大域流・積分カーネル・情報核）を組み合わせて**一つの定理として**まとめるファイルです。

定理21の四つの結論は、おおまかに次のとおりです。

1. 局所領域の**内部に唯一の最小点**（谷の底）が存在し、中心から \(B/(\kappa pm-\beta)\) 以内にある。
2. 前向き不変な領域から出発する軌道が**大域的に存在**し、一意である。
3. ポテンシャル差と距離が**指数的に収束**する（速さは \(\gamma(\kappa pm-\beta)\) に関係する）。
4. 目標についての**条件付き相互情報量**が、エントロピーに等しく正になる（情報容量）。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `theorem21_identity_mobility_global_exponential_case` | 恒等移動度の場合の、最小点＋大域軌道＋指数減衰 |
| `theorem21_state_dependent_mobility_from_threshold` | 状態依存の移動度（一様に正定値）。コンパクトな前向き不変な劣水準集合を仮定 |
| `…_on_invariant_region` | 同じ結論を、任意の前向き不変な部分領域（閉包が球の内部）に対して |
| `theorem21_integral_kernel_global_dynamics_from_threshold` | 積分カーネルの場合の、最初の 3 つの結論 |
| `isClosed_closedBall_sublevel` | 閉球の劣水準集合が閉であること（補助） |
| `theorem21_integral_kernel_and_information` | 積分カーネル＋情報容量の 4 結論（正確な劣水準集合版） |
| `Theorem21GlobalOrbit` | 大域軌道の証明書（存在と一意性を束ねた構造体） |
| `theorem21_integral_kernel_and_information_on_invariant_region` | 4 結論（任意の前向き不変な部分領域版） |

### 0.3 このファイルが証明していないこと

- 前向き不変な領域 \(C\) の**存在**は、多くの定理で**仮定**です（ヘッセ行列の閾値だけからは導いていません）。正確な劣水準集合版では、球の境界でエネルギー障壁があること（`hCboundary`）という仮定から、不変性を導いています。
- 恒等移動度の定理（最初のもの）は、実効ベクトル場の \(C^1\) 正則性（球の上）と連続性（端点での貼り合わせ）を仮定します。
- 情報容量（4つ目の結論）は、目標が**有限**、行動が目標を区別する、入力エントロピーが正、などの**仮定**のもとでの結論です。論文のモデルで確かめる作業はここにはありません。
- 有限次元の特殊化です。無限次元版は `GlobalFlow.lean` の次元に依らない補題を参照してください。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理21の定量力学・情報結合の結果。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem21`。`open RealInnerProductSpace`、`open Filter`、`open scoped Topology NNReal ContDiff`。

---

<a id="Tomabechi.Theorem21.theorem21_identity_mobility_global_exponential_case"></a>

## 定理 `theorem21_identity_mobility_global_exponential_case`

### 式

$$\begin{aligned}
&\text{閉球 }\bar B=\bar B(c,r)\text{ 上で }V,S\in C^1,\ \nabla V,\nabla S\ \text{は微分可能},\ \ \nabla^2V\succeq-\beta I,\ \ \nabla^2S\preceq-mI,\ \ \nabla S(c)=0,\ \ \|\nabla V\|\le B\\
&\text{閾値: }\ p>\frac{\max(\beta,B/r)}{\kappa m},\quad \varphi=V-\kappa pS,\quad x_0\in\bar B\ \ (\text{有限次元 }E)\\
&\Longrightarrow\ \exists x^\ast\in\operatorname{int}\bar B:\ \text{最小点（}\bar B\text{ 上）},\ \ \exists x:[a,\infty)\to\bar B,\ x(a)=x_0,\ \dot x=-\nabla\varphi(x),\\
&\qquad \varphi(x(t))-\varphi(x^\ast)\le\bigl(\varphi(x_0)-\varphi(x^\ast)\bigr)e^{-2(\kappa pm-\beta)(t-a)},\quad
\|x(t)-x^\ast\|\le\sqrt{\tfrac{2(\varphi(x_0)-\varphi(x^\ast))}{\kappa pm-\beta}}\;e^{-(\kappa pm-\beta)(t-a)}
\end{aligned}$$
（**初期点が閉球内にある局所的な結論**。移動度は恒等。）

### Lean のコメント（日本語訳）

> 論文の Hessian の評価、内向きの勾配の閾値、内部の唯一の最小点、大域的な恒等移動度の軌道、定量的な指数減衰を、1 つの定理にまとめる。流れについての結論は恒等移動度の特殊化であり、閉球上の実効ベクトル場の \(C^1\) 正則性（および、端点の貼り合わせのためにその大域的な連続性）を仮定する。

### 補題の説明

定理21の**恒等移動度の場合**（\(\dot x=-\nabla V_{\text{eff}}\)）の主結論です。\(p>p_{\text{crit}}\) なら、内部に最小点があり、閉球内のどの点から出発した解も全未来で球にとどまり、速さ \(\kappa pm-\beta\)（強凸の強さ）で収束します。

### 証明の概略

1. `exists_unique_interior_minimum_of_threshold`（GlobalFlow）で内部の最小点 \(x^\*\)。
2. 強凸の強さ \(c=\kappa pm-\beta>0\)（`critical_gain_estimates`）。
3. `exists_global_exponentially_decaying_effective_gradient_flow`（GlobalFlow）に、強凸性・ポテンシャルの微分・\(C^1\) 性を渡して軌道と減衰を得る（50 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_from_threshold"></a>

## 定理 `theorem21_state_dependent_mobility_from_threshold`

### 式

$$\text{閾値}\ +\ \text{状態依存の移動度}\ A(x)\ (\gamma\text{-強制的},\ C^1)\ +\ \text{開球に厳密に含まれる劣水準集合}\ C\ \Longrightarrow\ \text{最小点・唯一性・変位の評価・大域軌道・指数減衰}\ (\gamma(\kappa pm-\beta))$$

### Lean のコメント（日本語訳）

> 状態依存の移動度をもつ定理21の、リャプノフの部分の全体。閾値の仮定が、唯一の内部の最小点と強凸性の定数を構成する。コンパクトな前向き不変な実効ポテンシャルの劣水準集合と、\(C^1\) の移動度の場から、大域存在と定量的な減衰が得られる。

### 補題の説明

**一般の状態依存の移動度**での定理21の主結論です。減衰の速さは \(\gamma\)（移動度の下界）× \(c\)（強凸の強さ）。仮定は、実効ポテンシャルの劣水準集合 \(C=\bar B\cap\{V_{\text{eff}}\le\text{level}\}\) が開球に**厳密に含まれる**こと（`hCinterior`）で、前向き不変性はそこから散逸によって**導かれます**。

### 証明の概略

1. 最小点と強凸性：`exists_unique_interior_minimum_of_threshold`, `effective_potential_strongly_convex`。
2. ポテンシャルの微分・\(C^1\) 性：和・定数倍の微分則。
3. \(C\) が閉であること（連続性から）と、前向き不変性：`forward_invariant_sublevel_of_strict_interior_barrier`（GradientFlow）で、\(C\) の厳密な内部包含と散逸から導く。
4. 大域存在と減衰：`theorem21_state_dependent_mobility_global_existence_and_decay`（GlobalFlow）を適用（124 行）。

----

<a id="Tomabechi.Theorem21.theorem21_state_dependent_mobility_from_threshold_on_invariant_region"></a>

## 定理 `theorem21_state_dependent_mobility_from_threshold_on_invariant_region`

### 式

$$\text{任意の前向き不変な部分領域}\ C\ (\overline C\subset B(c,r))\ \Longrightarrow\ \text{同じ結論}$$

### Lean のコメント（日本語訳）

> 同じ閾値の結論を、閉包が局所球の内側にある、任意の前向き不変な部分領域について述べる。領域は、閾値の最小点と初期状態を含みさえすればよく、ポテンシャルの劣水準集合全体と等しい必要はない。その不変性は、定理21で使われる局所領域の定式化に合わせた、明示的な力学的な仮定である。

### 補題の説明

前の定理は「劣水準集合」を不変集合に使いましたが、こちらは**任意の**前向き不変な部分領域で成り立ちます。次元に依らない版（`..._of_uniform_local_solutions`）を使うため、局所解の一様な時間 \(\delta\) とリプシッツ定数 \(L\) を仮定として受け取ります。

### 証明の概略

1. 前の定理と同様に最小点・強凸性を構成。
2. `theorem21_state_dependent_mobility_global_existence_and_decay_of_uniform_local_solutions`（GlobalFlow）を適用（117 行）。

----

<a id="Tomabechi.Theorem21.theorem21_integral_kernel_global_dynamics_from_threshold"></a>

## 定理 `theorem21_integral_kernel_global_dynamics_from_threshold`

### 式

$$\text{積分カーネル}\ \int k(x,a)\,d\mu\ \Longrightarrow\ \text{最小点・唯一性・変位・大域軌道・指数減衰}\ (\text{第 1〜3 結論})$$

### Lean のコメント（日本語訳）

> 定理21の最初の 3 つの結論の、積分カーネル版。優収束による微分が平均勾配と平均 Hessian を与える。ゲインの閾値は、唯一の内部の最小点、前向き不変な劣水準集合、大域的な状態依存の移動度の軌道、定量的な指数減衰を構成する。

### 補題の説明

実効ポテンシャルが \(V(x)-\kappa p\int k(x,a)\,d\mu(a)\)（偏りカーネルを入力の確率分布で平均したもの）の場合の定理21です。`MeanFieldReconstruction.lean` の積分の微分の補題で勾配・Hessian・曲率を平均化し、`theorem21_state_dependent_mobility_from_threshold` に渡します。

### 証明の概略

1. 平均 Hessian の連続性・平均勾配の \(C^1\) 性・Hessian の可積分性・曲率の平均化・中心の勾配ゼロの平均化（`MeanFieldReconstruction` の補題）。
2. `general_reconstruction_kernel_conditions` で、積分カーネル \(S=\int k\)・平均勾配・平均 Hessian が、閾値定理の仮定（\(C^1\)・微分表現・中心の勾配 0・曲率）を満たすことを導く。
3. それらを `theorem21_state_dependent_mobility_from_threshold` に渡して結論を得る（73 行）。

----

<a id="Tomabechi.Theorem21.isClosed_closedBall_sublevel"></a>

## 補題 `isClosed_closedBall_sublevel`

### 式

$$f\ \text{は}\ \bar B\ \text{で連続}\ \Longrightarrow\ \{x\in\bar B\mid f(x)\le\text{level}\}\ \text{は閉集合}$$

### Lean のコメント（日本語訳）

> 球の上で連続な関数の閉球の劣水準集合は、周りの有限次元のノルム空間で閉である。証明は、球をコンパクトな部分型と見て、そこで閉な逆像をとり、それを写し戻す。

### 補題の説明

球の上だけで連続な関数について、「球の内側で値が level 以下」の集合が（空間全体で）閉であることを示します。次の定理で、劣水準集合の閉包を調べるために使います。

### 証明の概略

1. 球はコンパクト。部分型 \(U\) 上で \(f\) は連続（`continuousOn_iff_continuous_domRestrict`）。
2. `isClosed_Iic.preimage` で \(\{f\le\text{level}\}\) は \(U\) で閉、コンパクトなので像もコンパクトで閉（25 行）。

----

<a id="Tomabechi.Theorem21.theorem21_integral_kernel_and_information"></a>

## 定理 `theorem21_integral_kernel_and_information`

### 式

$$\text{積分カーネル}\ +\ \text{情報容量}\ \Longrightarrow\ \text{第 1〜4 結論}\ (\text{正確な劣水準集合 } C=\bar B\cap\{V_{\text{eff}}\le\text{level}\})$$

### Lean のコメント（日本語訳）

> 定理21の四つの結論の、有限次元の正確な劣水準集合への特殊化。枝上の記号の測度 \(\mu\) が再構成ポテンシャルと台の最小上界を与え、情報の節は、論文のとおり、独自の入力の法則 \(\nu\) を使う。優収束による微分が、カーネル水準の仮定から滑らかな平均勾配と Hessian を導く。領域 \(C\) は閉球の劣水準集合そのものであり、連続性がそれが閉であることを示し、球面上の厳密なエネルギー障壁の仮定が、その閉包が開球にあることを示し、散逸が前向き不変性を導く。最小点と初期状態の \(C\) への所属は、初期状態についてだけ仮定する。最小点の所属は、大域的な最小性と初期の劣水準の評価から出る。これは、目標の型が有限の、有限次元の特殊化であり、任意の不変領域の定式化ではない。

### 補題の説明

**定理21の四つの結論**をすべて含みます（正確な劣水準集合版）。前向き不変性を、球面上のエネルギー障壁（`hCboundary`）と散逸から**導く**点が、`..._on_invariant_region` との違いです。結論は、最小点・唯一性・変位の評価（第 1 結論）、軌道の存在と劣水準集合への留まり（第 2）、指数減衰（第 3）、情報容量（第 4）です。

### 証明の概略

1. 最小点・強凸性（上と同様）。
2. `isClosed_closedBall_sublevel` で \(C\) は閉、コンパクト。球面上のエネルギー障壁から \(\overline C=C\subset\)開球。
3. 散逸から前向き不変性（`forward_invariant_sublevel_of_strict_interior_barrier`）。
4. 一様な前向きの局所解（`exists_uniform_forward_local_trajectory_on_compact`）、リプシッツ定数（`exists_lipschitz_constant_on_closedBall_of_contDiffAt`）、前向き不変性（`forward_invariant_sublevel_of_strict_interior_barrier`）を用意し、`theorem21_state_dependent_mobility_from_threshold_on_invariant_region` に渡して、最小点・大域軌道・指数減衰・一意性を得る。
5. 情報容量は `theorem21_general_input_information_capacity`（DeterministicOutput）を独自の入力法則 \(\nu\) に対して適用し、枝への所属の仮定をそのまま添える（239 行）。

----

<a id="Tomabechi.Theorem21.Theorem21GlobalOrbit"></a>

## 構造体 `Theorem21GlobalOrbit`

### 式

$$\text{trajectory},\ \varepsilon>0,\ \ x(a)=x_0,\ \ x'=f(x)\ \text{on}\ (a-\varepsilon,\infty),\ \ x(t)\in U,\ \ \text{一意性}$$

### Lean のコメント（日本語訳）

> 定理21の条件付きの ODE の仮定に合わせた、大域解の証明書。閉ループの解の存在を、減衰の評価から切り離す。減衰の評価は、状態の球のコンパクト性を要しない。

### 定義の説明

「大域解がある」ということを 1 つの構造体にまとめたものです。フィールドは、軌道 `trajectory`、後ろ向きの余裕 `ε`、初期条件 `initial`、開区間 \((a-\varepsilon,\infty)\) 上の ODE `flow`、その区間で領域 \(U\) に入ること `nearRegion`、**一意性** `unique`（領域 \(C\) にとどまる他の解は同じ解）です。

### 証明の概略

1. 構造体なので証明はない（各フィールドを与えて構成する）。

----

<a id="Tomabechi.Theorem21.theorem21_integral_kernel_and_information_on_invariant_region"></a>

## 定理 `theorem21_integral_kernel_and_information_on_invariant_region`

### 式

$$\text{積分カーネル}\ +\ \text{情報容量}\ +\ \text{任意の前向き不変な部分領域}\ C\ \Longrightarrow\ \text{第 1〜4 結論}$$

### Lean のコメント（日本語訳）

> 任意の前向き不変な部分的な劣水準領域についての、有限次元の積分カーネル版の定理21。閾値の仮定が唯一の内部の最小点を与える。閉ループの場の \(C^1\) 正則性、領域の閉包のコンパクト性、およびその仮定された前向き不変性が、大域軌道を構成して一意性を与える。強凸性と強制的な移動度が定量的な指数の速さを与える。最小点は、論文の力学の節が要請するとおり、この領域に属すると仮定する。有限の目標の情報の結論は、同じ定理で証明される。

### 補題の説明

`theorem21_integral_kernel_and_information` の、不変領域を**仮定**する版です（球面上のエネルギー障壁は不要）。結論は同じ 4 つで、軌道の存在・一意性は `Theorem21GlobalOrbit` の形（存在と一意性の連言）で得られます。

### 証明の概略

1. 積分カーネルの平均勾配・平均 Hessian・曲率などの導出（`MeanFieldReconstruction` の補題と `general_reconstruction_kernel_conditions`）。
2. 最小点・強凸性・停留点（上と同様）。最小点が \(C\) に属することは仮定 `hminimizerInC`。
3. `theorem21_state_dependent_mobility_global_existence_and_decay` で、大域軌道・指数減衰・一意性。
4. 情報容量は `theorem21_general_input_information_capacity` を \(\nu\) に適用して枝への所属を添える（200 行）。

----


## コメント修正記録

（なし）
