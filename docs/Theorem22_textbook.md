# Theorem22.lean 解説

> 対象: [`Theorem22.lean`](../Theorem22.lean)（定理22：LUB の段階的蓄積・容量の単調性・待ち時間・切替・TCZ の変化）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 包摂半順序 | 抽象度の包摂関係 \(\preceq\)（上位が下位を包む）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22は、情報が**段階的に蓄積**する（記号の台の最小上界 LUB が増えていく）とき、各段階で局所谷が現れ、段階を渡るごとに次の性質が成り立つという定理です。

1. **順序**（(22.1)〜(22.3)）：LUB の列 \(u_{n+1}=u_n\vee v_{n+1}\) は単調で、新情報があれば厳密に増える。
2. **容量の単調性**（(22.6)）：段階が上がっても、許容される問題・方策の情報量の上限（容量）は減らない。
3. **待ち時間**（(22.5)）：段階の谷の近く（誤差 \(\varepsilon\) 以内）に入るには、対数の待ち時間で十分。
4. **切替**：切り替えた実際の軌道は、凍結した（段階を固定した）軌道の指数評価を引き継ぐ。
5. **TCZ の変化**：谷が動けば、到達可能な領域（TCZ）も変わる。

このファイルは、**順序論・情報量・待ち時間・切替の一意性**の部分を扱います。段階ごとの谷と軌道は `StageData.lean`、容量の抽象的な定義は `Capacity.lean` にあります。

### 0.2 構成

| 節 | 宣言 | 内容 |
| --- | --- | --- |
| LUB 更新 | `lub_update_*`, `indexed_lub_step_order`, `lub_stages_*` | 結合 \(u\vee v\) による段階列の単調性・厳密な上昇・有向性・上限 |
| 容量の単調性 | `capacity_monotone_along_lub_stages` 〜 `theorem22_order_capacity_and_supremum` | LUB 列に沿った容量の単調性（抽象・KL・CMI） |
| 容量の非負性 | `layerCapacity_nonnegative_*`, `finite_kl_capacity_nonnegative`, … | 値域 \([0,\infty)\) |
| 有限ゴール容量 | `finiteGoal*`, `finite_goal_capacity_*` | 有限の入力・目標・出力での具体化。同時法則のみの保存で足りる |
| 待ち時間 | `dwell_time_suffices_for_error`, `exponential_distance_reaches_error_after_dwell` | (22.5) |
| 切替の一意性 | `switched_*`, `eq_at_right_endpoint_of_eqOn_Ico` | 実軌道と凍結軌道が待ち時間の区間で一致し、評価が移る |
| TCZ の変化 | `previous_minimizer_outside_next_sublevel`, `stage_tcz_changes` | 旧い最小点が新しい段階の劣水準集合から外れる |

### 0.3 このファイルが証明していないこと

- **切替状態が次段階の吸引域に入ること**、**切替軌道の存在と一意性**（存在の部分）、**定理19の容量埋め込み**は、**明示的な接続条件（仮定）**として残されています。これらは LUB の漸化式だけからは従いません（ファイル冒頭のコメントのとおり）。
- 容量の単調性は、層間の埋め込みが（スコア・同時法則を）保存するという**仮定**から導きます。
- 順序構造での上限が最大元 \(\top\) に**等しい**ことは主張しません。追加の共終性（cofinality）の仮定が必要です。
- 段階間の谷の距離（強凸性から出る不等式）は `previous_minimizer_outside_next_sublevel` で**仮定**として受け取ります（論文は 2 つの最小点を結ぶ線分での強凸性から導く）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理22：LUB の段階的蓄積と局所谷の帰結**
>
> 本ファイルでは、順序論的な更新則と、各段階で必要となる解析・制御の仮定を分けて扱う。冒頭の補題は LUB の更新を直接証明し、段階間の分離の結果は、定理23で使う強凸性の帰結を与える。再利用する局所最小点・指数減衰の結果は、定理21から import し、ここでは重複して証明しない。
>
> 切替状態が次の段階の吸引域に入ること、切替軌道の存在・一意性、定理19の容量埋め込みは、明示的な接続条件として残す。これらは LUB の漸化式だけからは従わない。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem22`。`open Tomabechi.Theorem21 RealInnerProductSpace Filter`、`open scoped Topology NNReal ProbabilityTheory`。

---

<a id="Tomabechi.Theorem22.lub_update_is_monotone"></a>

## 補題 `lub_update_is_monotone`

### 式

$$u\le u\vee v$$

### Lean のコメント（日本語訳）

> 結合による更新は、それまでに蓄積された情報を決して取り除かない。
> 日本語の要約：結合更新 \(u\vee v\) は、既存の情報 \(u\) を下回らない。

### 補題の説明

LUB の更新 \(u\vee v\) は元の \(u\) 以上です（上限の基本性質）。

### 証明の概略

1. `le_sup_left`。

----

<a id="Tomabechi.Theorem22.lub_update_is_strict"></a>

## 補題 `lub_update_is_strict`

### 式

$$v\not\le u\ \Longrightarrow\ u<u\vee v$$

### Lean のコメント（日本語訳）

> 真に新しい元があれば、結合による更新は厳密に増える。
> 日本語の要約：新しい情報 \(v\not\le u\) があれば、結合の更新は厳密に上昇する。

### 補題の説明

\(v\) が \(u\) に含まれない（新情報）なら、更新で必ず \(u\) より真に大きくなります。

### 証明の概略

1. \(u\le u\vee v\) は成り立つ。等しいと仮定すると \(v\le u\vee v=u\) で、\(v\not\le u\) に矛盾（7 行）。

----

<a id="Tomabechi.Theorem22.lub_update_strict_iff"></a>

## 補題 `lub_update_strict_iff`

### 式

$$u<u\vee v\ \Longleftrightarrow\ v\not\le u$$

### Lean のコメント（日本語訳）

> 逆に、結合の更新がいつ厳密に増えるかを正確に特徴づける。
> 日本語の要約：結合更新の厳密な上昇と、新情報が既存の LUB に包摂されないことは同値である。

### 補題の説明

更新が厳密に増えるのは、新しい情報が既存の情報に含まれないときに限ります。

### 証明の概略

1. （←）`lub_update_is_strict`。
2. （→）\(v\le u\) なら \(u\vee v=u\)（`sup_eq_left`）で、\(u<u\vee v\) に矛盾（8 行）。

----

<a id="Tomabechi.Theorem22.indexed_lub_step_order"></a>

## 補題 `indexed_lub_step_order`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ u_n\le u_{n+1}\le\top\ \wedge\ (v_{n+1}\not\le u_n\to u_n<u_{n+1})$$

### Lean のコメント（日本語訳）

> 順序の結論 (22.3) の、添字つきの形。束の最上位による自明な上界を含む。
> 日本語の要約：更新式 (22.1) から、段階の順序、新情報による厳密な上昇、最大元による上界を示す。

### 補題の説明

段階列 \(u_n\) の 1 ステップごとの性質（増加・最大元以下・新情報なら厳密に増加）をまとめた補題です。

### 証明の概略

1. 漸化式 \(u_{n+1}=u_n\vee v_{n+1}\) に書き換える。
2. \(u_n\le u_n\vee v_{n+1}\)（`le_sup_left`）、\(u_{n+1}\le\top\)（`le_top`）、新情報が含まれなければ厳密な増加（`lub_update_is_strict`）の 3 つを組にする（4 行）。

----

<a id="Tomabechi.Theorem22.lub_stages_monotone"></a>

## 補題 `lub_stages_monotone`

### 式

$$u_{n+1}=u_n\vee v_{n+1}\ \Longrightarrow\ u\ \text{は単調}$$

### Lean のコメント（日本語訳）

> (22.1) の結合による更新は、単調な列をつくる。
> 日本語の要約：結合更新により、LUB の段階列が単調であることを示す。

### 補題の説明

1 ステップごとに増えるので、列全体も単調です。

### 証明の概略

1. `monotone_nat_of_le_succ`（1 ステップごとの単調性から列全体の単調性）を適用（6 行）。

----

<a id="Tomabechi.Theorem22.lub_stages_directed"></a>

## 補題 `lub_stages_directed`

### 式

$$u\ \text{単調}\ \Longrightarrow\ \operatorname{range}(u)\ \text{は有向集合}$$

### Lean のコメント（日本語訳）

> 単調な列は、集合として有向である。
> 日本語の要約：単調列の値域が有向集合であることを証明する。

### 補題の説明

任意の 2 つの値 \(u_i,u_j\) の上界として \(u_{\max(i,j)}\) が取れるので、有向集合です。

### 証明の概略

1. \(u(\max(i,j))\) が上界（単調性）。

----

<a id="Tomabechi.Theorem22.lub_stages_have_supremum_below_top"></a>

## 補題 `lub_stages_have_supremum_below_top`

### 式

$$\text{DCPO（最大元つき）}:\ \operatorname{range}(u)\ \text{に最小上界}\ \sup\ \text{があり}\ \sup\le\top$$

### Lean のコメント（日本語訳）

> 最大元をもつ有向完備半順序では、増加する LUB の梯子は、最大元以下に最小上界をもつ。これは有向完備性だけを使い、原文の弱い仮定に合わせたもので、完備束の仮定ではない。
> 日本語の要約：有向完備な半順序では、単調な段階列に上限が存在し、その上限は最大元以下である。

### 補題の説明

段階列の**極限**（全体の上限）が存在することを、完備束でなく**有向完備半順序**の仮定で示します。

### 証明の概略

1. 単調列の値域は有向（前の補題）。
2. 有向完備性により最小上界 `sSup` が存在（`isLUB_sSup`）、`le_top`（4 行）。

----

<a id="Tomabechi.Theorem22.capacity_monotone_along_lub_stages"></a>

## 補題 `capacity_monotone_along_lub_stages`

### 式

$$\text{埋め込みが単射・同時法則を保存}\ \Longrightarrow\ n\mapsto\mathrm{cap}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> (22.1) の結合の漸化式と、定理19の単射で同時法則を保つ層間の埋め込みが合わさって、容量の列が単調になる。これは、順序づけられた 2 つの層の任意の 1 組についての比較だけではなく、(22.6) の添字つきの形である。
> 日本語の要約：(22.1) の段階列全体について、各段の容量が単調非減少であることを示す。

### 補題の説明

`Capacity.lean` の 2 層の比較（`capacity_nondecreasing_of_injective_law_preserving_embedding`）を、\(u_n\le u_{n+1}\) に適用して、列全体の単調性にします。

### 証明の概略

1. `monotone_nat_of_le_succ`。各 \(n\) で \(u_n\le u_n\vee v_{n+1}=u_{n+1}\)。
2. `capacity_nondecreasing_of_injective_law_preserving_embedding` を適用（9 行）。

----

<a id="Tomabechi.Theorem22.finite_kl_capacity_monotone_along_lub_stages"></a>

## 補題 `finite_kl_capacity_monotone_along_lub_stages`

### 式

$$\text{KL の組を保存する埋め込み}\ \Longrightarrow\ n\mapsto\mathrm{cap}_{\mathrm{KL}}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> 添字つきの容量の主張 (22.6) の、測度 KL への特殊化。結合の各段階で、埋め込みは許容される各項目の同時測度と参照測度を保つ。結果の実数値の KL 容量は単調である。
> 日本語の要約：LUB の更新列に沿って、KL の組を保つ埋め込みのもとで、一般の測度の KL 容量が単調になる。

### 補題の説明

KL スコア版（`capacity_nondecreasing_of_finite_kl_preserving_embedding`）の列版です。

### 証明の概略

1. 一般の `capacity_monotone_along_lub_stages` に、スコアを `finiteKLDivergenceScore ∘ law`（有限 KL ダイバージェンスのスコア）として適用する（スコアが法則から決まること `fun _ => rfl`）。

----

<a id="Tomabechi.Theorem22.conditional_mutual_information_capacity_monotone_along_lub_stages"></a>

## 補題 `conditional_mutual_information_capacity_monotone_along_lub_stages`

### 式

$$\text{同時法則のみ保存する埋め込み}\ (\text{可算生成})\ \Longrightarrow\ n\mapsto\mathrm{cap}_{\mathrm{CMI}}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> 可算生成な測度の CMI の容量は、同時法則だけを保つ埋め込みのもとで、結合/LUB の段階列の全体に沿って単調である。参照法則の保存は、各段階で条件付き核の一意性により導かれ、2 つの層の比較の結果が (22.1) について繰り返される。
> 日本語の要約：可算生成性の下で、同時法則の保存だけから、(22.1) の LUB の段階列に沿う一般の測度の CMI 容量の単調性を示す。

### 補題の説明

CMI 版（`capacity_nondecreasing_of_joint_preserving_conditional_mutual_information_embedding`）の列版です。

### 証明の概略

1. 各 \(n\) で、同時法則の保存から参照法則の保存が従い（`Capacity` の補題）、2 層の比較を適用（8 行）。

----

<a id="Tomabechi.Theorem22.theorem22_order_conditional_mutual_information_and_supremum"></a>

## 定理 `theorem22_order_conditional_mutual_information_and_supremum`

### 式

$$\text{(完備束)}:\ u\ \text{単調},\ \text{各段の順序},\ \text{CMI 容量の単調性},\ \sup u\ \text{は存在}\ \le\top$$

### Lean のコメント（日本語訳）

> 定理22の順序・容量・上限の結論を、測度論的な条件付き相互情報量に特殊化したもの。結合の段階の順序と、可算生成で同時法則を保つ CMI 容量の単調性を、1 つの結果にまとめる。
> 日本語の要約：可算生成性の下で、同時法則を保つ一般の測度の CMI 容量を用いて、定理22の段階の順序・容量の単調性・上限の結論をまとめる。

### 補題の説明

定理22の主結論（順序＋容量＋極限）を、CMI をスコアとして述べた版です（完備束 \(L\)）。

### 証明の概略

1. `lub_stages_monotone`、`indexed_lub_step_order`、`lub_stages_have_supremum_below_top`（順序）。
2. `conditional_mutual_information_capacity_monotone_along_lub_stages`（容量）をまとめる（11 行）。

----

<a id="Tomabechi.Theorem22.theorem22_order_conditional_mutual_information_and_supremum_of_dcpo"></a>

## 定理 `theorem22_order_conditional_mutual_information_and_supremum_of_dcpo`

### 式

$$\text{(有向完備半順序＋最大元)}:\ \text{同じ結論}$$

### Lean のコメント（日本語訳）

> 定理22で述べられている厳密な順序論的な仮定は有向完備性であり、完備束ではない。この版は、二項の結合を、その最小上界の性質とともに明示的なデータとして取る。そして、最大元をもつ有向完備半順序だけのもとで、LUB の漸化式、測度の CMI の容量の単調性、段階列の上限を組み合わせる。
> 日本語の要約：有向完備半順序と最大元、および最小上界として指定した二項の結合のもとで、更新・CMI 容量の単調性・上限をまとめる。

### 補題の説明

上の定理の、仮定を**論文どおりに弱めた**版です：完備束ではなく有向完備半順序（DCPO）と最大元。結合 \(\text{join}\) は、最小上界の性質 `hjoin` つきの関数として与えます。

### 証明の概略

1. 結合を `hjoin` で扱い、更新の単調性・厳密な上昇を、`IsLUB` から示す。
2. 容量の単調性、DCPO の上限の存在（30 行）。

----

<a id="Tomabechi.Theorem22.theorem22_order_capacity_and_supremum"></a>

## 定理 `theorem22_order_capacity_and_supremum`

### 式

$$\text{(完備束)}:\ u\ \text{単調},\ \text{各段},\ \mathrm{cap}\ \text{単調},\ \operatorname{IsLUB}(\operatorname{range}u,\sup),\ \sup\le\top$$

### Lean のコメント（日本語訳）

> 定理22の順序・容量・極限の LUB の結論を 1 つのインターフェースにまとめる。結合の漸化式が (22.3) を与え、単射で法則を保つ埋め込みが (22.6) の単調性を与え、有向完備性が段階列全体の上限を与える（\(\top\) で上から抑えられる）。上限が \(\top\) に等しいという主張は、追加の共終性の仮定なしには行わない。
> 日本語の要約：LUB の単調列、情報容量の単調性、列全体の上限が最大元以下であること、を統合する。最大元への到達は主張しない。

### 補題の説明

抽象スコア版（法則を経由するスコア）での、定理22の順序・容量・上限の主結論です。

### 証明の概略

1. `lub_stages_monotone`、`indexed_lub_step_order`、`capacity_monotone_along_lub_stages`、`lub_stages_have_supremum_below_top` をまとめる（11 行）。

----

<a id="Tomabechi.Theorem22.layerCapacity_nonnegative_of_score_nonnegative"></a>

## 補題 `layerCapacity_nonnegative_of_score_nonnegative`

### 式

$$\text{score}\ge0\ \Longrightarrow\ \mathrm{cap}(a)\ge0$$

### Lean のコメント（日本語訳）

> 非負のスコアは、非負の層の容量を与える。単調性の定理の有界性の前提と合わせて、定理19の容量に必要な値域 \([0,\infty)\) を記録する。
> 日本語の要約：許容されるスコアが非負なら、スコアの上限としての容量も非負である。

### 補題の説明

非負の数の上限は非負です（非空・有界）。

### 証明の概略

1. 許容される元 \(x\) をとる（非空性）。\(0\le\text{score}(x)\le\sup\)（`le_csSup`）（8 行）。

----

<a id="Tomabechi.Theorem22.finite_kl_capacity_nonnegative"></a>

## 補題 `finite_kl_capacity_nonnegative`

### 式

$$\mathrm{cap}_{\mathrm{KL}}(a)\ge0$$

### Lean のコメント（日本語訳）

> 有限の KL スコアは、`klDiv` が \(\mathbb R_{\ge0\infty}\) に値をとるので非負である。有限性が実数値のスコアを意味あるものにし、空でなく有界なスコアの族が、(22.6) で要求される非負の容量を与える。
> 日本語の要約：有限 KL スコアの非負性から、一般の測度の KL 容量が非負であることを導く。

### 補題の説明

KL ダイバージェンスは非負なので、容量も非負です。

### 証明の概略

1. `ENNReal.toReal_nonneg`、`layerCapacity_nonnegative_of_score_nonnegative`（6 行）。

----

<a id="Tomabechi.Theorem22.conditional_mutual_information_capacity_nonnegative"></a>

## 補題 `conditional_mutual_information_capacity_nonnegative`

### 式

$$\mathrm{cap}_{\mathrm{CMI}}(a)\ge0$$

### Lean のコメント（日本語訳）

> 測度論的な条件付き相互情報量は有限 KL スコアなので、定理19で述べられているのと同じ、空でない・有限容量の条件のもとで、その容量は非負である。これは、(22.6) の一般の可測 CMI への特殊化の、値域 \([0,\infty)\) の条件を完成する。
> 日本語の要約：一般の測度の CMI 容量が、論文の値域 \([0,\infty)\) に入ることを示す。

### 補題の説明

CMI は KL スコアなので、前の補題から従います。

### 証明の概略

1. `finite_kl_capacity_nonnegative` を `toFiniteKLLaw` に適用（4 行）。

----

<a id="Tomabechi.Theorem22.finiteGoalLayerCapacity"></a>

## 定義 `finiteGoalLayerCapacity`

### 式

$$\mathrm{cap}_{\text{finite}}(a)=\sup\{I(G;Y\mid X)(q)\ \mid\ q\in\text{admissible}(a)\}$$

### Lean のコメント（日本語訳）

> 層の容量を、定理21の有限ゴールの条件付き相互情報量の API に特殊化する。ここでは問題は共通の有限の文字集合 \(X\)・\(G\)・\(Y\) を共有する。これは、定理19で問題空間が変わる場合より狭く、したがって上の完全に一般なスコアに基づく結果が、一般のインターフェースとして残る。
> 日本語の要約：有限ゴール・有限の問題空間で、条件付き相互情報量を用いる層の容量を定義する。

### 定義の説明

有限モデル（`FiniteCMI` の条件付き相互情報量）をスコアとする層の容量です。

### 証明の概略

1. 定義：`layerCapacity admissible (fun q => finiteConditionalMutualInformation (mass q) (policy q)) a`。

----

<a id="Tomabechi.Theorem22.finiteGoalJointLaw"></a>

## 定義 `finiteGoalJointLaw`

### 式

$$P(x,g,y)=\begin{cases}\text{mass}(x,g)&(y=\text{policy}(x,g))\\0&(\text{else})\end{cases}$$

### Lean のコメント（日本語訳）

> 有限の文脈・目標・決定論的出力の同時法則。
> 日本語の要約：有限モデルの問題・目標・決定論的な出力の同時質量を定義する。

### 定義の説明

\((x,g)\) の質量を、決定論的な出力 \(y=\text{policy}(x,g)\) のところにだけ置いた、\((X,G,Y)\) の同時質量です。

### 証明の概略

1. 定義：`if y = policy x g then mass x g else 0`。

----

<a id="Tomabechi.Theorem22.finiteConditionalMutualInformationOfJointLaw"></a>

## 定義 `finiteConditionalMutualInformationOfJointLaw`

### 式

$$I(G;Y\mid X)=H(G\mid X)-H(G\mid X,Y)\quad(\text{同時法則 }P(x,g,y)\ \text{だけで書く})$$

### Lean のコメント（日本語訳）

> 有限の \((X,G,Y)\) の同時法則だけで書いた条件付き相互情報量。これにより、スコアは、質量 0 の \((x,g)\) の組での政策の値ではなく、観測できる法則に依存するようになる。
> 日本語の注：有限の同時法則から条件付き相互情報量を計算する。

### 定義の説明

`finiteConditionalMutualInformation`（`mass` と `policy` で定義）を、同時法則だけから計算する形に書き直した定義です。同時法則だけで決まるので、質量 0 の入力で政策の値を変えてもスコアは変わりません。

### 証明の概略

1. 定義：エントロピーの各項を同時法則の周辺和で表す（11 行）。

----

<a id="Tomabechi.Theorem22.finiteConditionalMutualInformation_factors_through_jointLaw"></a>

## 補題 `finiteConditionalMutualInformation_factors_through_jointLaw`

### 式

$$I(\text{mass},\text{policy})=I_{\text{joint}}\bigl(P(\text{mass},\text{policy})\bigr)$$

### Lean のコメント（日本語訳）

> 既存の有限の \((\text{mass},\text{policy})\) による条件付き相互情報量の定義は、誘導される \((X,G,Y)\) の同時法則を経由して因数分解される。したがって、その法則を保つことは、決定論的な政策が質量 0 の入力で変わる場合でも、スコアを保つのに十分である。
> 日本語の要約：有限の条件付き相互情報量が、誘導される同時法則だけで定まり、質量 0 の入力での政策の値を保たなくても、法則の保存だけで足りる。

### 補題の説明

`finiteConditionalMutualInformation = finiteConditionalMutualInformationOfJointLaw ∘ finiteGoalJointLaw` という書き換えです。

### 証明の概略

1. 同時法則を展開し、出力 \(y\) についての和が \(y=\text{policy}(x,g)\) の 1 項だけになること（`Finset.sum_eq_single_of_mem`）を使って、各エントロピーの項を書き換える（51 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_nondecreasing_of_joint_distribution_preserving_embedding"></a>

## 補題 `finite_goal_capacity_nondecreasing_of_joint_distribution_preserving_embedding`

### 式

$$\text{誘導された同時法則だけ保存}\ \Longrightarrow\ \mathrm{cap}_{\text{finite}}(a)\le\mathrm{cap}_{\text{finite}}(b)$$

### Lean のコメント（日本語訳）

> (22.6) の有限ゴールの容量版で、その埋め込みの前提は、誘導される同時法則だけを保つ。したがって、決定論的な政策が質量 0 の入力で変わることを許し、定理19の分布レベルの条件に合う。
> 日本語の要約：誘導された問題・目標・出力の同時法則だけを保つ層間の単射から、容量の単調性を導く。

### 補題の説明

埋め込みが（質量・政策そのものでなく）**同時法則だけ**を保てば、容量が単調になります。`finiteConditionalMutualInformation_factors_through_jointLaw` を使います。

### 証明の概略

1. スコアが同時法則の関数（上の補題）。
2. `capacity_nondecreasing_of_injective_law_preserving_embedding`（Capacity）を `jointLaw := finiteGoalJointLaw`、`scoreOfLaw := finiteConditionalMutualInformationOfJointLaw` で適用（25 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_bounded_of_probability_mass"></a>

## 補題 `finite_goal_capacity_bounded_of_probability_mass`

### 式

$$\text{mass}\ge0,\ \textstyle\sum\text{mass}=1\ \Longrightarrow\ \text{スコア集合は上に有界}\ (\le|G|)$$

### Lean のコメント（日本語訳）

> 有限の目標の文字集合では、正規化された非負の同時質量が、容量のスコアを `card G` で抑える。したがって、許容されるスコアの集合は、有限性の前提を別に置かなくても上に有界である。
> 日本語の要約：有限ゴール上の確率モデルから、容量の上界を評価する。

### 補題の説明

`FiniteCMI` の `finiteConditionalMutualInformation_le_card_mul_total` を、確率モデル（全質量 1）に適用して有界性を得ます。

### 証明の概略

1. 各 \(q\) で \(I(q)\le|G|\cdot1=|G|\)（`finiteConditionalMutualInformation_le_card_mul_total`）。上界として \(|G|\) をとる（8 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_nondecreasing_of_distribution_preserving_embedding"></a>

## 補題 `finite_goal_capacity_nondecreasing_of_distribution_preserving_embedding`

### 式

$$\text{質量・政策を保存}\ \Longrightarrow\ \mathrm{cap}_{\text{finite}}(a)\le\mathrm{cap}_{\text{finite}}(b)$$

### Lean のコメント（日本語訳）

> 分布を保つ埋め込みは、始域と終域の問題が同じ有限の文字集合を使うとき、有限ゴールの容量を非減少にする。前提は、同時モデルを、厳密に座標ごとの形（条件付き質量と決定論的な行動の写像）で保つ。結論は、定理21の情報スコアを書き換え、上限の単調性の議論を適用して得られる。単射性は、もとの仮定から保持するが、スコアの単調性の議論自体は値域の包含だけを必要とする。
> 日本語の要約：同じ有限の文字集合で、分布を保つ段階間の埋め込みから、容量の単調性を導く。

### 補題の説明

質量 `mass` と政策 `policy` を**そのまま**保つ埋め込み（より強い仮定）の場合です。スコアが保たれるので、上限の単調性が従います。

### 証明の概略

1. \(\text{score}(\text{embedding}\,x)=\text{score}(x)\)（質量・政策が等しいから）。
2. 値域の包含から上限の単調性（24 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_nondecreasing_of_probability_embedding"></a>

## 補題 `finite_goal_capacity_nondecreasing_of_probability_embedding`

### 式

$$\text{正規化された質量}\ +\ \text{分布保存}\ \Longrightarrow\ \mathrm{cap}_{\text{finite}}\ \text{単調（有界性の仮定なし）}$$

### Lean のコメント（日本語訳）

> 分布を保つ埋め込みは、正規化された有限ゴールの容量を、スコアの有界性を別に仮定しなくても、非減少にする。正規化と非負の質量が、一様な上界 `card G` を与え、有限の条件付き相互情報量の補題が、スコアの保存を与える。
> 日本語の要約：確率の正規化の仮定を使って、有限ゴールの容量の単調性を得る。

### 補題の説明

上の補題の有界性の仮定を、確率モデルの仮定（`finite_goal_capacity_bounded_of_probability_mass`）から**導く**版です。

### 証明の概略

1. `finite_goal_capacity_bounded_of_probability_mass` で有界性。
2. `finite_goal_capacity_nondecreasing_of_distribution_preserving_embedding` を適用（7 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_monotone_along_lub_stages"></a>

## 補題 `finite_goal_capacity_monotone_along_lub_stages`

### 式

$$n\mapsto\mathrm{cap}_{\text{finite}}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> 有限ゴールの条件付き相互情報量の容量は、情報を蓄積する LUB の段階に沿って単調である。これは (22.1) と (22.6) の確率モデルの例を直接組み合わせ、各段階の容量が意味をもつための正規化の上界を含む。
> 日本語の要約：情報蓄積の LUB 列に沿った、有限ゴールの容量の単調非減少性を示す。

### 補題の説明

有限ゴールの場合の、LUB 列に沿った容量の単調性です。

### 証明の概略

1. 各 \(n\) で、\(u_{n+1}=u_n\vee v_{n+1}\ge u_n\) と `finite_goal_capacity_nondecreasing_of_probability_embedding` を適用（8 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_monotone_along_lub_stages_of_joint_distribution_preserving_embedding"></a>

## 補題 `finite_goal_capacity_monotone_along_lub_stages_of_joint_distribution_preserving_embedding`

### 式

$$\text{誘導された同時法則のみ保存}\ \Longrightarrow\ n\mapsto\mathrm{cap}_{\text{finite}}(u_n)\ \text{は単調}$$

### Lean のコメント（日本語訳）

> 保存を、誘導される \((X,G,Y)\) の同時法則についてだけ述べた、有限 (22.6) の段階ごとの版。正規化された非負の質量が、各層の容量を定義するのに必要な一様なスコアの上界を与える。
> 日本語の要約：同時法則の保存だけを仮定して、LUB の更新列に沿う有限ゴールの容量の単調性を示す。

### 補題の説明

上の補題の、埋め込みの仮定を同時法則だけの保存に弱めた版です（質量 0 の入力で政策が変わってもよい）。

### 証明の概略

1. `finite_goal_capacity_nondecreasing_of_joint_distribution_preserving_embedding` を各ステップに適用（8 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_nonnegative"></a>

## 補題 `finite_goal_capacity_nonnegative`

### 式

$$I\ge0\ (\forall\text{admissible})\ \Longrightarrow\ \mathrm{cap}_{\text{finite}}(a)\ge0$$

### Lean のコメント（日本語訳）

> 許容される問題・方策の組のすべてが非負の条件付き相互情報量をもつなら、有限ゴールの層の容量は非負である。具体的な定理19の例では、これは別の情報理論的な義務である。層の上限の議論自体は、純粋に順序論的である。
> 日本語の要約：許容される問題・方策の組でスコアが非負なら、層の容量も非負である。

### 補題の説明

スコアが非負なら上限も非負、という順序論的な補題です。スコアの非負性自体は次の補題で示します。

### 証明の概略

1. `layerCapacity_nonnegative_of_score_nonnegative` を適用（5 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_nonnegative_of_mass"></a>

## 補題 `finite_goal_capacity_nonnegative_of_mass`

### 式

$$\text{mass}\ge0\ \Longrightarrow\ \mathrm{cap}_{\text{finite}}(a)\ge0$$

### Lean のコメント（日本語訳）

> 有限ゴールの特殊化では、非負の同時質量が、非負の条件付き相互情報量、したがって非負の層の容量にとって十分である。これは、具体的な確率モデルから、スコアの非負性の前提を解消する。スコアの像の有界性は、明示的なまま残る。
> 日本語の要約：非負で正規化された質量から、有限ゴールの容量の非負性を導く。

### 補題の説明

`FiniteCMI` の `finiteConditionalMutualInformation_nonneg` から、スコアの非負性が従います。

### 証明の概略

1. `finiteConditionalMutualInformation_nonneg` で各スコアが非負。`finite_goal_capacity_nonnegative` を適用（6 行）。

----

<a id="Tomabechi.Theorem22.finite_goal_capacity_probability_range"></a>

## 補題 `finite_goal_capacity_probability_range`

### 式

$$0\le\mathrm{cap}_{\text{finite}}(a)\le|G|$$

### Lean のコメント（日本語訳）

> 確率の正規化のもとで、有限ゴールの層の容量は、非負で、かつ高々目標の個数である。したがって、この共通の有限の文字集合への特殊化では、スコアの上限は有限の実数量である。
> 日本語の要約：確率の正規化のもとで、有限ゴールの容量が非負かつ目標の個数以下であることを示す。

### 補題の説明

容量の値域が \([0,|G|]\) に入ることを示します。

### 証明の概略

1. 非負性（直前の補題）。
2. 上界：スコア集合は非空で上に有界（`finite_goal_capacity_bounded_of_probability_mass`）、`IsLUB` の最小性で \(\sup\le|G|\)（24 行）。

----

<a id="Tomabechi.Theorem22.dwell_time_suffices_for_error"></a>

## 補題 `dwell_time_suffices_for_error`

### 式

$$T\ge\max\Bigl(0,\ \frac{1}{\gamma c}\log\frac{C}{\varepsilon}\Bigr)\ \Longrightarrow\ C\,e^{-\gamma cT}\le\varepsilon$$

### Lean のコメント（日本語訳）

> 待ち時間の評価 (22.5) は、指数的な距離の評価が \(\varepsilon\) より下に下がるのに十分である。これは、定量的な速さのスカラーの帰結であり、切替系の存在の仮定からは独立である。
> 日本語の要約：指数的な距離の評価について、対数の待ち時間 (22.5) が、指定された誤差への到達に十分であることを示す。

### 補題の説明

距離が \(C\,e^{-\gamma c t}\) の形で減るとき、時間 \(T\ge\frac1{\gamma c}\log(C/\varepsilon)\) 待てば誤差 \(\varepsilon\) 以下になる、という計算です。

### 証明の概略

1. \(C\le\varepsilon\) の場合：\(e^{-\gamma cT}\le1\)（\(T\ge0\)）なので \(C e^{-\gamma cT}\le C\le\varepsilon\)。
2. \(C>\varepsilon\) の場合：\(\log(C/\varepsilon)>0\)、\(\gamma cT\ge\log(C/\varepsilon)\)、よって \(e^{-\gamma cT}\le\varepsilon/C\)（44 行）。

----

<a id="Tomabechi.Theorem22.exponential_distance_reaches_error_after_dwell"></a>

## 補題 `exponential_distance_reaches_error_after_dwell`

### 式

$$\operatorname{dist}(x(t_0+T),x^\*)\le C\,e^{-\gamma cT}\ \&\ T\ge\text{待ち時間}\ \Longrightarrow\ \operatorname{dist}(x(t_0+T),x^\*)\le\varepsilon$$

### Lean のコメント（日本語訳）

> 待ち時間の条件 (22.5) を指数的な軌道の評価に組み合わせる：少なくとも対数の待ち時間だけ待てば、状態は段階の最小点の \(\epsilon\) 以内にある。軌道の評価は、定理21の定量的な状態距離の結論で具体化できる。
> 日本語の要約：待ち時間 (22.5) を満たせば、指数減衰する軌道が許容誤差の中に入ることを導く。

### 補題の説明

`dwell_time_suffices_for_error` を軌道の距離評価に適用します。

### 証明の概略

1. `hdecay` と `dwell_time_suffices_for_error` をつなぐ（`le_trans`、4 行）。

----

<a id="Tomabechi.Theorem22.switched_stage_gap_decay_of_freeze_agreement"></a>

## 補題 `switched_stage_gap_decay_of_freeze_agreement`

### 式

$$x(t)=x_{\text{free}}(t)\ (t\in[t_0,t_0+T])\ \Longrightarrow\ \text{実軌道のエネルギー差も同じ指数評価}$$

### Lean のコメント（日本語訳）

> 待ち時間の区間の間、実際の切替軌道は、中断されない段階のエネルギー評価を引き継ぐ。ただし、両方の軌道は、同じ初期値で、同じ段階の力学を解く。区間上の等式は、ここでは明示的な前提である。それを導くには、論文の切替閉ループ ODE の一意性の定理が必要である。
> 日本語の要約：待ち時間の区間上での実軌道と凍結軌道の一致を使って、指数減衰の評価を実軌道に移す。

### 補題の説明

実軌道と凍結軌道が一致していれば、凍結軌道の評価がそのまま実軌道の評価になります（一致は仮定）。

### 証明の概略

1. 一致 `hmatch` で書き換える（7 行）。

----

<a id="Tomabechi.Theorem22.switched_orbits_agree_before_endpoint"></a>

## 補題 `switched_orbits_agree_before_endpoint`

### 式

$$\text{同じ ODE・初期値・閉球にとどまる}\ \Longrightarrow\ \text{actual}=\text{free on}\ [t_0,t_0+T)$$

### Lean のコメント（日本語訳）

> 同じ段階の ODE と、定理21の閉球上の一意性の定理から、実軌道と凍結した段階の軌道の一致を導く。これは、切替の区間に使う有限次元の局所的な一意性の段階である。端点は `Ico` により除かれ、連続性により別に得られる。
> 日本語の要約：同じ閉ループ ODE と初期値についての一意性により、切替の前まで 2 つの軌道を一致させる。

### 補題の説明

`theorem21_state_dependent_closed_loop_unique_on_ball`（GlobalFlow）をそのまま適用した補題です。

### 証明の概略

1. `theorem21_state_dependent_closed_loop_unique_on_ball` を適用（5 行）。

----

<a id="Tomabechi.Theorem22.eq_at_right_endpoint_of_eqOn_Ico"></a>

## 補題 `eq_at_right_endpoint_of_eqOn_Ico`

### 式

$$f=g\ \text{on}\ [a,b),\ \ f,g\ \text{が}\ b\ \text{で連続}\ \Longrightarrow\ f(b)=g(b)$$

### Lean のコメント（日本語訳）

> 連続性により、2 つの軌道の等式を、\([a,b)\) から切替の時刻 \(b\) まで延長する。
> 日本語の要約：半開区間での一致は、右端点での連続性により、切替の時刻まで延長できる。

### 補題の説明

\(b\) の左側で一致していて、\(b\) で連続なら、\(b\) の値も一致します（ハウスドルフ空間での極限の一意性）。

### 証明の概略

1. \(b\) の左側の近傍で \(f=g\)（`filter_upwards`）。
2. 両方の左極限が \(f(b)\)、\(g(b)\) で、一致する関数の極限は同じなので \(f(b)=g(b)\)（`tendsto_nhds_unique`、13 行）。

----

<a id="Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval"></a>

## 補題 `switched_orbits_agree_on_closed_interval`

### 式

$$\text{一意性}\ +\ \text{端点の連続性}\ \Longrightarrow\ \text{actual}=\text{free on}\ [t_0,t_0+T]$$

### Lean のコメント（日本語訳）

> ODE の一意性の結果と、切替の時刻での連続性により、閉じた待ち時間の区間全体での一致が得られる。
> 日本語の要約：一意性による区間内部の一致と、終端での連続性を合わせて、閉じた待ち時間の区間全体で同定する。

### 補題の説明

直前の 2 つの補題（\([t_0,t_0+T)\) での一致と、端点の値の一致）を合わせて、閉区間での一致にします。

### 証明の概略

1. `switched_orbits_agree_before_endpoint`、`eq_at_right_endpoint_of_eqOn_Ico`（11 行）。

----

<a id="Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval_of_right_derivative"></a>

## 補題 `switched_orbits_agree_on_closed_interval_of_right_derivative`

### 式

$$\text{右微分だけ}\ +\ \text{連続}\ +\ L\text{-リプシッツ}\ \Longrightarrow\ \text{actual}=\text{frozen on}\ [t_0,t_1]$$

### Lean のコメント（日本語訳）

> 切替の時刻で自然な片側の微分による、切替軌道の一意性。経路は待ち時間の区間で連続でありさえすればよく、\([t_0,t_1)\) で右微分つきで ODE を解く。最初の切替で、両側の微分は課さない。
> 日本語の要約：切替の開始点では右微分だけを仮定し、連続性と待ち時間内の ODE から、閉区間全体で軌道の一致を示す。

### 補題の説明

切替の時刻では左側の微分が定義できないので、右微分だけで一意性を示します。Mathlib の `ODE_solution_unique_of_mem_Icc_right` 系（Grönwall）を使います。

### 証明の概略

1. `ODE_solution_unique_of_mem_Icc_right` 型の補題を、区間 \([t_0,t_1]\)、リプシッツ定数 \(L\)、右微分 `HasDerivWithinAt … (Set.Ici t)` で適用（5 行）。

----

<a id="Tomabechi.Theorem22.switched_orbits_agree_on_closed_interval_of_lipschitz"></a>

## 補題 `switched_orbits_agree_on_closed_interval_of_lipschitz`

### 式

$$\text{場が}\ L\text{-リプシッツ}\ \Longrightarrow\ \text{actual}=\text{free on}\ [t_0,t_0+T]\quad(\text{次元に依らない})$$

### Lean のコメント（日本語訳）

> 閉ループの場のリプシッツ定数を直接与えたときの、切替軌道の一致の、次元に依らない版。上の有限次元の系は、コンパクトな閉球上の \(C^1\) 正則性からこの評価を導く。一般のノルム空間では、局所的な \(C^1\) 正則性だけでは、非コンパクトな球上の一様なリプシッツ定数は得られない。
> 日本語の要約：一般のノルム空間で、場のリプシッツ定数を仮定した、次元に依らない一意性の版。

### 補題の説明

上の補題を、通常の（両側の）微分で述べた版です。

### 証明の概略

1. 両側微分から右微分を作り、連続性を用意して上の補題を適用（12 行）。

----

<a id="Tomabechi.Theorem22.switched_stage_gap_decay_from_lipschitz"></a>

## 補題 `switched_stage_gap_decay_from_lipschitz`

### 式

$$\text{リプシッツ}\ +\ \text{凍結軌道の指数評価}\ \Longrightarrow\ \text{実軌道の指数評価}$$

### Lean のコメント（日本語訳）

> 場の直接のリプシッツ評価を仮定した、凍結した段階のエネルギー評価の、実際の切替解への、次元に依らない移転。
> 日本語の要約：直接仮定したリプシッツ性から軌道の一致を証明して、凍結軌道の指数評価を移す。

### 補題の説明

軌道の一致（上の補題）を使って、`switched_stage_gap_decay_of_freeze_agreement` の仮定を満たします。

### 証明の概略

1. `switched_orbits_agree_on_closed_interval_of_lipschitz`（Lipschitz 場なら実軌道と凍結軌道が \([t_0,t_0+T]\) で一致）を適用する。
2. 初期時刻で \(\mathrm{actual}(t_0)=\mathrm{free}(t_0)\)。各 \(t\) で実軌道を凍結軌道に置き換え、凍結軌道の指数評価 `hfreeDecay` を適用する（9 行）。

----

<a id="Tomabechi.Theorem22.switched_stage_gap_decay_from_ode_uniqueness"></a>

## 補題 `switched_stage_gap_decay_from_ode_uniqueness`

### 式

$$C^1\ \text{場（有限次元）}\ +\ \text{凍結軌道の指数評価}\ \Longrightarrow\ \text{実軌道の指数評価}$$

### Lean のコメント（日本語訳）

> 凍結した段階の指数評価は、その端点より前の待ち時間の区間全体で、実際の切替軌道に移る。上の抽象的な一致の補題と違い、この補題は、共通の ODE・\(C^1\) の場・閉球への包含・同じ初期値から、軌道の一致を導く。
> 日本語の要約：有限次元の \(C^1\) の場に対する ODE の一意性を使って、待ち時間の区間での指数評価を移す。

### 補題の説明

有限次元（\(C^1\) 場ならリプシッツ）の場合に、上の補題の一致を ODE の一意性から導く版です。

### 証明の概略

1. `switched_orbits_agree_on_closed_interval`（有限次元 ODE の一意性による一致）を適用する。
2. 初期時刻で一致、各 \(t\) で実軌道を凍結軌道に置き換え、凍結軌道の指数評価 `hfreeDecay`（例：`per_stage_exponential_decay` の第 2 成分）を適用する（9 行）。

----

<a id="Tomabechi.Theorem22.switched_stage_gap_decay_from_stage_estimate"></a>

## 補題 `switched_stage_gap_decay_from_stage_estimate`

### 式

$$\text{段階の評価（例えば}\ \texttt{per\_stage\_exponential\_decay}\ \text{の第 2 成分）}\ \Longrightarrow\ \text{実切替軌道の評価}$$

### Lean のコメント（日本語訳）

> (22.4) のエンドツーエンドのインターフェース：凍結した軌道についての段階の評価（例えば `per_stage_exponential_decay` の第 2 成分）と、有限次元の ODE の一意性が、閉じた待ち時間の区間全体で、実際の切替軌道についての同じ定量的な評価を導く。
> 日本語の要約：凍結段階の指数評価と、実軌道との待ち時間での一致から、実軌道の評価を導く。

### 補題の説明

`per_stage_exponential_decay`（StageData）の出力を、そのまま実切替軌道へ移す形に整えた補題です。

### 証明の概略

1. 凍結軌道の評価 `hstageEstimate`（\(t\ge t_0\)）を、区間 \([t_0,t_0+T]\) に制限して `switched_stage_gap_decay_from_ode_uniqueness` に渡す。

----

<a id="Tomabechi.Theorem22.switched_state_reaches_error_after_dwell"></a>

## 補題 `switched_state_reaches_error_after_dwell`

### 式

$$T\ge\text{待ち時間}\ \Longrightarrow\ \operatorname{dist}(x_{\text{actual}}(t_0+T),x^\*)\le\varepsilon$$

### Lean のコメント（日本語訳）

> 待ち時間の区間の終わりでの、実際の切替状態に (22.5) を適用する。凍結した段階の距離の評価は、有限次元の ODE の一意性により移され、連続性が右端点での一致を与える。
> 日本語の要約：凍結軌道との一致と待ち時間の条件から、実切替軌道の切替時の誤差を評価する。

### 補題の説明

**(22.5) の実軌道版**：段階の距離評価（凍結軌道）と、実軌道との一致から、待ち時間のあと実軌道が誤差 \(\varepsilon\) 以内に入ります。

### 証明の概略

1. `switched_orbits_agree_on_closed_interval` で、終点 \(t_0+T\) まで実軌道と凍結軌道が一致。
2. 凍結軌道の距離評価 `hfreeDistance`（\(t=t_0+T\)）に、`dwell_time_suffices_for_error`（待ち時間 \(T\) が十分なら誤差が \(\epsilon\) 以下）を合わせる（12 行）。

----

<a id="Tomabechi.Theorem22.previous_minimizer_outside_next_sublevel"></a>

## 補題 `previous_minimizer_outside_next_sublevel`

### 式

$$\theta<\tfrac c2\delta^2\le V_{n+1}(x^\*_n)-V_{n+1}(x^\*_{n+1})\ \Longrightarrow\ x^\*_n\notin\{x\mid V_{n+1}(x)-V_{n+1}(x^\*_{n+1})\le\theta\}$$

### Lean のコメント（日本語訳）

> 次の段階でのポテンシャルの差が、直前の最小点を、次の段階の劣水準集合から除く。厳密な差の評価は前提として公開される：論文は、それを 2 つの最小点を結ぶ線分上の強凸性から導く。このインターフェースは、Hessian から強凸性への段階を、黙って仮定することを避ける。
> 日本語の要約：強凸性による段階間のポテンシャルの差が、次の段階の閾値を超えれば、古い最小点を除く。

### 補題の説明

段階が進むと谷の位置が動き、古い谷の底は新しい段階では「谷の外（高い所）」になる、という主張です。ポテンシャルの差 \(V_{n+1}(x^\*_n)-V_{n+1}(x^\*_{n+1})\ge\frac c2\delta^2\) は、強凸性から出るべき評価で、**ここでは仮定**です。

### 証明の概略

1. 仮定の差の評価と閾値 \(\theta<\frac c2\delta^2\) から、旧最小点では \(V_{n+1}(x^\*_n)-V_{n+1}(x^\*_{n+1})>\theta\)。劣水準集合の定義に反するので外にある（5 行）。

----

<a id="Tomabechi.Theorem22.stage_tcz_changes"></a>

## 補題 `stage_tcz_changes`

### 式

$$x^\*_n\in\text{tcz}_n,\ \ x^\*_n\notin\text{tcz}_{n+1}\ \Longrightarrow\ \text{tcz}_{n+1}\neq\text{tcz}_n$$

### Lean のコメント（日本語訳）

> 古い最小点が古い到達可能な TCZ に属し、次の段階の強凸性の差がそれを新しい TCZ から除くなら、2 つの TCZ の集合は異なる。
> 日本語の要約：古い最小点の古い TCZ への所属と、次の段階の TCZ からの除外から、隣り合う TCZ の不一致を示す。

### 補題の説明

TCZ（目標集合）が段階ごとに**変わる**ことの、集合論的な結論です。古い点が古い集合にあり新しい集合にないなら、2 つの集合は等しくありません。

### 証明の概略

1. 等しいと仮定すると、`hold` と `hnew` が矛盾（5 行）。

----


## コメント修正記録

（なし）
