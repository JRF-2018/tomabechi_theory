# Tomabechi/Consistency/ConsistencyR123_HConditions.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_HConditions.lean`](../Tomabechi/Consistency/ConsistencyR123_HConditions.lean)（追加の明示条件 H-flow・H-sum・H-stage・H-info を、名前のついた命題として書き下す）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 標準 Borel 空間 | 測度論でよい性質（可測な逆写像など）をもつ空間。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 劣勾配（凸劣勾配） | 凸関数が折れ曲がって微分できない点でも使える「傾き」。ベクトル \(g\) が \(f(z)\ge f(x)+g\cdot(z-x)\)（支持不等式）をすべての \(z\) で満たすとき、\(g\) を \(x\) での劣勾配という。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

追加の明示条件（[Additional_Assumptions.md](Additional_Assumptions.md)）は、これまで証拠つきのデータ型の中に**埋め込まれていて**、名前で取り出せませんでした。このファイルは、四つの条件を、共有モデル `N` の成分についての**独立した命題**として書き下し、最終の入力型を満たす任意の `N` で成り立つことを示します。これで「追加条件とは具体的に何か」が、Lean の型として読めるようになります。

| 構造体 | 追加条件 | 対象の定理 |
| --- | --- | --- |
| `ExplicitHFlow` | H-flow：同じ指定フィードバックが軌道・到達集合を生成し、再始動が整合する | 定理1–4・20、24・26・27 |
| `ExplicitHSum` | H-sum：可算層の有限部分和の一様可積分性・a.e. 収束・端点の総和可能性 | 定理15→23 第一部 |
| `ExplicitHStage` | H-stage：段階の谷の平均場データ | 定理21・22・23 第二部 |
| `ExplicitHInfo` | H-info：出力空間が標準 Borel | 定理19・21・22 の情報節 |

### 0.2 このファイルが証明していないこと

* ここで述べるのは、**このモデルで使った形**の H 条件です（以下に各条件の範囲を書きます）。
* H-flow の残りの部分（定理3の状態写像、距離・Borel 構造の一致）は、このファイルでは述べません（別のファイルにあります）。
* 追加条件が「必要である」ことは主張しません。これらは現在の証明が使う十分条件です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> `ExplicitAdditionalConditions N` は、共有保存式と具体 context の採用等式からなる。追加の明示条件 H-flow・H-sum・H-stage・H-info は、これまで証拠つきデータの型（`C1OptimalConsensusAdapter`・`SharedEntropyInputs`・`MeanFieldStageInput` など）の中に埋め込まれていて、名前で取り出せなかった。ここではそれぞれを共有署名 N の field についての命題として書き下し、最終受入型 `SharedPointDomainInputs N` を満たす任意の N で成り立つことを示す（具体証人への代入ではない）。
>
> 範囲：ここで述べるのは、このモデルで用いた形の H 条件である。H-stage は全段の平均場入力の条件、H-sum は全 alive 区間の有限部分和の一様可積分性・a.e. 収束・端点総和可能性、H-flow は一点初期集合の同じ選択 flow・再始動・到達集合と頂点軌道の再始動、H-info は出力の型 `Bool` が標準 Borel 空間であることに限る。定理3の状態写像と、ノルム・Borel 構造の一致（H-flow の残りの部分）は、ここでは述べない。

「具体証人への代入ではない」とは、`sharedModel` という特定のモデルについて確かめるのではなく、**最終入力型を満たすどんな `N` についても**成り立つ、という意味です。

---

<a id="Tomabechi.Consistency.R123.ExplicitHFlow"></a>

## 構造体 `ExplicitHFlow`

### 式

$$
\text{同じ選択 flow で } x(t)\ \text{を生成},\quad \Phi_{s\to t}\circ\Phi_{a\to s}=\Phi_{a\to t}\ (a\le s\le t),\quad \text{到達集合は前向き不変}
$$

### Lean のコメント（日本語訳）

> H-flow：一点初期集合の同じ選択 flow が軌道と到達集合を生成し、再始動が軌道の続きと一致する。頂点の閉ループ軌道も非負開始時刻で再始動と整合する。

### 定義の説明

H-flow は、「軌道・到達集合・残差を別々に選ぶ曖昧さ」を除く条件です。フィールドは次のとおりです。

* `same_selected_flow`：どの初期点・開始時刻でも、アダプタの flow は同じ選択 flow（`N.legacy.c1.selectedFlow`）。
* `point_initial`：初期集合は一点集合 `{x}`。
* `reachable_from_flow`：到達集合は、その flow の解から作った到達集合（閉包）。
* `flow_initial`：時刻 `s` に点 `y` から始めた軌道の、時刻 `s` での値は `y`。
* `flow_restart`：`a ≤ s ≤ t` のとき、`a` から `t` までの軌道は、途中の `s` で再始動した軌道と一致する（半群則）。
* `reachable_invariant`：非負の開始時刻で、到達集合の点から始めた軌道は、以後も到達集合に留まる（前向き不変）。
* `top_restart`：頂点の閉ループ軌道も、非負の開始時刻で再始動と整合する。

### 証明の概略

構造体の定義です（証明はありません。成立の証明は `explicitHConditions` で与えます）。

----

<a id="Tomabechi.Consistency.R123.ExplicitHSum"></a>

## 構造体 `ExplicitHSum`

### 式

$$
\sum_p w_p H_p<\infty,\qquad \Bigl\{\textstyle\sum_{p\in s} w_p h_p\Bigr\}_{s\ \text{有限}}\ \text{は }L^1\text{ で一様可積分},\qquad \sum_{i<k} w_{p_i}h_{p_i}(t)\ \xrightarrow{\text{a.e.}}\ \sum_p w_p h_p(t)
$$

### Lean のコメント（日本語訳）

> H-sum：全 alive 区間で、正層の有限部分和の一様可積分性、列挙の部分和の a.e. 収束、端点での総和可能性。全時刻での総和可能性は要求しない。

### 定義の説明

可算無限個の層の和を扱うための条件です（定理15→23 第一部）。無限和の項別微分は、そのままでは成り立ちません。そこで、各有限区間 \([a,b]\)（\(0\le a<b\)）について次を明示的に要求します。

* `endpoint_summable`：両端 \(a, b\) で、重みつきエントロピーの総和が収束する。
* `all_finite_ui`：正層の有限部分和の導関数の族が、区間上で一様可積分。
* `prefix_tendsto`：層の列挙に沿った部分和が、ほとんど至る所の \(t\) で、全体の和に収束する。

全時刻での総和可能性までは要求しません。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ExplicitHStage"></a>

## 構造体 `ExplicitHStage`

### 式

$$
F_n=B_n-\kappa_n\,\rho_n\,M_n,\quad \overline{\{F_n\le F_n(x^{\mathrm{init}}_n)\}}\subset B(c_n,r_n)
$$

（\(B_n\) は背景場、\(M_n\) は平均場、\(c_n,r_n\) は球の中心と半径）

### Lean のコメント（日本語訳）

> H-stage：全段で、平均場の全点積分表示、中心と台の LUB の表象、閉球上の背景・平均場の C² 性、移動度の C¹ 性・対称性・一様強制性、勾配表現、初期点を含む部分準位の閉包が開球内にあること、初期値で決まる部分準位の等式。

### 定義の説明

段階の谷（定理21・22・23 第二部）の入力を、各段 \(n\) ごとに並べたものです。

* `meanField_integral`：平均場は、すべての点で積分表示に一致する。
* `center_lub`：球の中心は、台の上限（LUB）の表象に等しい。
* `background_c2`・`meanField_c2`：閉球の各点の周りで、背景場・平均場は C²。
* `background_gradient`・`meanField_gradient`：勾配は、内積による表現と Fréchet 微分が一致する。
* `mobility_c1`・`mobility_symmetric`・`mobility_coercive`：移動度は C¹、対称、一様強制（\(\gamma\lVert w\rVert^2\le\langle Mw,w\rangle\)）。
* `initial_mem`：初期点は部分準位集合に入る。
* `sublevel_barrier`：部分準位集合の閉包は、球の内部に入る（内部障壁）。
* `sublevel_eq`：部分準位集合は、閉球のうち、有効ポテンシャルが初期値以下の点の集合に等しい。

`sublevel_barrier` は、原文の「任意の不変領域」より強い十分条件です（[Additional_Assumptions.md](Additional_Assumptions.md)）。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ExplicitHInfo"></a>

## 構造体 `ExplicitHInfo`

### 式

$$
Y=\mathrm{Bool}\ \text{は標準 Borel 空間}
$$

### Lean のコメント（日本語訳）

> H-info：情報実験と定理21の行為出力の型 `Bool` は標準 Borel 空間である。

### 定義の説明

情報理論の節の出力空間が、標準 Borel 空間であるという条件です。このモデルでは出力の型が `Bool`（二値）なので、`Bool` が標準 Borel 空間であること（`Nonempty (StandardBorelSpace Bool)`）を述べます。これは、可測な単射から可測な復号器を作るために使います。出力空間が標準 Borel でないと成り立たない反例が、定理19にあります（[Additional_Assumptions.md](Additional_Assumptions.md)）。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ExplicitHConditions"></a>

## 構造体 `ExplicitHConditions`

### 式

$$
\mathrm{H\text{-}flow}\wedge\mathrm{H\text{-}sum}\wedge\mathrm{H\text{-}stage}\wedge\mathrm{H\text{-}info}
$$

### Lean のコメント（日本語訳）

> 追加の明示条件 H の四つをまとめたもの。

### 定義の説明

四つの H 条件（`flow`・`sum`・`stage`・`info`）を一つにまとめた述語です。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedPointDomainInputs.explicitHConditions"></a>

## 定理 `SharedPointDomainInputs.explicitHConditions`

### 式

$$
\mathrm{SharedPointDomainInputs}(N)\ \Longrightarrow\ \mathrm{ExplicitHConditions}(N)
$$

### Lean のコメント（日本語訳）

> 最終受入型を満たす任意の N で、H 条件が名前付きで成り立つ。

### 補題の説明

最終の入力型を満たす `N` なら、四つの H 条件が成り立ちます。特定のモデルではなく、**任意の** `N` についての定理なので、「追加条件は、最終入力型が要求するものの一部を名前で取り出したもの」であることが分かります。

### 証明の概略

1. 最終入力型から、核の入力（`SharedKernelInputs`）、27・3 の入力（`SharedR3And27Inputs`）、保存式 `hp`、エントロピーの入力 `he` を取り出す。
2. **H-flow**：`same_selected_flow`・`point_initial`・`reachable_from_flow` は保存式 `hp` の `point_flow`・`point_initial`・`point_reachable`。`flow_initial`・`flow_restart` は flow 自身の性質（`initial`・`restart`）。`reachable_invariant` は入力型の `invariant`。頂点の再始動は、27 の頂点入力（`top27`）の `restart` から。
3. **H-sum**：エントロピーの入力 `he` の `endpoint_summable`・`all_finite_ui`・`prefix_tendsto` をそのまま並べる。
4. **H-stage**：各段 `N.stages n` が持つ同名の証拠フィールド（`meanField_eq_integral`、`center_eq_supportLub_representation`、`background_c2_at` など）を一対一に並べる。
5. **H-info**：`Bool` の標準 Borel 構造は型クラスの自動解決（`inferInstance`）で得られる。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_explicit_H_conditions"></a>

## 定理 `final_consistency_with_explicit_H_conditions`

### 式

$$
\exists N,\ \mathrm{FullOriginalPremises}(N)\wedge\mathrm{ExplicitAdditionalConditions}(N)\wedge\mathrm{SharedNondegenerate}(N)\wedge\mathrm{ExplicitHConditions}(N)
$$

### Lean のコメント（日本語訳）

> 最終存在宣言に、H 条件を名前付きで加えた版。外部のモデル前提を含まない。

### 補題の説明

最終存在宣言（[Final の解説](Tomabechi_Consistency_ConsistencyR123_Final_textbook.md)）に、「追加の明示条件 H は、具体的にはこの四つの命題である」という名前を付けた版です。内容が増えるのではなく、追加条件を読める形で明示します。

### 証明の概略

1. `sharedModel` を取る。
2. 最初の三つは `Final` の三つの定理（`sharedModel_fullOriginalPremises`・`sharedModel_explicitAdditionalConditions`・`sharedModel_nondegenerate`）。
3. 四つ目は、上の `explicitHConditions` を `sharedModel_fullOriginalPremises.inputs`（最終入力型）に適用する。

----

## コメント修正記録

`.lean` のコメントの修正はありません。
