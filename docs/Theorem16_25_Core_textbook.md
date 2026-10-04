# Theorem16_25_Core.lean 解説

> 対象: [`Theorem16_25_Core.lean`](../Theorem16_25_Core.lean)（定理16・25の依存コア（逆極限・固定点・縮小写像・無我））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 包摂半順序 | 抽象度の包摂関係 \(\preceq\)（上位が下位を包む）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 局所凸空間 | 凸な開集合の基をもつ位相ベクトル空間。Schauder 型不動点定理の舞台。 |
| Tychonoff の定理 | コンパクト空間の（無限）積はコンパクト。 |
| Schauder–Tychonoff 不動点定理 | コンパクト凸集合上の連続な自己写像に固定点がある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| Knaster–Tarski | 完備束上の単調写像に最小・最大の固定点がある。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理16**（自己意識の固定点）と**定理25**（無我）の、依存関係を整えた論理の核です。

- **定理16**：各層の状態の**逆極限**（層の間の射影と整合する、全層の状態の組）の上で、連続な自己写像（自己意識のフィードバック）には**固定点**がある（Schauder–Tychonoff／Fan–Glicksberg）。さらに、完備距離上の**縮小写像**なら固定点は**一意**で、**幾何級数的に収束**する。
- **定理25**：(25.1) 履歴ごとに固定点が異なれば、**全履歴に共通する固定点はない**。(25.2) 条件 25-D（機能的完備性：候補の自性に介入しても関係状態と将来出力の同時法則が変わらない）のもとで、**関係状態を超える因果効果をもつ固定的な自性（アートマン）は存在しない**。

### 0.2 構成

| 節 | 内容 |
| --- | --- |
| 縮小写像の例 | Euler の勾配更新・勾配流の時間 \(T\) 写像が縮小写像になる十分条件（定理21との橋） |
| 逆極限 | 層の状態の逆極限が非空・コンパクト・凸（`affineInverseLimitSet` など）、有限層の整合性を有向性から導く |
| 固定点の存在 | Fan–Glicksberg（Econlib からの移植）、定理16の固定点存在、Knaster–Tarski の別の道 |
| 縮小条件節 | Banach の定理による一意性・幾何収束・自己表象の固定点 |
| 反例 | 恒等写像：連続・コンパクト凸でも一意性も縮小性も出ない |
| 履歴別の固定点族 | `HistoryFixedPoints` と、各種の構成（存在・一意性・縮小・順序論） |
| 定理25 (25.1) | 共通の固定点がないこと |
| 因果モデル | 25-A(2)・25-D のモデル（抽象・確率測度・SCM・大域履歴・共有法則） |
| 25-B/C | 存在プロファイル・関係網・C3 の統合モデル |
| 定理25 (25.2) | 25-D のもとで Atman は存在しない（多くの変種） |
| まとめ | `theorem16_25_conditionalProofCore` ほか |

### 0.3 このファイルが証明していないこと

- **縮小性は、定理16の局所凸・コンパクトの位相的な条件から導けません**（恒等写像が反例）。縮小条件は論文に明記された**追加条件**で、ここでは明示的な仮定として使います。基礎的な逆極限条件から縮小性を導いたとは主張しません。
- 定理16の**存在節**は Econlib の Fan–Glicksberg を移植して証明しています（縮小性は不要）。
- **条件 25-A(1)（履歴によって固定点が異なる）**と**25-D（機能的完備性）**は、**独立した仮定**です。25-B/C は意味づけを与えますが、25-D を導きません。
- 25-A(2)（確率法則の条件）は、25.1・25.2 の論理的な証明には使いません。
- 固定点・状態・出力の符号化、候補の独立性・可測性などの**モデルの対応条件は仮定**です。定理16の位相的な条件から導いたものではありません。
- 距離・縮小性の具体モデルでの検証（定理21型の強凸性から縮小を導く部分は一部のみ）は、個別モデルの課題です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理16・25の依存コア**
>
> このファイルでは、履歴ごとの逆極限の状態と、層別のフィードバックの整合性を型で表し、定理16の固定点の存在・縮小写像による一意性と、定理25の第 1 の結論の論理的な接続を分ける。
>
> 原文の定理16は、有限層の族の整合性からなる逆極限と、連続な自己写像に対する固定点の存在を主張し、さらに、完備距離の上の縮小性を条件として、一意性と幾何的な収束を述べる。有限層の整合性は、有向性・各層の非空性・射影の合成則・TCZ の像の包含から導出し、別の仮定にはしない。この縮小の条件は、原文に明示されているが、局所凸・コンパクトの条件から導く証明は、原文にない。Mathlib v4.34.1 には、局所凸空間のコンパクトな凸集合に対する固定点定理はないため、Econlib の Fan–Glicksberg の証明の依存を、Apache-2.0 の表示つきで移植し、定理16の存在の部分を形式化する。存在と、縮小条件のもとでの一意性・幾何的な収束を、別々に扱う。元の論文の条件を受け取る統合定理は、恒等射影則と最大元なしも API に残すが、有限整合性の導出と固定点の存在の証明では、それらを使用しない。
>
> 定理25の第 1 の結論は、異なる履歴に相対する固定点が異なるという条件 25-A(1) と、各履歴で固定点が一意であることから、全履歴に共通の固定点がないことを導く。
>
> 第 2 の結論は、条件 25-D の機能的完備性を、「候補の自性の介入が、関係状態と将来の出力の同時法則を変えない」と読む、操作的なモデルの上で形式化する。25-B・25-C は、モデルの層別・関係の構造を与えるが、それらだけから 25-D は導かれない。

名前空間は `Tomabechi.Theorem16_25`。`open Function`、`open scoped Convex`、`open scoped RealInnerProductSpace`。（`Econlib` 由来のファイルについては `docs/Econlib_textbook.md` を参照する予定。）

---

<a id="Tomabechi.Theorem16_25.theorem25_finiteDomain_aemeasurable"></a>

## 補題 `theorem25_finiteDomain_aemeasurable`

### 式

$$U\ \text{有限離散},\ f:U\to V\ \Longrightarrow\ f\ \text{は}\ \mu\text{-a.e. 可測}$$

### Lean のコメント（日本語訳）

> 有限離散の外生空間からの写像は可測であり、その確率法則の pushforward は通常の像測度になる。

### 補題の説明

有限で各点が可測な空間からの写像は、必ず可測です。後で「外生ノイズを有限個の値に限った」モデルの法則（像測度）を定義するための準備です（private 補題）。

### 証明の概略

1. `MeasurableSingletonClass` と `Finite` から、可測集合の逆像が有限個の 1 点集合の和になることを使い、`Measurable.aemeasurable` を得る。

----

<a id="Tomabechi.Theorem16_25.theorem25_probabilityMap_eq_one_of_forall_mem"></a>

## 補題 `theorem25_probabilityMap_eq_one_of_forall_mem`

### 式

$$\forall u,\ f(u)\in s\ \Longrightarrow\ (f_\*\mu)(s)=1$$

### Lean のコメント（日本語訳）

> 確率測度の pushforward は、すべての像点を含む可測集合に確率 1 を与える。

### 補題の説明

すべての値が集合 \(s\) に入るなら、像測度で \(s\) の確率は 1 です。

### 証明の概略

1. 像測度の定義 \((f_\*\mu)(s)=\mu(f^{-1}s)\) と、\(f^{-1}s\) が全体であることから、確率測度の全質量 1 を使う。

----

<a id="Tomabechi.Theorem16_25.gradientEulerStep_contracting"></a>

## 補題 `gradientEulerStep_contracting`

### 式

$$\text{強凸（}c\text{）},\ \|\nabla V(y)-\nabla V(x)\|\le L\|y-x\|,\ 1-2\eta c+\eta^2L^2\le K^2\ \Longrightarrow\ x\mapsto x-\eta\nabla V(x)\ \text{は}\ K\text{-縮小}$$

### Lean のコメント（日本語訳）

> 強単調な勾配と勾配の Lipschitz の上界があれば、明示したステップ幅の条件のもとで、陽的な Euler の勾配更新は縮小写像になる。これは、定理21型のポテンシャルの力学から、定理16の `ContractingWith` へ進むための、有限次元・離散時間の橋渡しの候補である。

### 補題の説明

勾配降下法の 1 ステップ \(x\mapsto x-\eta\nabla V(x)\) が、ステップ幅 \(\eta\) が適切なら**縮小写像**になる、というよく知られた事実です。縮小写像なら Banach の不動点定理で、唯一の固定点（谷の底）への幾何収束が得られます。

### 証明の概略

1. 更新後の 2 点の差のノルムの 2 乗を展開：\(\|y-x\|^2-2\eta\langle\nabla V(y)-\nabla V(x),y-x\rangle+\eta^2\|\nabla V(y)-\nabla V(x)\|^2\)。
2. 強単調性（`strongly_monotone_gradient`、StrongConvexity）で内積項を \(c\|y-x\|^2\) 以上、Lipschitz で最後の項を \(L^2\|y-x\|^2\) 以下。
3. \((1-2\eta c+\eta^2L^2)\|y-x\|^2\le K^2\|y-x\|^2\) で縮小率 \(K\)（`nlinarith`）。

----

<a id="Tomabechi.Theorem16_25.stronglyConvexGradientFlow_dist_contracting"></a>

## 補題 `stronglyConvexGradientFlow_dist_contracting`

### 式

$$\operatorname{dist}(f(t),g(t))\le e^{-c(t-a)}\operatorname{dist}(f(a),g(a))$$

### Lean のコメント（日本語訳）

> 強凸ポテンシャルに対する、恒等移動度の自律勾配流 \(x'=-\nabla V\) は、2 つの軌道の間の距離を、指数率 \(c\) で縮める。各軌道が凸領域に留まることは明示的な仮定である。これは、定理21の状態依存の移動度 \(x'=-A(x)\nabla V\) 一般を扱わず、また、定理16の抽象的な層別のフィードバックとの同一視も、仮定からは導かない。

### 補題の説明

同じ勾配流の**2 つの異なる軌道**が、互いに指数的に近づく（距離が縮む）ことを示します。1 つの軌道が目標に近づく（定理1・21）のとは別の、**軌道間の縮小**です。

### 証明の概略

1. 距離の 2 乗 \(D(t)=\|f(t)-g(t)\|^2\) の微分は \(-2\langle\nabla V(f)-\nabla V(g),f-g\rangle\)。
2. 強単調性から \(D'\le-2cD\)。
3. Grönwall 型の評価（`Tomabechi.Theorem1` の指数比較）で \(D(t)\le e^{-2c(t-a)}D(a)\)、平方根をとる。

----

<a id="Tomabechi.Theorem16_25.coordinateFlow_dist_contracting"></a>

## 補題 `coordinateFlow_dist_contracting`

### 式

$$\operatorname{dist}(\phi(f(t)),\phi(g(t)))\le e^{-\mu(t-a)}\operatorname{dist}(\phi(f(a)),\phi(g(a)))$$

### Lean のコメント（日本語訳）

> 座標変換後のドリフトが一様に強単調なら、もとの状態の軌道の、変換座標での距離は指数的に縮む。距離は \(\mathrm{dist}(\text{coordinate}\,x,\text{coordinate}\,y)\) であり、もとの座標の Euclid 距離ではない。

### 補題の説明

1 次元の状態で、座標 \(\phi\) を取り替えると \(\phi(x(t))\) のドリフトが一様に強単調になる場合の、軌道間の縮小です。「適合距離」のモデル（座標の取り替え）の基礎です。

### 証明の概略

1. 差 \(\delta(t)=u_g(t)-u_f(t)\)（変換座標）と \(q=\delta^2\)、積分因子つきの量 \(\phi(t)=e^{2\mu(t-a)}q(t)\) を置く。
2. \(\delta'=\text{drift}(f)-\text{drift}(g)\)、\(q'=2\delta\,\delta'\)。ドリフトの強単調性（率 \(\mu\)）から \(\phi'\le0\)（内部で）。
3. \(\phi\) は連続で内部の導関数が非正なので、区間上で単調非増加（平均値の定理）。よって \(q(t)\le e^{-2\mu(t-a)}q(a)\)、平方根をとって距離の指数縮小（132 行）。

----

<a id="Tomabechi.Theorem16_25.stronglyConvexGradientFlow_timeMap_contracting"></a>

## 補題 `stronglyConvexGradientFlow_timeMap_contracting`

### 式

$$\Phi_T:x_0\mapsto x(T)\ \text{は}\ e^{-cT}\text{-縮小写像（}T>0\text{）}$$

### Lean のコメント（日本語訳）

> 恒等移動度の強凸な勾配流の、時間 \(T>0\) の写像は、すべての初期値からの軌道が領域に留まるなら、縮小写像になる。これは、定理16の Banach の条件に対する十分条件の例である。軌道の大域存在・領域の不変性、および定理16の自己意識の更新則との同一視は別途必要で、定理21にある状態依存の移動度 \(A(x)\) を含む一般の系への拡張も、証明していない。

### 補題の説明

勾配流を時間 \(T\) だけ進める写像（時間 \(T\) 写像）が縮小率 \(e^{-cT}<1\) の縮小写像であることを示します。これが、定理16の「縮小条件」の十分条件の**1 つの具体例**です。

### 証明の概略

1. `stronglyConvexGradientFlow_dist_contracting` を、\(a=0\)、\(t=T\) で 2 つの初期値からの軌道に適用して、\(\operatorname{dist}(\Phi_T x,\Phi_T y)\le e^{-cT}\operatorname{dist}(x,y)\)。
2. \(e^{-cT}<1\)（\(c,T>0\)）で `ContractingWith`。

----

<a id="Tomabechi.Theorem16_25.affineMap_preserves_convexCombination"></a>

## 補題 `affineMap_preserves_convexCombination`

### 式

$$f(ax+by)=af(x)+bf(y)\quad(a+b=1)$$

### Lean のコメント（日本語訳）

> アフィン写像は、係数の和が 1 の凸結合を保つ。

### 補題の説明

アフィン写像（線形写像＋定数）は、重み付き平均を保ちます。逆極限の凸性の証明で使う基本事実です。

### 証明の概略

1. アフィン写像の定義から、係数の和が 1 であることを使って定数項をまとめる。

----

<a id="Tomabechi.Theorem16_25.ProjectionConstraintIndex"></a>

## 定義 `ProjectionConstraintIndex`

### 式

$$\{(\beta,\alpha)\mid\beta\le\alpha\}$$

### Lean のコメント（日本語訳）

> 逆極限を定める射影の方程式の添字。

### 定義の説明

層の添字 \(I\)（半順序集合）の、順序づけられた対 \(\beta\le\alpha\) の全体です。各対に「\(\alpha\) 層の状態を \(\beta\) 層へ射影した結果が \(\beta\) 層の状態に一致する」という方程式が 1 つ対応します。

### 証明の概略

1. 定義：`{p : I × I // p.1 ≤ p.2}` 型の別名。

----

<a id="Tomabechi.Theorem16_25.affineInverseLimitSet"></a>

## 定義 `affineInverseLimitSet`

### 式

$$\varprojlim K=\Bigl\{(x_i)\in\prod_iK_i\ \Bigm|\ \pi_{\beta\alpha}(x_\alpha)=x_\beta\ (\beta\le\alpha)\Bigr\}$$

### Lean のコメント（日本語訳）

> 凸な層の状態集合の逆極限は、層の間の射影がアフィンなら凸である。これは、Schauder–Tychonoff の固定点定理に渡す、逆極限の側の凸性を形式化する。

### 定義の説明

**逆極限**：すべての層の状態の組 \((x_i)\) で、層の間の射影が整合しているもの全体です。定理16の「逆極限の状態空間」で、各層の凸なコンパクト集合 \(K_i\) の積の中で、射影の方程式を満たす部分集合として定義します。

### 証明の概略

1. 定義：`{x | (∀ i, x i ∈ K i) ∧ ∀ β ≤ α, project _ (x α) = x β}`。

----

<a id="Tomabechi.Theorem16_25.product_locallyConvexSpace"></a>

## 補題 `product_locallyConvexSpace`

### 式

$$\prod_iE_i\ \text{は局所凸空間}$$

### Lean のコメント（日本語訳）

> 各層の局所凸性は、積の空間にも引き継がれ、Schauder–Tychonoff を適用する周囲の空間を与える。

### 補題の説明

局所凸な空間の積は局所凸です（Mathlib の標準インスタンス）。固定点定理の舞台になります。

### 証明の概略

1. 型クラス推論 `inferInstance`。

----

<a id="Tomabechi.Theorem16_25.product_topologicalVectorSpaceOperations"></a>

## 補題 `product_topologicalVectorSpaceOperations`

### 式

$$\text{加法・スカラー倍が連続}\ \Longrightarrow\ \prod_iE_i\ \text{でも連続}$$

### Lean のコメント（日本語訳）

> Fan–Glicksberg を使う周囲の空間は、単なる局所凸空間のクラスではなく、位相ベクトル空間である。各層で加法とスカラー倍が連続なら、積の空間でも両方の連続性が引き継がれる。

### 補題の説明

固定点定理（Fan–Glicksberg）は位相ベクトル空間を要求するので、その条件が積空間で成り立つことを確認します。

### 証明の概略

1. 型クラス推論（積空間の `IsTopologicalAddGroup`, `ContinuousSMul`）。

----

<a id="Tomabechi.Theorem16_25.affineProjectionConstraint"></a>

## 定義 `affineProjectionConstraint`

### 式

$$C_{(\beta,\alpha)}=\{x\mid\pi_{\beta\alpha}(x_\alpha)=x_\beta\}$$

### Lean のコメント（日本語訳）

> 射影の整合条件を、積の空間の上の 1 つの閉の候補として表す。

### 定義の説明

各対 \(\beta\le\alpha\) の整合条件を満たす点の集合です。逆極限はこれら全部の共通部分（と各 \(K_i\) の積との共通部分）になります。有限交叉性でコンパクト性・非空性を示すために使います。

### 証明の概略

1. 定義：`{x | project _ (x j.1.2) = x j.1.1}` の形（添字の対 `j` に対して）。

----

<a id="Tomabechi.Theorem16_25.affineInverseLimitSet_nonempty_compact_of_relativeContinuous"></a>

## 補題 `affineInverseLimitSet_nonempty_compact_of_relativeContinuous`

### 式

$$\pi\ \text{が}\ K\ \text{上でのみ連続},\ \text{有限層整合}\ \Longrightarrow\ \varprojlim K\ \text{は非空かつコンパクト}$$

### Lean のコメント（日本語訳）

> 各射影が TCZ 上でだけ連続でも、逆極限は非空かつコンパクトである。積の TCZ の部分型を周囲の空間とみなして、等式の制約の閉性を示すので、周囲の空間全体への連続な延長は仮定しない。

### 補題の説明

**逆極限の存在とコンパクト性**（論文の条件に近い形）：各層が（コンパクトで空でない）TCZ \(K_i\) で、射影が \(K\) 上で連続、有限個の層についてなら整合する状態が取れる、という仮定から、全体の整合する状態が存在し、集合としてコンパクトです。

### 証明の概略

1. 積 \(\prod K_i\) は Tychonoff の定理でコンパクト。
2. 各整合条件は、\(K\) の部分型の上で閉（Hausdorff と連続性から）。
3. 有限個の整合条件の共通部分は、有限層整合から非空。コンパクト集合の閉部分集合族の有限交叉性から、全体の共通部分が非空・コンパクト。

----

<a id="Tomabechi.Theorem16_25.affineInverseLimitSet_isCompact"></a>

## 補題 `affineInverseLimitSet_isCompact`

### 式

$$\pi\ \text{が連続}\ \Longrightarrow\ \varprojlim K\ \text{はコンパクト}$$

### Lean のコメント（日本語訳）

> コンパクトな層の積の中で、アフィンの射影の方程式が閉であれば、逆極限はコンパクトである。Hausdorff な層と、連続な射影から閉性を得るための条件も、引数に明記する。

### 補題の説明

上の補題の、非空性を除いた版（射影が全体で連続）です。閉集合（整合条件）の共通部分はコンパクト集合の閉部分集合なので、コンパクトです。

### 証明の概略

1. 各整合条件の集合は閉（連続な写像の等式の集合、Hausdorff）。
2. その共通部分と \(\prod K_i\)（コンパクト）の共通部分は、コンパクト集合の閉部分集合。

----

<a id="Tomabechi.Theorem16_25.affineInverseLimitSet_nonempty"></a>

## 補題 `affineInverseLimitSet_nonempty`

### 式

$$K_i\neq\varnothing,\ \text{有限層整合}\ \Longrightarrow\ \varprojlim K\neq\varnothing$$

### Lean のコメント（日本語訳）

> 論文の各層の非空性と、有限層の整合性から、アフィンの逆極限は非空である。コンパクトな層の積に、閉の射影の等式を加える、有限交叉の議論を直接適用する。

### 補題の説明

**逆極限が空でない**ことを、各層が空でなく、有限個の層ごとには整合する状態があることから示します（有限交叉性）。

### 証明の概略

1. 各整合条件は閉。有限個の整合条件と \(\prod K_i\) の共通部分は非空（有限層整合）。
2. コンパクト空間での有限交叉性（`IsCompact.inter_iInter_nonempty` 型）で全体が非空。

----

<a id="Tomabechi.Theorem16_25.affineInverseLimitSet_convex"></a>

## 補題 `affineInverseLimitSet_convex`

### 式

$$K_i\ \text{凸},\ \pi\ \text{が}\ K\ \text{上でアフィン}\ \Longrightarrow\ \varprojlim K\ \text{は凸}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆極限は凸集合です：2 つの整合する状態の凸結合は、各層で凸（\(K_i\) の凸性）で、射影がアフィンなので整合性も保ちます。

### 証明の概略

1. 凸結合 \(ax+by\) をとり、各成分が \(K_i\) に入る（凸性）。
2. 射影がアフィンなので \(\pi(ax_\alpha+by_\alpha)=a\pi x_\alpha+b\pi y_\alpha=ax_\beta+by_\beta\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_inverseLimit_nonempty_compact_convex"></a>

## 定理 `theorem16_inverseLimit_nonempty_compact_convex`

### 式

$$\varprojlim K\ \text{は非空・コンパクト・凸}$$

### Lean のコメント（日本語訳）

> 逆極限の強い条件の版。射影の連続性を周囲の空間全体で仮定する。論文の条件に近い、相対連続性の版は `theorem16_inverseLimit_of_originalLayerConditions` を使う。

### 補題の説明

**定理16の前半**（Schauder–Tychonoff に渡す舞台の整備）：逆極限は空でなく、コンパクトで、凸です。

### 証明の概略

1. `affineInverseLimitSet_nonempty`、`affineInverseLimitSet_isCompact`、`affineInverseLimitSet_convex` をまとめる。

----

<a id="Tomabechi.Theorem16_25.theorem16_finiteLayerConsistency_of_directedProjections"></a>

## 補題 `theorem16_finiteLayerConsistency_of_directedProjections`

### 式

$$I\ \text{上向き有向},\ \pi\ \text{が合成則を満たし}\ K\ \text{を保つ}\ \Longrightarrow\ \forall\text{有限}\ t,\ \exists\ \text{整合する}\ (z_i)_{i\in t}$$

### Lean のコメント（日本語訳）

> 上向きに有向な添字集合では、有限個の層の上界をとり、その層の任意の点を、すべての有限個の層へ射影できる。射影の合成則と TCZ の像の包含により、有限層の整合性は、別の仮定ではなく、導かれる。

### 補題の説明

論文の「任意の有限個の層について整合する点がある」という条件を、**有向性**から導きます。有限個の層の上界の層の 1 点をとり、そこから各層へ射影すれば、射影の合成則により互いに整合します。

### 証明の概略

1. 有限集合 \(t\) についての帰納法（`Finset.induction_on`）。
2. 新しい層を加えるとき、既存の層と新しい層の共通の上界の層をとり（有向性）、その層の点から射影で全層の値を定める。
3. 射影の合成則（`hprojectComp`）で整合性、像の包含（`hprojectMaps`）で \(K\) への所属。

----

<a id="Tomabechi.Theorem16_25.theorem16_inverseLimit_of_originalLayerConditions"></a>

## 定理 `theorem16_inverseLimit_of_originalLayerConditions`

### 式

$$\text{(原文の逆系条件)}\ \Longrightarrow\ \varprojlim K\ \text{は非空・コンパクト・凸}$$

### Lean のコメント（日本語訳）

> 定理16の原文に列挙された逆系の条件を入口に明示した、統合結果。原文との対応のために、最大元なしと射影の恒等則も受け取るが、この存在・コンパクト性の証明では使わない。有限層の整合性は別の引数にせず、上界の層の 1 点を有限個の層へ射影して導く。したがって、以下の逆極限の結論には、最大元なしは位相論的には不要である。

### 補題の説明

**定理16の逆極限の部分**を、論文の仮定の形（有向・各層非空・射影の合成則・TCZ の像の包含・射影の TCZ 上での連続性）で述べた定理です。有限層の整合性は、`theorem16_finiteLayerConsistency_of_directedProjections` で導きます。

### 証明の概略

1. 有限層の整合性：`theorem16_finiteLayerConsistency_of_directedProjections`。
2. `affineInverseLimitSet_nonempty_compact_of_relativeContinuous`（非空・コンパクト）と `affineInverseLimitSet_convex`（凸）を合わせる。

----

<a id="Tomabechi.Theorem16_25.affineLayerProjection"></a>

## 定義 `affineLayerProjection`

### 式

$$\pi_{\beta\alpha}:K_\alpha\to K_\beta$$

### Lean のコメント（日本語訳）

> TCZ の間の層間の射影を、部分型の上の写像として表す。

### 定義の説明

射影を、TCZ の点（部分型）から TCZ の点への写像として扱い直したものです。

### 証明の概略

1. 定義：`⟨project hβα x.1, hprojectMaps hβα x.2⟩`。

----

<a id="Tomabechi.Theorem16_25.inducedAffineInverseLimitMap"></a>

## 定義 `inducedAffineInverseLimitMap`

### 式

$$F((x_i)_i)=(f_i(x_i))_i$$

### Lean のコメント（日本語訳）

> 各層の TCZ の上で定義されたフィードバックが射影と可換なら、逆極限の上に誘導される自己写像。周囲の空間全体への延長は要求しない。

### 定義の説明

各層で定義された写像 \(f_i\) が、射影と可換（\(\pi\circ f_\alpha=f_\beta\circ\pi\)）なら、成分ごとに適用した \(F=(f_i)\) は、逆極限を逆極限へ写します（整合性が保たれる）。

### 証明の概略

1. 成分ごとに \(f_i\) を適用し、可換性 `hcomm` で整合性（逆極限に属すること）を示して定義する。

----

<a id="Tomabechi.Theorem16_25.inducedAffineInverseLimitMap_continuous"></a>

## 補題 `inducedAffineInverseLimitMap_continuous`

### 式

$$f_i\ \text{連続}\ \Longrightarrow\ F\ \text{連続}$$

### Lean のコメント（日本語訳）

> 層別の連続なフィードバックから、逆極限上の誘導された自己写像の連続性が従う。

### 補題の説明

積位相では、各成分が連続な写像は連続です。

### 証明の概略

1. 積空間への写像が連続 ⇔ 各成分が連続（`continuous_pi`）。

----

<a id="Tomabechi.Theorem16_25.theorem16_fixedPoint_exists_of_originalLayerConditions"></a>

## 定理 `theorem16_fixedPoint_exists_of_originalLayerConditions`

### 式

$$\begin{aligned}
&I\ \text{有向},\ E_i\ \text{局所凸 Hausdorff},\ K_i\subset E_i\ \text{非空・コンパクト・凸},\ p_{\beta\alpha}\ \text{は }K_\alpha\text{ 上で連続アフィン},\ p_{\alpha\alpha}=\mathrm{id},\ p_{\gamma\beta}p_{\beta\alpha}=p_{\gamma\alpha},\ p(K_\alpha)\subset K_\beta\\
&f_i:K_i\to K_i\ \text{連続},\ \ p_{\beta\alpha}\circ f_\alpha=f_\beta\circ p_{\beta\alpha}\\
&\Longrightarrow\ \exists x\in\varprojlim K_i,\ \ \tilde f(x)=x
\end{aligned}$$
（最大元なし `hnoMax` も署名にあるが、固定点存在の証明では使わない。縮小性は不要＝存在節のみ。）

### Lean のコメント（日本語訳）

> 定理16の逆極限の条件から、層別の連続なフィードバックが誘導する、逆極限の自己写像の固定点が存在する。逆極限の非空・コンパクト・凸性と Fan–Glicksberg を合成するため、縮小性は不要である。原文との対応で、最大元なし・射影の恒等則も引数に含むが、この証明では不要である。有限層の整合性は、上向きの有向性・層ごとの非空性・射影の合成則・TCZ の像の包含から導き、独立の仮定にしない。

### 補題の説明

**定理16の固定点の存在節**：逆極限は非空・コンパクト・凸で、誘導された写像は連続なので、Fan–Glicksberg の固定点定理（Schauder–Tychonoff の一般化）により固定点が存在します。縮小性は要りません。

### 証明の概略

1. `theorem16_inverseLimit_of_originalLayerConditions` で、逆極限 \(L\) が非空・コンパクト・凸であることを得る。
2. 誘導写像 \(\tilde f\) が \(L\) 上で連続であること（`inducedAffineInverseLimitMap_continuous`）。
3. \(x\mapsto\{\tilde f(x)\}\)（1 元の集合値写像）を作り、グラフが閉・値が非空凸であることを示して、`fanGlicksbergFixedPoint`（Econlib）を直接適用する。固定点 \(x\in\{\tilde f(x)\}\) から \(\tilde f(x)=x\)（58 行）。

----

<a id="Tomabechi.Theorem16_25.theorem16_fixedPoint_exists_of_continuous_inverseLimitMap"></a>

## 定理 `theorem16_fixedPoint_exists_of_continuous_inverseLimitMap`

### 式

$$F:\varprojlim K\to\varprojlim K\ \text{連続}\ \Longrightarrow\ \exists x,\ F(x)=x$$

### Lean のコメント（日本語訳）

> 逆極限のコンパクト・凸性が、定理16の層の条件から得られたあとは、層別の写像への分解を要求せず、逆極限全体の上の任意の連続な自己写像について、固定点が存在する。原文の \(F\) が層別の連続な写像から誘導されるとは限らない場合の、定理16→25のための入口である。

### 補題の説明

上の定理を、「層別に分解できない」一般の連続な自己写像 \(F\) に対して述べたものです（定理25 への接続用）。

### 証明の概略

1. `theorem16_inverseLimit_of_originalLayerConditions` で逆極限 \(L\) が非空・コンパクト・凸。
2. 与えられた連続な自己写像 \(F:L\to L\) について、集合値写像 \(\Phi(x)=\{F(x)\}\) を作る。グラフ \(\{(x,y)\mid y=F(x)\}\) は閉（`isClosed_eq`、\(F\) の連続性）、値は \(L\) に含まれる非空凸集合。
3. `fanGlicksbergFixedPoint`（Econlib）を適用し、\(x\in\{F(x)\}\) から \(F(x)=x\)（49 行）。

----

<a id="Tomabechi.Theorem16_25.HasClosedGraph"></a>

## 定義 `HasClosedGraph`

### 式

$$\operatorname{graph}\Phi=\{(x,y)\mid y\in\Phi(x)\}\ \text{が閉}$$

### Lean のコメント（日本語訳）

> Econlib の Fan–Glicksberg の API と同じ意味で、集合値の写像のグラフの閉性を表す。

### 定義の説明

集合値写像（対応）\(\Phi\) のグラフが閉集合であること。Kakutani–Fan–Glicksberg の固定点定理の仮定です。

### 証明の概略

1. 定義：`IsClosed {p | p.2 ∈ Φ p.1}`。

----

<a id="Tomabechi.Theorem16_25.exists_fixedPoint_of_fanGlicksberg"></a>

## 補題 `exists_fixedPoint_of_fanGlicksberg`

### 式

$$K\ \text{非空・コンパクト・凸},\ f:K\to K\ \text{連続}\ \Longrightarrow\ \exists x,\ f(x)=x$$

### Lean のコメント（日本語訳）

> 局所凸の Hausdorff 空間の、空でないコンパクトな凸集合上の連続な自己写像は、固定点をもつ。Econlib の Kakutani–Fan–Glicksberg の定理を、1 元の対応 \(\{f(x)\}\) に適用した、定理16の存在節に対応する一般的な結果である。縮小性は仮定しない。

### 補題の説明

Schauder–Tychonoff の固定点定理の形です。Mathlib にはない定理で、Econlib からの移植（Apache-2.0）を使います。

### 証明の概略

1. 連続写像 \(f:K\to K\) の、1 元の集合値写像 \(\Phi(x)=\{f(x)\}\) を作る。
2. グラフ \(\{(x,y)\mid y=f(x)\}\) は `isClosed_eq` で閉。値は \(K\) に含まれる（\(f(x)\in K\)）、凸（`convex_singleton`）、非空。
3. `fanGlicksbergFixedPoint`（Econlib）を適用して、\(x\in\{f(x)\}\)、すなわち \(f(x)=x\)（26 行）。

----

<a id="Tomabechi.Theorem16_25.existsUnique_fixedPoint_of_fanGlicksberg_and_contraction"></a>

## 補題 `existsUnique_fixedPoint_of_fanGlicksberg_and_contraction`

### 式

$$K\ \text{コンパクト・凸},\ f\ \text{連続かつ}\ q\text{-縮小}\ \Longrightarrow\ \exists!\,x,\ f(x)=x$$

### Lean のコメント（日本語訳）

> Fan–Glicksberg の存在と Banach の縮小条件を、同じ一般的な設定で合成する。コンパクトな部分集合は、周囲の距離が誘導する距離で完備なので、連続性から存在を得て、縮小性からその固定点の一意性を得る。原文の定理16の縮小の節を、toy モデルによらず記述する。

### 補題の説明

**存在（Fan–Glicksberg）＋唯一性（縮小）**：コンパクトな凸集合上の連続な縮小写像は、唯一の固定点をもちます。

### 証明の概略

1. `exists_fixedPoint_of_fanGlicksberg` で存在。
2. 縮小写像の固定点は高々 1 つ（`ContractingWith.fixedPoint_unique`）。

----

<a id="Tomabechi.Theorem16_25.existsUnique_fixedPoint_and_geometricIterates_of_fanGlicksberg_and_contraction"></a>

## 補題 `existsUnique_fixedPoint_and_geometricIterates_of_fanGlicksberg_and_contraction`

### 式

$$\exists!\,x,\ f(x)=x\ \wedge\ f^n(x_0)\to x\ \wedge\ \operatorname{dist}(f^n(x_0),x)\le\frac{\operatorname{dist}(x_0,f(x_0))\,q^n}{1-q}$$

### Lean のコメント（日本語訳）

> 原文の定理16の存在の節と縮小条件の節を、定量的な反復の評価まで含めて合成する。\(q<1\) のもとで、任意の初期点から Banach の固定点へ収束し、誤差は、初期の残差に比例して \(q^n/(1-q)\) 以下となる。

### 補題の説明

定理16の**縮小条件節の定量版**：固定点の一意存在・反復の収束・誤差の幾何的な評価（事前評価）を 1 つの定理にまとめます。

### 証明の概略

1. コンパクト集合の部分型は完備（距離空間）。
2. Banach の不動点定理（`ContractingWith.exists_fixedPoint`）による反復の収束と、事前評価 `dist_fixedPoint_le`。
3. 一意性は縮小性から。

----

<a id="Tomabechi.Theorem16_25.singletonCorrespondence_hasClosedGraph"></a>

## 補題 `singletonCorrespondence_hasClosedGraph`

### 式

$$f\ \text{連続}\ \Longrightarrow\ \{(x,f(x))\}\ \text{は閉（Hausdorff）}$$

### Lean のコメント（日本語訳）

> 連続な自己写像を 1 元の集合値の対応にしたとき、そのグラフは、Hausdorff な周囲の空間で閉じている。これにより、連続性から Fan–Glicksberg の閉グラフの仮定への移行を明示する。

### 補題の説明

連続写像のグラフは（値の空間が Hausdorff なら）閉集合です。

### 証明の概略

1. グラフ \(=\{p\mid p.2=f(p.1)\}\) は、連続な 2 つの写像の等式の集合で、Hausdorff 空間では閉（`isClosed_eq`）。

----

<a id="Tomabechi.Theorem16_25.singletonCorrespondence_values"></a>

## 補題 `singletonCorrespondence_values`

### 式

$$\{f(x)\}\subseteq K,\ \text{凸},\ \text{非空}$$

### Lean のコメント（日本語訳）

> 1 元の集合値の対応の値は、もとの自己写像が自己写像である限り、非空・凸で、\(K\) に含まれる。

### 補題の説明

1 点集合は凸で非空です。

### 証明の概略

1. `Set.singleton_subset_iff`、`convex_singleton`、`Set.singleton_nonempty`。

----

<a id="Tomabechi.Theorem16_25.inducedMap_of_identityLayerFeedback_is_identity"></a>

## 補題 `inducedMap_of_identityLayerFeedback_is_identity`

### 式

$$f_i=\mathrm{id}\ \Longrightarrow\ F=\mathrm{id}$$

### Lean のコメント（日本語訳）

> 各層のフィードバックを恒等写像に選ぶと、誘導された逆極限の作用素も恒等写像になる。したがって、層の間の可換性や逆系の条件だけでは、縮小性は得られない。

### 補題の説明

**反例（縮小性は逆系の条件から出ない）**：恒等写像は射影と可換で、条件をすべて満たしますが、縮小写像ではありません（任意の点が固定点）。縮小性は別の仮定が必要、ということの形式的な確認です。

### 証明の概略

1. 成分ごとに恒等写像を適用するので、全体も恒等写像（`rfl`）。

----

<a id="Tomabechi.Theorem16_25.LayeredState"></a>

## 構造体 `LayeredState`

### 式

$$\{E_i\}_{i\in I},\ \pi_{\beta\alpha}:E_\alpha\to E_\beta,\ \ \pi_{\alpha\alpha}=\mathrm{id},\ \ \pi_{\gamma\beta}\pi_{\beta\alpha}=\pi_{\gamma\alpha}$$

### Lean のコメント（日本語訳）

> 各層の状態の集合と射影からなる逆系。射影の恒等律と合成律を明示する。

### 定義の説明

**逆系（射影系）**：層の添字 \(I\)（半順序）ごとの状態の型 `State`、層の間の射影 `project`、恒等律 `project_refl`、合成律 `project_comp` をまとめた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.CompatibleFamily"></a>

## 定義 `CompatibleFamily`

### 式

$$\{(x_\alpha)\mid\pi_{\beta\alpha}(x_\alpha)=x_\beta\}$$

### Lean のコメント（日本語訳）

> 逆系の射影と整合する、層別の状態の族。

### 定義の説明

整合する状態の組（逆極限の元）の型です。

### 証明の概略

1. 定義：整合の条件つきの部分型。

----

<a id="Tomabechi.Theorem16_25.SelfState"></a>

## 定義 `SelfState`

### 式

$$\text{履歴}\ h\ \text{に相対する逆極限}$$

### Lean のコメント（日本語訳）

> 履歴 \(h\) に相対する、逆極限（互換な全層の状態）の表現。

### 定義の説明

「自己」の状態を、整合する全層の状態の組として表した型の別名です。

### 証明の概略

1. 定義：`CompatibleFamily sys` の別名。

----

<a id="Tomabechi.Theorem16_25.projectionConstraint"></a>

## 定義 `projectionConstraint`

### 式

$$\{x\mid\pi_{\beta\alpha}(x_\alpha)=x_\beta\}\subset\prod_\alpha E_\alpha$$

### Lean のコメント（日本語訳）

> 積の空間の上の、「\(\alpha\) 層を \(\beta\) 層へ射影すると \(\beta\) 成分に一致する」という、閉の条件の候補。

### 定義の説明

各対 \(\beta\le\alpha\) の整合条件の集合です（`affineProjectionConstraint` の `LayeredState` 版）。

### 証明の概略

1. 定義：`{x | sys.project j.2 (x j.1.2) = x j.1.1}`。

----

<a id="Tomabechi.Theorem16_25.projectionConstraint_isClosed"></a>

## 補題 `projectionConstraint_isClosed`

### 式

$$\pi\ \text{連続},\ E_\alpha\ \text{Hausdorff}\ \Longrightarrow\ \text{整合条件は閉}$$

### Lean のコメント（日本語訳）

> 射影の写像が連続で、各層が Hausdorff なら、逆極限の整合の方程式は閉の条件である。ここでは、射影の連続性を、積の空間へ合成した形で与える。

### 補題の説明

2 つの連続写像の等式の集合は、Hausdorff 空間では閉です。

### 証明の概略

1. `isClosed_eq`（連続写像 2 つの等式）を適用。

----

<a id="Tomabechi.Theorem16_25.inverseLimitSet"></a>

## 定義 `inverseLimitSet`

### 式

$$\varprojlim=\bigcap_j\text{projectionConstraint}_j$$

### Lean のコメント（日本語訳）

> 射影の条件をすべて満たす、積の空間の中の、逆極限の部分集合。

### 定義の説明

逆極限を、整合条件の共通部分として定義します。

### 証明の概略

1. 定義：`⋂ j, projectionConstraint sys j`。

----

<a id="Tomabechi.Theorem16_25.inverseLimit_isCompact_of_closed_constraints"></a>

## 補題 `inverseLimit_isCompact_of_closed_constraints`

### 式

$$\text{整合条件が閉},\ E_\alpha\ \text{コンパクト}\ \Longrightarrow\ \varprojlim\ \text{コンパクト}$$

### Lean のコメント（日本語訳）

> 射影の整合の方程式が閉なら、逆極限は、積の空間の閉部分集合である。各層がコンパクトなら、Tychonoff により積もコンパクトなので、逆極限もコンパクトとなる。

### 補題の説明

積空間（Tychonoff でコンパクト）の閉部分集合はコンパクトです。

### 証明の概略

1. Tychonoff の定理（積空間はコンパクト）。
2. 閉集合の共通部分は閉、コンパクト空間の閉部分集合はコンパクト（`IsClosed.isCompact`）。

----

<a id="Tomabechi.Theorem16_25.inverseLimit_isCompact_of_continuous_projections"></a>

## 補題 `inverseLimit_isCompact_of_continuous_projections`

### 式

$$\pi\ \text{連続}\ \Longrightarrow\ \varprojlim\ \text{コンパクト}$$

### Lean のコメント（日本語訳）

> Tychonoff の定理と閉部分集合の定理による、逆極限のコンパクト性。

### 補題の説明

上の補題の、射影が連続な場合です（連続なら整合条件は閉）。

### 証明の概略

1. `projectionConstraint_isClosed` と `inverseLimit_isCompact_of_closed_constraints`。

----

<a id="Tomabechi.Theorem16_25.finite_layer_compatibility_implies_constraint_fip"></a>

## 補題 `finite_layer_compatibility_implies_constraint_fip`

### 式

$$\text{有限層整合}\ \Longrightarrow\ \bigcap_{j\in s}C_j\neq\varnothing\ (\forall\text{有限}\ s)$$

### Lean のコメント（日本語訳）

> 原文の「任意の有限個の層の族に整合する点がある」という条件を、射影の方程式の族の有限交叉性へ移す。指定されていない層は、非空性から任意に埋めるので、有限個の制約の端点だけが整合していればよい。

### 補題の説明

有限個の整合条件が同時に満たせることを、有限個の層の整合性から示します（関係しない層は、空でないので適当に埋める）。

### 証明の概略

1. 有限個の整合条件 \(s\) が関わる層の有限集合 \(t\) をとり、`hfinite` で \(t\) 上の整合する値 \(z\) を得る。
2. \(t\) 外の層は非空性（`hnonempty`）から任意に選んで、全体の点を作る。

----

<a id="Tomabechi.Theorem16_25.inverseLimit_nonempty_of_closed_finite_compatibility"></a>

## 補題 `inverseLimit_nonempty_of_closed_finite_compatibility`

### 式

$$\text{整合条件が閉},\ \text{有限交叉性}\ \Longrightarrow\ \varprojlim\neq\varnothing$$

### Lean のコメント（日本語訳）

> 各層がコンパクトで、射影の整合の方程式が閉じていて、任意の有限個の方程式が同時に満たせるなら、逆極限は空でない。有限層の族の整合性から、方程式の族の有限整合性を導く仕上げは、層別のモデルの具体的な射影に即した、別の補題として扱う。

### 補題の説明

コンパクト空間の閉集合族が有限交叉性をもてば、全体の共通部分も空でない、という標準的な議論です。

### 証明の概略

1. 射影の整合条件 `projectionConstraint` は各添字で閉集合で、有限交叉性（`hfip`）を満たす。
2. コンパクト空間の閉集合族の有限交叉性から共通部分が非空（`CompactSpace.iInter_nonempty`）。
3. 共通部分の元 \(x\) は、すべての \(\beta\le\alpha\) で \(p(x_\alpha)=x_\beta\) を満たすので `CompatibleFamily` の元（17 行）。

----

<a id="Tomabechi.Theorem16_25.inverseLimit_nonempty_of_continuous_finite_compatibility"></a>

## 補題 `inverseLimit_nonempty_of_continuous_finite_compatibility`

### 式

$$\text{コンパクト Hausdorff 層・連続射影・有限層整合}\ \Longrightarrow\ \varprojlim\neq\varnothing$$

### Lean のコメント（日本語訳）

> 原文のコンパクト Hausdorff の層と連続な射影の設定では、整合条件の閉性は自動である。有限層の整合性から、有限個の方程式の族の同時解を得る部分は、`hfip` に明示される。

### 補題の説明

上の補題の、「閉性」を連続性から得る版で、有限交叉性も `finite_layer_compatibility_implies_constraint_fip` から得ます。

### 証明の概略

1. `projectionConstraint_isClosed` で閉性。
2. `finite_layer_compatibility_implies_constraint_fip` で有限交叉性。
3. `inverseLimit_nonempty_of_closed_finite_compatibility` を適用。

----

<a id="Tomabechi.Theorem16_25.inducedMap"></a>

## 定義 `inducedMap`

### 式

$$F((x_\alpha))=(f_\alpha(x_\alpha))$$

### Lean のコメント（日本語訳）

> 定理16の層別の写像が互換性を保つとき誘導される、逆極限上の自己写像。この定義は固定点の存在を主張せず、写像の構成に必要な可換性だけを入力にする。

### 定義の説明

`inducedAffineInverseLimitMap` の `LayeredState` 版です。

### 証明の概略

1. 成分ごとに \(f_\alpha\) を適用し、可換性で整合性を示す。

----

<a id="Tomabechi.Theorem16_25.inducedMap_continuous"></a>

## 補題 `inducedMap_continuous`

### 式

$$f_\alpha\ \text{連続}\ \Longrightarrow\ F\ \text{連続}$$

### Lean のコメント（日本語訳）

> 連続な層別のフィードバックが互換性を保つなら、誘導される逆極限の写像も連続である。これは、Schauder–Tychonoff を逆極限に適用するのに必要な接続である。

### 補題の説明

成分ごとに連続なので、積位相で連続です。

### 証明の概略

1. `continuous_pi` と部分型の連続性。

----

<a id="Tomabechi.Theorem16_25.inverseLimit_fixedPoint_of_finite_constraint_consistency"></a>

## 補題 `inverseLimit_fixedPoint_of_finite_constraint_consistency`

### 式

$$\text{射影条件と固定点条件の有限部分系が常に同時可解}\ \Longrightarrow\ \exists\ \text{逆極限上の固定点}$$

### Lean のコメント（日本語訳）

> 射影の条件と、各層の固定点の条件の、有限の部分系が、常に同時に解けるなら、逆極限の上に固定点がある。これは、連続性・コンパクト性から自動的には出ず、有限段階の固定点の整合性を、追加の条件とする。

### 補題の説明

固定点定理（Fan–Glicksberg）を使わず、**有限交叉性**だけで固定点の存在を示す版です。ただし「有限個の条件（射影の整合と各層の固定点条件）が同時に解ける」という追加の仮定 `hfinite` が必要です。

### 証明の概略

1. 射影の整合条件（`projectionConstraint`、閉集合）と、各層の固定点条件 \(\{x\mid f_\alpha(x_\alpha)=x_\alpha\}\)（閉集合）を、すべて閉集合として並べる。
2. 有限個の条件が同時に解けること（`hfinite`）から有限交叉性が成り立つ。コンパクト空間の閉集合族の有限交叉性（`CompactSpace.iInter_nonempty` 相当）で共通部分が非空。
3. 共通部分の元が、整合的かつ各層で固定点方程式を満たす（60 行）。

----

<a id="Tomabechi.Theorem16_25.HasFixedPoint"></a>

## 定義 `HasFixedPoint`

### 式

$$\exists x,\ F(x)=x$$

### Lean のコメント（日本語訳）

> 固定した履歴に対する固定点の存在を表す命題。固定点の一意性は含めない。

### 定義の説明

固定点が存在する、という命題です。

### 証明の概略

1. 定義：`∃ x, F x = x`。

----

<a id="Tomabechi.Theorem16_25.SelfRepresentation"></a>

## 構造体 `SelfRepresentation`

### 式

$$\text{relation}\subset\text{Rep}\times S\ \text{閉},\ \text{represent}:S\to\text{Rep}\ \text{連続},\ (\text{represent}\,s,s)\in\text{relation}$$

### Lean のコメント（日本語訳）

> 定理16の自己表象のデータ。コンパクト Hausdorff の表象の空間、閉じた表象関係、連続な表象の写像を保持する。単射性は、原文でも必須の条件ではない。

### 定義の説明

「自己」の状態 \(S\) とその**表象** `Rep`（コンパクト Hausdorff）の関係を束ねた構造体です。表象の写像は連続で、各状態はその表象と閉じた関係で結ばれます。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.HasUniqueFixedPoint"></a>

## 定義 `HasUniqueFixedPoint`

### 式

$$\exists!\,x,\ F(x)=x$$

### Lean のコメント（日本語訳）

> 固定点が一意であること。

### 定義の説明

固定点が唯一であること。

### 証明の概略

1. 定義：`∃! x, F x = x`。

----

<a id="Tomabechi.Theorem16_25.Theorem25SelfProcessLawModel"></a>

## 構造体 `Theorem25SelfProcessLawModel`

### 式

$$\text{baselineJointLaw}_i(h),\ \text{intervenedJointLaw}_i(h,s)\in\mathcal P(R_i\times Y_i^+)$$

### Lean のコメント（日本語訳）

> 原文の 25-A(2) の法則の等式の部分を、固定した主体 \(i\) の全自己過程 \(R_i\) と将来の出力 \(Y_i^+\) の同時確率法則として、25-D のモデルから独立に表す。ここでは、入力の履歴からの候補の独立性を別のフィールドに保持し、層別の \(\Gamma\) との同一視は仮定しない。

### 定義の説明

定理25（無我）の条件 25-A(2) のための「同時法則のモデル」です。履歴 \(h\) のもとでの、基準の同時法則と、候補 \(s\) を介入させたときの同時法則を与えます。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25SelfProcessLawModel.Condition25A2"></a>

## 定義 `Theorem25SelfProcessLawModel.Condition25A2`

### 式

$$\forall h,s:\ \text{intervenedJointLaw}(h,s)=\text{baselineJointLaw}(h)$$

### Lean のコメント（日本語訳）

> 原文の 25-A(2) に対応する、型つきの条件。候補の独立性は、このモデルが渡す抽象的な命題であり、`IndepFun` による確率的な独立性の証明ではない。全履歴・全候補の介入で、\((R_i,Y_i^+)\) の同時法則が不変になる等式を記す。25-D とは別の条件である。

### 定義の説明

「候補の介入をしても、自己過程と将来の出力の同時法則が変わらない」という条件 25-A(2) です。

### 証明の概略

1. 定義：候補独立性の命題と、全履歴・全候補での法則の等式の連言。

----

<a id="Tomabechi.Theorem16_25.Theorem25SelfProcessSCM"></a>

## 構造体 `Theorem25SelfProcessSCM`

### 式

$$U\ \text{外生},\ \ (R,Y^+)=\text{baselineEquation}(h,u),\ \text{intervenedEquation}(h,s,u)$$

### Lean のコメント（日本語訳）

> 原文の 25-A(2) の実際の確率版。外生の確率空間の上に履歴・候補の変数を置き、自己過程の全体と将来の出力の同時の観測を、構造式で与える。候補と履歴の独立性、および介入の前後の可測性は、明示的なモデルの条件として保持する。

### 定義の説明

**構造的因果モデル（SCM）**：外生の確率空間 \(U\) の上に、履歴・候補の変数と、基準・介入後の構造式を置いたモデルです。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25SelfProcessSCM.toLawModel"></a>

## 定義 `Theorem25SelfProcessSCM.toLawModel`

### 式

$$\text{SCM}\ \mapsto\ \text{同時法則のモデル（外生法則の像測度）}$$

### Lean のコメント（日本語訳）

> SCM の構造式を、外生の法則で押し出して、原文の 25-A(2) の同時法則を生成する。

### 定義の説明

SCM から、外生法則の像測度として同時法則のモデルを作ります。

### 証明の概略

1. 定義：`exogenousLaw.map (baselineEquation h)` など。

----

<a id="Tomabechi.Theorem16_25.Theorem25SelfProcessSCM.condition25A2"></a>

## 補題 `Theorem25SelfProcessSCM.condition25A2`

### 式

$$\text{IndepFun}\ \wedge\ \text{介入前後の法則が等しい}\ \Longrightarrow\ \text{Condition25A2}$$

### Lean のコメント（日本語訳）

> 実際の確率変数の独立性と、生成された同時法則の不変性から、25-A(2) を得る。

### 補題の説明

SCM の実際の独立性（`IndepFun`）と法則の不変性の仮定から、条件 25-A(2) が成り立ちます。

### 証明の概略

1. `toLawModel` の定義を展開し、独立性と法則の等式を仮定から渡す。

----

<a id="Tomabechi.Theorem16_25.represented_fixedPoint_of_equivariance"></a>

## 補題 `represented_fixedPoint_of_equivariance`

### 式

$$R(F(s))=F_{\mathrm{Rep}}(R(s)),\ F(s)=s\ \Longrightarrow\ F_{\mathrm{Rep}}(R(s))=R(s)$$

### Lean のコメント（日本語訳）

> 定理16の自己意識の固定点が存在すれば、同変な自己表象も固定点を表す。この移送は、固定点の存在（Schauder の節）とは独立に、同変性だけから従う。

### 補題の説明

自己の固定点 \(s\) の表象 \(R(s)\) は、表象空間での写像 \(F_{\mathrm{Rep}}\) の固定点にもなります（表象の写像が自己写像と可換なら）。

### 証明の概略

1. \(F_{\mathrm{Rep}}(R(s))=R(F(s))=R(s)\)（同変性と \(F(s)=s\)）。関係 \((R(s),s)\in\text{relation}\) は `represents`。

----

<a id="Tomabechi.Theorem16_25.compatible_point_of_closed_finite_constraints"></a>

## 補題 `compatible_point_of_closed_finite_constraints`

### 式

$$X\ \text{コンパクト},\ \text{閉集合族が有限交叉性をもつ}\ \Longrightarrow\ \bigcap_iC_i\neq\varnothing$$

### Lean のコメント（日本語訳）

> コンパクトな空間の上の任意の閉の制約の族について、有限個ごとの整合性から、全体の整合点を得る一般的な補題。上の逆極限の定理は、これを層別の射影の条件に適用している。

### 補題の説明

**コンパクト性と有限交叉性**：コンパクト空間で、閉集合の族の任意の有限個の共通部分が空でないなら、全体の共通部分も空でない。位相論の標準的な事実です。

### 証明の概略

1. Mathlib の `IsCompact.inter_iInter_nonempty`（有限交叉性）などを適用。

----

<a id="Tomabechi.Theorem16_25.hasFixedPoint_of_completeLattice_monotone"></a>

## 補題 `hasFixedPoint_of_completeLattice_monotone`

### 式

$$\text{完備束}\ \alpha,\ f\ \text{単調}\ \Longrightarrow\ \exists x,\ f(x)=x$$

### Lean のコメント（日本語訳）

> Knaster–Tarski による固定点の存在。これは、定理16の局所凸・コンパクトの条件とは別の、順序論的な十分条件（完備束上の単調な写像）であり、定理16の仮定からは自動的には従わない。

### 補題の説明

**Knaster–Tarski の固定点定理**：完備束上の単調写像は、最小の固定点をもちます（Mathlib の `OrderHom.lfp`）。連続性ではなく単調性を使う、別の定式化です。

### 証明の概略

1. `OrderHom.lfp` が固定点（`OrderHom.map_lfp`）。

----

<a id="Tomabechi.Theorem16_25.hasUniqueFixedPoint_of_contraction"></a>

## 補題 `hasUniqueFixedPoint_of_contraction`

### 式

$$\text{完備距離空間},\ f\ \text{が}\ q\text{-縮小}\ \Longrightarrow\ \exists!\,x,\ f(x)=x$$

### Lean のコメント（日本語訳）

> Mathlib の Banach の固定点定理を使う、追加の条件つきの道。完備距離空間の上で縮小性を仮定すると、固定点が存在し、しかも一意になる。これは、原文の定理16に明記された、縮小条件の節の形式化である。

### 補題の説明

**Banach の縮小写像の原理**：完備距離空間で縮小写像は唯一の固定点をもちます。

### 証明の概略

1. `ContractingWith.exists_fixedPoint` と `ContractingWith.fixedPoint_unique`。

----

<a id="Tomabechi.Theorem16_25.theorem16_uniqueRepresentedFixedPoint_of_contraction"></a>

## 定理 `theorem16_uniqueRepresentedFixedPoint_of_contraction`

### 式

$$f\ \text{が}\ K\text{-縮小}\ \Longrightarrow\ \exists!\,s,\ F(s)=s\ \wedge\ F_{\mathrm{Rep}}(R(s))=R(s)\ \wedge\ (R(s),s)\in\text{relation}$$

### Lean のコメント（日本語訳）

> 定理16の縮小条件を加えた、統合の結論。同じ作用素の Banach の固定点が一意であり、その固定点の自己表象も、同変な作用素の固定点となり、表象関係に属する。

### 補題の説明

縮小条件（完備距離）のもとで、自己の固定点が唯一存在し、その表象も固定点で、表象関係に属する、という定理16の統合結論です。

### 証明の概略

1. `hasUniqueFixedPoint_of_contraction` で、縮小写像の固定点 \(s\) の存在と一意性を得る。
2. 表象の固定点性は、同変性 `hequiv` と \(F(s)=s\) から \(F_{\rm Rep}(R(s))=R(s)\)（`rw [← hequiv s, hs]`）。関係への所属は `R.represents s`。
3. 一意性：条件を満たす \(t\) は \(F(t)=t\) を満たすので \(t=s\)（22 行）。

----

<a id="Tomabechi.Theorem16_25.theorem16_banach_point_agrees_with_existing_fixedPoint"></a>

## 補題 `theorem16_banach_point_agrees_with_existing_fixedPoint`

### 式

$$F(s)=s\ \Longrightarrow\ s=\text{Banach 固定点}$$

### Lean のコメント（日本語訳）

> 定理16の Fan–Glicksberg の存在点と、Banach の点との同一性。同じ逆極限型 SC の上の、同じ誘導された写像 \(F\) について、原文の条件から得た任意の固定点は、SC に追加した完備距離と `ContractingWith` の条件のもとで、Banach の固定点に一致する。この橋渡しは、SC 上の `MetricSpace`・`CompleteSpace` と縮小性を、追加の仮定として要求する。

### 補題の説明

位相的な固定点定理で得た固定点と、縮小写像の原理で得る固定点は、縮小性があれば**同じ点**です。

### 証明の概略

1. 縮小写像の固定点の一意性（`ContractingWith.fixedPoint_unique`）。

----

<a id="Tomabechi.Theorem16_25.theorem16_existing_fixedPoint_is_unique_under_contraction"></a>

## 補題 `theorem16_existing_fixedPoint_is_unique_under_contraction`

### 式

$$\exists s,\ F(s)=s\ \Longrightarrow\ \exists!\,s,\ F(s)=s$$

### Lean のコメント（日本語訳）

> 定理16の存在定理の結論を、縮小条件で精密化する。Fan–Glicksberg からすでに得た固定点は Banach の固定点と等しく、したがって唯一である。

### 補題の説明

存在がすでに分かっているとき、縮小性から**唯一性**が加わります。

### 証明の概略

1. `theorem16_banach_point_agrees_with_existing_fixedPoint` を、存在する固定点に適用して、一意性を得る。

----

<a id="Tomabechi.Theorem16_25.contraction_iterates_tendsto_and_rate"></a>

## 補題 `contraction_iterates_tendsto_and_rate`

### 式

$$f^n(x)\to x^\*,\ \ \operatorname{dist}(f^n(x),x^\*)\le K^n\operatorname{dist}(x,x^\*)$$

### Lean のコメント（日本語訳）

> 縮小写像の道の、定量的な反復の収束。Mathlib の固定点 API が与える、事前の誤差の評価と極限に加えて、Lipschitz の評価を各反復に適用して、\(K^n\) の誤差の境界を得る。係数 \(K<1\) と完備距離性は、定理16の無条件の存在の節に対する追加の仮定ではなく、原文が明記する、一意性・反復の収束の条件の節に属する。

### 補題の説明

縮小写像の反復が、固定点へ**幾何級数的**（\(K^n\)）に収束します。

### 証明の概略

1. Banach の定理で反復が固定点に収束（`ContractingWith.tendsto_iterate_fixedPoint`）。
2. 固定点の性質 \(f(x^\*)=x^\*\) と Lipschitz 評価を反復適用して \(\operatorname{dist}(f^n x,x^\*)\le K^n\operatorname{dist}(x,x^\*)\)（帰納法）。

----

<a id="Tomabechi.Theorem16_25.theorem16_fullRepresentedFixedPoint_of_exists_and_contraction"></a>

## 定理 `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction`

### 式

$$\exists!\,s:\ F(s)=s,\ F_{\mathrm{Rep}}(R(s))=R(s),\ (R(s),s)\in\text{relation},\ \operatorname{dist}(F^nx,s)\le K^n\operatorname{dist}(x,s)$$

### Lean のコメント（日本語訳）

> 定理16の固定点の存在の節と縮小条件の節に、自己表象の忠実性・同変性をまとめた、一般的な結論。存在は Fan–Glicksberg などから与え、縮小条件で一意性と、任意の初期値からの定量的な反復の収束を得る。表象作用素の連続性は、原文の条件として保持する。

### 補題の説明

**定理16の完全な結論**：存在（位相的）＋縮小条件 ⇒ 一意性・表象の固定点・任意の初期値からの幾何収束。

### 証明の概略

1. 存在仮定 `hexists` の固定点 \(s\) を取る。Banach の固定点（`ContractingWith.fixedPoint`）と一致する（`theorem16_banach_point_agrees_with_existing_fixedPoint`）ので、他の固定点 \(t\) も \(t=s\)（一意性）。
2. 表象：\(F_{\rm Rep}(R(s))=R(s)\) は同変性と \(F(s)=s\) から、関係への所属は `R.represents s`。
3. 幾何収束：\(n\) についての帰納法で \(d(F^nx,s)\le K^nd(x,s)\)（縮小性 \(d(Fy,Fs)\le Kd(y,s)\)）。これらを `∃!` にまとめる（45 行）。

----

<a id="Tomabechi.Theorem16_25.identity_has_two_fixedPoints"></a>

## 補題 `identity_has_two_fixedPoints`

### 式

$$\mathrm{id}(x)=x,\ \mathrm{id}(y)=y,\ x\ne y$$

### Lean のコメント（日本語訳）

> 固定点の存在だけからは、一意性は導けない。恒等写像は、2 つ以上の元があれば、そのすべてを固定するので、縮小性などの一意性の条件が、別に必要である。

### 補題の説明

**反例**：恒等写像はすべての点が固定点です。

### 証明の概略

1. 2 点 \(x\ne y\) をとれば、どちらも恒等写像の固定点。

----

<a id="Tomabechi.Theorem16_25.identity_not_contracting_of_distinct"></a>

## 補題 `identity_not_contracting_of_distinct`

### 式

$$\exists x\neq y\ \Longrightarrow\ \neg\,\mathrm{ContractingWith}\ K\ \mathrm{id}$$

### Lean のコメント（日本語訳）

> 自明でない距離空間では、恒等写像は縮小写像にならない。したがって、連続な自己写像という定理16の一般の条件から、縮小性は導けない。

### 補題の説明

2 点の距離が縮まらないので、恒等写像は縮小写像ではありません。

### 証明の概略

1. 縮小率 \(K<1\) なら \(\operatorname{dist}(x,y)\le K\operatorname{dist}(x,y)\) で、\(\operatorname{dist}(x,y)>0\) に矛盾。

----

<a id="Tomabechi.Theorem16_25.identity_on_unitInterval_not_contracting"></a>

## 補題 `identity_on_unitInterval_not_contracting`

### 式

$$\neg\,\exists K,\ \mathrm{ContractingWith}\ K\ (\mathrm{id}\ \text{on}\ [0,1])$$

### Lean のコメント（日本語訳）

> 単位区間の恒等写像は、定理16の、空でないコンパクトな凸集合の上の連続な自己写像の条件を満たすが、その自然な距離では縮小写像にならない。コンパクト・凸・連続性から縮小性が出ない例。

### 補題の説明

上の一般的な事実を単位区間 \([0,1]\) に適用した具体例です。

### 証明の概略

1. `identity_not_contracting_of_distinct` を、\(0\ne1\) で適用。

----

<a id="Tomabechi.Theorem16_25.identity_on_unitInterval_nonunique"></a>

## 補題 `identity_on_unitInterval_nonunique`

### 式

$$[0,1]\ \text{コンパクト・凸},\ \mathrm{id}\ \text{連続自己写像},\ \exists x\neq y,\ \mathrm{id}(x)=x\wedge\mathrm{id}(y)=y$$

### Lean のコメント（日本語訳）

> コンパクト性・凸性と連続性だけでは、固定点の一意性は出ない。単位区間の恒等写像はすべての点を固定する、という追加の条件の必要性を示す例。

### 補題の説明

定理16が「存在」しか言わず、「一意性」には縮小条件が要ることの、具体的な反例です。

### 証明の概略

1. \([0,1]\) のコンパクト性（`isCompact_Icc`）、凸性（`convex_Icc`）、連続性、自己写像であること、\(0\ne1\) で 2 つの固定点。

----

<a id="Tomabechi.Theorem16_25.HistoryFixedPoints"></a>

## 構造体 `HistoryFixedPoints`

### 式

$$\forall h,\ \exists!\,\text{固定点 }\text{fp}(h)$$

### Lean のコメント（日本語訳）

> 定理25の第 1 の結論に使う、履歴ごとの固定点の族。各履歴に固定点があり、その固定点が一意であることだけを保持する。

### 定義の説明

履歴 \(h\) ごとの自己写像（フィードバック）の固定点の族と、その存在・一意性の証明を束ねた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfExistenceAndUniqueness"></a>

## 定義 `historyFixedPointsOfExistenceAndUniqueness`

### 式

$$\text{存在}\ +\ \text{一意性}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 履歴ごとの連続な写像について固定点の存在を得て、別に与えた一意性から `HistoryFixedPoints` を組み立てる。存在は Fan–Glicksberg などから、一意性は原文の縮小条件などから供給できるため、両者を 1 つの根拠に混同しない。

### 定義の説明

存在（`hexists`）と一意性（`hunique`）を別々の仮定として受け取り、固定点の族を作ります。

### 証明の概略

1. `Classical.choose`（存在から固定点を選ぶ）と、一意性の仮定でフィールドを埋める（`⟨fp, ...⟩`）。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfContinuousInverseLimitMaps"></a>

## 定義 `historyFixedPointsOfContinuousInverseLimitMaps`

### 式

$$\text{履歴別の逆極限条件}\ +\ F_h\ \text{連続}\ +\ \text{一意性}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 履歴ごとの、原文の型の逆極限の条件と、その逆極限の上に直接定義された連続な写像から、履歴別の固定点の族を構成する。固定点の存在は、各履歴に定理16の Fan–Glicksberg を適用して得る。一意性は独立の条件として受け取るので、原文が縮小条件を置く場合の依存も明示される。

### 定義の説明

各履歴で逆極限の上の連続写像 \(F_h\) に `theorem16_fixedPoint_exists_of_continuous_inverseLimitMap` を適用して存在を得ます。

### 証明の概略

1. 各履歴で `theorem16_fixedPoint_exists_of_continuous_inverseLimitMap`。
2. `historyFixedPointsOfExistenceAndUniqueness` に渡す。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfCarrierContractions"></a>

## 定義 `historyFixedPointsOfCarrierContractions`

### 式

$$\text{各履歴で}\ q_h\text{-縮小}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 各履歴の carrier に固有の完備距離と縮小性から、固定点の族を直接構成する。周囲の `Self` 全体の距離空間の構造は仮定しない。

### 定義の説明

縮小写像の原理だけで固定点の族を作ります（存在も一意性も縮小性から）。

### 証明の概略

1. 各履歴で `ContractingWith.exists_fixedPoint`（Banach）。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfContractions"></a>

## 定義 `historyFixedPointsOfContractions`

### 式

$$\text{carrier}_h\ \text{完備},\ F_h\ \text{縮小}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 履歴別の状態の集合の上で、各フィードバックが縮小写像なら、Banach の定理から `HistoryFixedPoints` を構成する。フィードバックは TCZ の部分型の上で直接与え、周囲の空間全体への延長を要求しない。

### 定義の説明

上の定義の、carrier が完備な部分集合である形です（部分型の上の距離を使う）。

### 証明の概略

1. 完備な部分集合の部分型は完備距離空間。Banach の固定点定理を適用。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfUniqueMonotoneLattice"></a>

## 定義 `historyFixedPointsOfUniqueMonotoneLattice`

### 式

$$\text{完備束}\ +\ F_h\ \text{単調}\ +\ \text{一意性}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 完備束の上の単調な写像から、履歴ごとの固定点の族を構成する、代替の道。Knaster–Tarski が存在を与え、一意性は別の仮定 `hunique` として切り分ける。距離・縮小性は要らないが、定理16のコンパクト凸・連続性の条件とは別の十分条件である。

### 定義の説明

順序論的な道（Knaster–Tarski）で固定点の族を作ります。

### 証明の概略

1. 各履歴 \(h\) の固定点を、単調写像の最小不動点 `lfp`（Knaster–Tarski）として取る。
2. 固定点性は `map_lfp`、一意性は仮定 `hunique`（任意の固定点は最小不動点に一致）から。担体は全体 `True`（23 行）。

----

<a id="Tomabechi.Theorem16_25.no_common_fixed_point_of_history_separation"></a>

## 補題 `no_common_fixed_point_of_history_separation`

### 式

$$\text{fp}(h_1)\neq\text{fp}(h_2)\ \Longrightarrow\ \neg\,\exists s,\ F_{h_1}(s)=s\wedge F_{h_2}(s)=s$$

### Lean のコメント（日本語訳）

> 定理25の第 1 の結論（履歴別の一意な固定点と、条件 25-A(1) のもとで、共通の固定点はない）。

### 補題の説明

**定理25（無我）第 1 結論の核心**：履歴ごとの固定点が一意で、2 つの履歴で固定点が異なる（25-A(1)）なら、**すべての履歴に共通する固定点はありません**。共通の固定点 \(s\) があれば、各履歴の（唯一の）固定点と一致して、両者が等しくなってしまうからです。

### 証明の概略

1. 共通の固定点 \(s\) があると仮定する。
2. 各履歴の固定点の一意性で \(s=\text{fp}(h_1)\)、\(s=\text{fp}(h_2)\)。よって \(\text{fp}(h_1)=\text{fp}(h_2)\)、分離の仮定に矛盾。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_uniqueMonotoneLattice"></a>

## 定理 `theorem25_firstConclusion_of_uniqueMonotoneLattice`

### 式

$$\text{Knaster–Tarski 版の定理25第 1 結論}$$

### Lean のコメント（日本語訳）

> Knaster–Tarski の存在と、仮定した一意性を、履歴ごとに使い、定理25の第 1 の結論へ接続する。25-A(1) に対応する、履歴の固定点の分離があれば、共通の固定点はない。

### 補題の説明

順序論的な道で作った固定点の族に、`no_common_fixed_point_of_history_separation` を適用した定理です。

### 証明の概略

1. 履歴 \(h_1,h_2\) の両方の固定点になる \(s\) があるとする。
2. `hunique` で \(s=\mathrm{lfp}(\text{feedback}_{h_1})\) かつ \(s=\mathrm{lfp}(\text{feedback}_{h_2})\)。
3. よって 2 つの lfp が等しくなり、履歴分離の仮定 `hsep` に矛盾（17 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_historyContractions"></a>

## 定理 `theorem25_firstConclusion_of_historyContractions`

### 式

$$\text{各履歴で縮小}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定点なし}$$

### Lean のコメント（日本語訳）

> 各履歴の縮小写像の条件から、Banach の固定点をとり、条件 25-A(1) の履歴の分離を使って、定理25の第 1 の結論を得る、接続の定理。縮小性は、定理16の条件の節・定理25の前提に明記される。完備距離の構造は、定理16の位相的な存在の条件とは別に要る。

### 補題の説明

縮小写像の道での定理25 第 1 結論です。

### 証明の概略

1. `historyFixedPointsOfContractions` と `no_common_fixed_point_of_history_separation`。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfExistingPointsAndContractions"></a>

## 定義 `historyFixedPointsOfExistingPointsAndContractions`

### 式

$$\text{存在（定理16）}\ +\ \text{縮小（一意性のみ）}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 定理16のコンパクト凸の固定点の存在を先に使い、縮小性は一意性にだけ使う。Banach の存在定理を再度使う方法と異なり、履歴別の carrier の完備性は要求しない。

### 定義の説明

存在は位相的な固定点定理（Fan–Glicksberg）から、一意性だけ縮小性から得ます。carrier の完備性は要りません。

### 証明の概略

1. `hexists` で存在、縮小写像の固定点の一意性（`ContractingWith.fixedPoint_unique` 型）で一意性。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_theorem16ExistenceAndContraction"></a>

## 定理 `theorem25_firstConclusion_of_theorem16ExistenceAndContraction`

### 式

$$\text{定理16の存在}\ +\ \text{縮小一意性}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定点なし}$$

### Lean のコメント（日本語訳）

> 定理16の各履歴の固定点の存在（例：Fan–Glicksberg）と、縮小による一意性を合わせて、25.1 へ進む。25-A(1) に相当する、履歴の間の固定点の分離を加えれば、共通の固定点はない。逆極限の carrier の完備距離性は要求せず、縮小性から存在も導かず、定理16の存在点を使う。

### 補題の説明

**定理16→定理25 の主要な接続**：存在（位相）＋一意性（縮小）で履歴別の固定点の族を作り、分離から共通の固定点がないことを導きます。

### 証明の概略

1. `historyFixedPointsOfExistingPointsAndContractions` と `no_common_fixed_point_of_history_separation`。

----

<a id="Tomabechi.Theorem16_25.historyAffineInverseLimitSet"></a>

## 定義 `historyAffineInverseLimitSet`

### 式

$$\varprojlim K(h)$$

### Lean のコメント（日本語訳）

> 履歴ごとに異なる層の TCZ から作る、逆極限の部分集合。

### 定義の説明

履歴 \(h\) ごとに TCZ \(K(h)_i\) が変わる場合の逆極限です。

### 証明の概略

1. 定義：`affineInverseLimitSet E (K h) project`。

----

<a id="Tomabechi.Theorem16_25.historyInducedAffineInverseLimitMap"></a>

## 定義 `historyInducedAffineInverseLimitMap`

### 式

$$F_h=(f_{h,i})_i$$

### Lean のコメント（日本語訳）

> 射影と可換な、履歴別の層のフィードバックが、逆極限の上に誘導する写像。

### 定義の説明

履歴 \(h\) ごとのフィードバックが誘導する逆極限の自己写像です。

### 証明の概略

1. `inducedAffineInverseLimitMap` を各履歴に適用。

----

<a id="Tomabechi.Theorem16_25.Theorem16HistoryLayerSystem"></a>

## 構造体 `Theorem16HistoryLayerSystem`

### 式

$$\text{(層の ambient と射影系は共通)}\ +\ \text{TCZ}\ K(h)_i\ +\ \text{フィードバック}\ f_{h,i}$$

### Lean のコメント（日本語訳）

> 定理16の、層ごとの原文の条件を、履歴の族として束ねる。同一の層の ambient と射影系を使い、TCZ・フィードバックだけが履歴に依存する設定。

### 定義の説明

定理16の仮定（有向・各層の TCZ はコンパクト凸で非空・射影の合成則・TCZ の像の包含・TCZ 上での連続性・フィードバックは連続で射影と可換 等）を、履歴ごとに束ねた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem16HistoryLayerSystem.fixedPointExists"></a>

## 補題 `Theorem16HistoryLayerSystem.fixedPointExists`

### 式

$$\forall h,\ \exists x\in\varprojlim K(h),\ F_h(x)=x$$

### Lean のコメント（日本語訳）

> 履歴ごとに、原文 §7 の逆極限の固定点の存在定理を適用する。

### 補題の説明

構造体の仮定から、各履歴の逆極限上の固定点の存在を得る補題です。

### 証明の概略

1. 各履歴で `theorem16_fixedPoint_exists_of_originalLayerConditions`。

----

<a id="Tomabechi.Theorem16_25.Theorem16HistoryLayerSystem.fullRepresentedFixedPointConclusion"></a>

## 定理 `Theorem16HistoryLayerSystem.fullRepresentedFixedPointConclusion`

### 式

$$\text{履歴別の}\ \S7\ \text{層データ}\ +\ \text{距離・縮小・表象}\ \Longrightarrow\ \text{固定点の存在・一意・表象・幾何誤差}$$

### Lean のコメント（日本語訳）

> 履歴別の原文 §7 の層データから得た固定点の存在を、表象・縮小・幾何的な誤差の評価までつなぐ、定理16の完全な固定点の結論。距離・縮小性・表象のデータは、原文の追加条件の節として受け取る。

### 補題の説明

履歴別の層システムについての、定理16の完全な結論です（`theorem16_fullRepresentedFixedPoint_of_exists_and_contraction` を適用）。

### 証明の概略

1. `fixedPointExists` で存在。
2. `theorem16_fullRepresentedFixedPoint_of_exists_and_contraction` を適用。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfTheorem16LayerSystem"></a>

## 定義 `historyFixedPointsOfTheorem16LayerSystem`

### 式

$$\text{層システム}\ +\ \text{ambient 距離での縮小}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 定理16の原文の条件から、履歴ごとの固定点を得て、縮小性は一意性にだけ使う、履歴の族。Banach の存在定理を使わないため、逆極限の完備距離性は要求しない。この実装の `ContractingWith` は、共通の Pi の ambient の距離を、逆極限の部分型に制限して使う。原文の「SC 上だけの完備距離」より強い、ambient の距離の拡張可能性を含むため、モデルの接続の条件として明記する。

### 定義の説明

層システムから、固定点の族を作ります。距離は積空間 ambient（\(\prod E_i\)）の距離を部分型に制限したものです（論文の「逆極限 SC 上だけの距離」より強い仮定）。

### 証明の概略

1. `fixedPointExists` で存在、縮小性（`hcontract`）で一意性。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_originalTheorem16HistorySystem"></a>

## 定理 `theorem25_firstConclusion_of_originalTheorem16HistorySystem`

### 式

$$\text{層システム}\ +\ \text{縮小}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定状態なし}$$

### Lean のコメント（日本語訳）

> 履歴別の TCZ・連続で整合なフィードバックから、定理16の固定点を得たあと、縮小性による一意性と、25-A(1) の固定点の分離を用いて、25.1 の共通の固定状態の不存在へ接続する。さらに、縮小の計量が Pi の ambient 全体へ延長できることを、要求する実装版である。

### 補題の説明

`historyFixedPointsOfTheorem16LayerSystem` を使った、定理25 第 1 結論です。

### 証明の概略

1. `historyFixedPointsOfTheorem16LayerSystem` と `no_common_fixed_point_of_history_separation`。

----

<a id="Tomabechi.Theorem16_25.historyFixedPointsOfTheorem16LayerSystemWithSCMetric"></a>

## 定義 `historyFixedPointsOfTheorem16LayerSystemWithSCMetric`

### 式

$$\text{各履歴の逆極限 SC に距離}\ \Longrightarrow\ \text{HistoryFixedPoints}$$

### Lean のコメント（日本語訳）

> 原文どおり、各履歴の逆極限 SC そのものに距離を置く、固定点の族。Pi の ambient 全体への距離の拡張を要求せず、SC 上の完備距離と縮小性から、一意性を使う。存在は、定理16の局所凸の位相的な固定点定理から得るため、ここでは Banach の存在を重ねて使わない。

### 定義の説明

論文の設定（距離は逆極限 \(SC\) 自身に置く）に沿った固定点の族です。

### 証明の概略

1. 存在：`fixedPointExists`。一意性：SC 上の縮小性。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_originalTheorem16HistorySystemWithSCMetric"></a>

## 定理 `theorem25_firstConclusion_of_originalTheorem16HistorySystemWithSCMetric`

### 式

$$\text{SC 上の距離・縮小}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定状態なし}$$

### Lean のコメント（日本語訳）

> 履歴ごとの SC に直接与えた完備距離・縮小性と、25-A(1) の分離を用いて 25.1 を導く。これが、Pi の ambient の距離の拡張を避ける、原文の条件に沿った接続である。

### 補題の説明

論文の条件に最も近い、定理16→25 の接続です。

### 証明の概略

1. `historyFixedPointsOfTheorem16LayerSystemWithSCMetric` と `no_common_fixed_point_of_history_separation`。

----

<a id="Tomabechi.Theorem16_25.theorem25_fullFirstConclusion_of_originalTheorem16HistorySystemWithSCMetric"></a>

## 定理 `theorem25_fullFirstConclusion_of_originalTheorem16HistorySystemWithSCMetric`

### 式

$$\exists h_1,h_2:\ \text{fp}(h_1)\neq\text{fp}(h_2)\ \Longrightarrow\ \text{全履歴に共通の固定点はない}$$

### Lean のコメント（日本語訳）

> 定理16の履歴別の逆極限の存在と、SC 上の完備距離の縮小条件を使い、25-A(1) の「ある 2 つの履歴で固定点が異なる」から、25.1 の全履歴に共通の固定点の不存在を導く。25-A(2) の確率法則の条件は、この結論の依存に含めない。

### 補題の説明

上の定理の、「ある二履歴で固定点が異なる」という存在の形の分離仮定を使った版です（25-A(2) は使わない）。

### 証明の概略

1. 異なる固定点をもつ 2 履歴 \(h_1,h_2\) を取り出し、上の定理を適用する。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_inverseLimitContractions"></a>

## 定理 `theorem25_firstConclusion_of_inverseLimitContractions`

### 式

$$\text{逆極限の完備性・縮小性}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定状態なし}$$

### Lean のコメント（日本語訳）

> 定理16の逆極限のフィードバックを、履歴別の Banach の固定点の族へ直接渡して、定理25 (25.1) を得る。各逆極限の完備性・縮小性と、25-A(1) の固定点の分離は、明示的な仮定であり、定理16の局所凸コンパクトの固定点の存在条件から自動的には導かない。

### 補題の説明

逆極限上の縮小写像（Banach）の道で 25.1 を得ます。

### 証明の概略

1. `historyFixedPointsOfContractions`（逆極限の carrier 版）と `no_common_fixed_point_of_history_separation`。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_compactInverseLimitContractions"></a>

## 定理 `theorem25_firstConclusion_of_compactInverseLimitContractions`

### 式

$$\text{逆極限がコンパクト}\ \Longrightarrow\ \text{完備性は導ける}$$

### Lean のコメント（日本語訳）

> 履歴別の逆極限が、採用した距離の位相でコンパクトなら、その完備性は別の仮定にせず導ける。定理16のコンパクトな逆極限を距離化して、定理25へ接続するときに使う補正版。距離の位相が、定理16で用いた積位相と一致することは、モデル側の接続の条件として必要である。

### 補題の説明

コンパクトな距離空間は完備です。上の定理の「完備性」の仮定を、コンパクト性から導く版です。

### 証明の概略

1. コンパクトな距離空間は完備（`IsCompact.isComplete`）。上の定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_historyGradientEulerSteps"></a>

## 定理 `theorem25_firstConclusion_of_historyGradientEulerSteps`

### 式

$$\text{履歴別の強凸ポテンシャルの Euler 勾配更新（縮小）}\ +\ \text{25-A(1)}\ \Longrightarrow\ \text{共通の固定点なし}$$

### Lean のコメント（日本語訳）

> 定理21型の強凸ポテンシャルから、履歴ごとに Euler の勾配更新を作り、勾配の Lipschitz 条件とステップ幅の条件で縮小性を得て、定理25の第 1 の結論へ接続する。Euler の離散化・共通の完備距離・履歴別の強凸性は、明示的なモデルの条件であり、定理16の原文だけから得られる結果ではない。

### 補題の説明

**定理21 → 定理16 → 定理25 の具体的な接続**：履歴ごとの強凸ポテンシャルの勾配降下（`gradientEulerStep_contracting` で縮小写像）を履歴別のフィードバックとして、固定点が履歴ごとに異なれば共通の固定点がないことを導きます。

### 証明の概略

1. 各履歴で `gradientEulerStep_contracting` により Euler の更新は縮小写像。
2. `theorem25_firstConclusion_of_historyContractions` を適用する。

----

<a id="Tomabechi.Theorem16_25.Theorem25CausalModel"></a>

## 構造体 `Theorem25CausalModel`

### 式

$$\text{intervenedLaw}(d,a,h,s),\ \text{baselineLaw}(d,a,h)\in\text{Law}(d,a)$$

### Lean のコメント（日本語訳）

> 定理25-D を、因果モデルの抽象的な「同時法則」として表すデータ。`intervenedLaw` は do(Σ=s) のあとの \((\Gamma_{d,\alpha},Y^+_{d,\alpha})\) の同時法則、`baselineLaw` は候補の自性を介入しない基準の法則を表す。実際の確率モデルでは、これらを、対応する積の空間の上の確率測度として具体化する。

### 定義の説明

**因果モデルの抽象的な核**：存在 \(d\)・層 \(a\)・履歴 \(h\)・候補 \(s\) に対して、候補に介入した後の法則と、介入しない基準の法則を与えます（法則の型は何でもよい）。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25CausalModel.hasNonRedundantCausalEffect"></a>

## 定義 `Theorem25CausalModel.hasNonRedundantCausalEffect`

### 式

$$\exists h,\ \text{intervenedLaw}(d,a,h,s)\neq\text{baselineLaw}(d,a,h)$$

### Lean のコメント（日本語訳）

> ある介入で、関係状態と将来の出力の同時法則が、基準の法則から変化することを、本形式化における「非冗長な因果効果」とする。

### 定義の説明

候補 \(s\) に介入すると（関係状態と将来出力の）法則が**変わる**、という意味での「関係状態を超える因果効果」です。

### 証明の概略

1. 定義：ある履歴で介入後の法則が基準の法則と異なる、という述語。

----

<a id="Tomabechi.Theorem16_25.Theorem25CausalModel.hasAtman"></a>

## 定義 `Theorem25CausalModel.hasAtman`

### 式

$$\exists s,\ \text{(独立・固定的な個体化)}\wedge\text{hasNonRedundantCausalEffect}$$

### Lean のコメント（日本語訳）

> 操作的な \(\mathrm{Atman}(d,\alpha)\)：独立で固定的な個体化と、関係状態を超える非冗長な因果効果を同時にもつ、候補の自性が存在すること。

### 定義の説明

**操作的な「アートマン（常一主宰の自己）」**：候補の自性が存在して、(i) 履歴から独立で固定的に個体化され、(ii) 関係状態を超える因果効果をもつ、という述語です。定理25（無我）は、これが成り立たないことを示します。

### 証明の概略

1. 定義：述語（存在量化）。

----

<a id="Tomabechi.Theorem16_25.Theorem25CausalModel.FunctionallyComplete"></a>

## 定義 `Theorem25CausalModel.FunctionallyComplete`

### 式

$$\forall d,a,h,s,\ \text{intervenedLaw}(d,a,h,s)=\text{baselineLaw}(d,a,h)$$

### Lean のコメント（日本語訳）

> 条件 25-D の操作的な形式。任意の存在・層・履歴・候補の介入で、同時法則が不変である。

### 定義の説明

**機能的完備性（条件 25-D）**：どんな候補に介入しても、関係状態と将来出力の法則が変わらない（候補の自性が余計な因果効果をもたない）。

### 証明の概略

1. 定義：全称命題。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_functionalCompleteness"></a>

## 定理 `theorem25_secondConclusion_of_functionalCompleteness`

### 式

$$\text{FunctionallyComplete}\ \Longrightarrow\ \forall d,a,\ \neg\,\text{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 定理25の第 2 の結論の因果の核：条件 25-D の法則の不変性のもとでは、どの存在・層にも、関係状態を超える因果効果をもつ固定的な自性はない。25-B（全層のプロファイル）と 25-C（関係の網）は、モデルの意味づけ・存在の構造を与えるが、この含意には使われない。原文 §14.5 も 25-D を決定的な条件と明記する。これは、25-B/C から 25-D を導いた結果ではなく、25-D を明示的な仮定とした結論である。

### 補題の説明

**定理25 第 2 結論（無我）の核心**：25-D（介入しても法則が変わらない）を仮定すれば、「関係状態を超える因果効果をもつ自性（アートマン）」は存在しません。**25-D 自体は仮定**であり、導いてはいません。

### 証明の概略

1. `hasAtman` の定義：独立・固定的な個体化と `hasNonRedundantCausalEffect`（ある履歴で介入後の法則が基準と異なる）の組。
2. 仮定から得た Atman の証人 \(s\) の因果効果の履歴 \(h\)（介入後の法則 \(\ne\) 基準の法則）を取り出す。
3. 25-D（機能的完備性）は、すべての \(d,a,h,s\) で法則が等しいと述べるので、矛盾（11 行）。

----

<a id="Tomabechi.Theorem16_25.Theorem25ProbabilityCausalModel"></a>

## 構造体 `Theorem25ProbabilityCausalModel`

### 式

$$\text{baselineJointLaw},\ \text{intervenedJointLaw}\in\mathcal P(\Gamma_{d,a}\times Y^+_{d,a})$$

### Lean のコメント（日本語訳）

> \((\Gamma_{d,\alpha},Y^+_{d,\alpha})\) の同時分布を、実際の確率測度で与える、定理25の因果モデル。基準の法則と do(Σ=s) の介入後の法則を、それぞれ積の可測空間の上の一般の確率測度として保持する。分布の族の生成（構造方程式・介入の意味論）が、条件 25-D を満たすかどうかは、別のモデルの検証である。

### 定義の説明

上の抽象的な因果モデルの、確率測度版です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25StructuralCausalModel"></a>

## 構造体 `Theorem25StructuralCausalModel`

### 式

$$\Gamma=\text{stateEquation}(h,u),\ \ Y^+=\text{outputEquation}(h,u,s)$$

### Lean のコメント（日本語訳）

> 構造因果モデルの簡約された表現。外生の法則は履歴 \(h\) に依存せず、do(H=h) は構造方程式の入力 \(h\) を固定する。`stateEquation` は関係状態 \(\Gamma\)、`outputEquation` は将来の出力を与える。基準の過程は `defaultCandidate` を用い、do(Σ=s) では出力方程式へ \(s\) を代入する。ここでは、H・Σ への介入の意味論を、この置換の規則で定義し、グラフ手術型の一般の SCM までは主張しない。

### 定義の説明

**構造因果モデル（SCM）の簡約版**：外生変数 \(U\)、履歴 \(h\)、候補 \(s\) から、関係状態 \(\Gamma\) と将来出力 \(Y^+\) を、構造方程式で定めます。介入は「入力を置き換える」ことで定義します。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25StructuralCausalModel.toProbabilityCausalModel"></a>

## 定義 `Theorem25StructuralCausalModel.toProbabilityCausalModel`

### 式

$$\text{法則}=(\text{構造方程式})_\*\,(\text{外生法則})$$

### Lean のコメント（日本語訳）

> 構造方程式と外生変数の法則の pushforward で、基準・介入後の同時分布を生成する。

### 定義の説明

SCM から、外生法則の像測度として、基準・介入後の同時分布を作ります。

### 証明の概略

1. 定義：`exogenousLaw.map (fun u => (stateEquation .., outputEquation ..))`。

----

<a id="Tomabechi.Theorem16_25.Theorem25StructuralCausalModel.baselineJointLaw_apply"></a>

## 補題 `Theorem25StructuralCausalModel.baselineJointLaw_apply`

### 式

$$\mathbb P_{\text{baseline}}(A)=\mathbb P_U\bigl((\Gamma,Y^+)(u,\text{default})\in A\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生成された基準の法則の値は、外生法則による集合の逆像の確率です（像測度の定義の確認）。

### 証明の概略

1. 像測度の定義 `Measure.map_apply`（可測集合 \(A\)）。

----

<a id="Tomabechi.Theorem16_25.Theorem25StructuralCausalModel.intervenedJointLaw_apply"></a>

## 補題 `Theorem25StructuralCausalModel.intervenedJointLaw_apply`

### 式

$$\mathbb P_{\text{do}(\Sigma=s)}(A)=\mathbb P_U\bigl((\Gamma,Y^+)(u,s)\in A\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入後の法則の値の公式です。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Theorem16_25.Theorem25ProbabilityCausalModel.toCausalModel"></a>

## 定義 `Theorem25ProbabilityCausalModel.toCausalModel`

### 式

$$\text{確率測度のモデル}\ \to\ \text{抽象的な因果コア}$$

### Lean のコメント（日本語訳）

> 確率測度のモデルを、法則の型に依存しない因果コアへ忘却する。

### 定義の説明

確率測度で与えたモデルを、抽象的な `Theorem25CausalModel` として見直します（法則の型を `ProbabilityMeasure` にする）。

### 証明の概略

1. 定義：フィールドの対応づけ。

----

<a id="Tomabechi.Theorem16_25.theorem25_functionalCompleteness_projects_to_representation"></a>

## 補題 `theorem25_functionalCompleteness_projects_to_representation`

### 式

$$\text{25-D}\ \Longrightarrow\ (\text{encode}\,\Gamma,Y^+)\ \text{の法則も介入で不変}$$

### Lean のコメント（日本語訳）

> 25-D の同時法則の不変性は、関係状態 \(\Gamma\) から可測に読み出せる表現 \(R\) へ射影しても保たれる。これは、\(R\) を \(\Gamma\) の関数として表せる場合に限り、25-D から 25-A(2) 型の法則の不変性へ縮約する橋である。

### 補題の説明

25-D（\((\Gamma,Y^+)\) の法則不変）から、\(\Gamma\) を表現 \(R=\text{encode}(\Gamma)\) に写した \((R,Y^+)\) の法則不変が出ます（同じ写像で押し出せば等式は保たれる）。

### 証明の概略

1. 介入後と基準の法則が等しい（25-D）ので、同じ写像 `fun z => (encode z.1, z.2)` による像測度も等しい（`congrArg`）。

----

<a id="Tomabechi.Theorem16_25.Theorem25ProbabilityCausalModel.RepresentationSliceLawInvariant"></a>

## 定義 `Theorem25ProbabilityCausalModel.RepresentationSliceLawInvariant`

### 式

$$(\text{encode}\,\Gamma,Y^+)\ \text{の介入後と基準の法則が等しい}$$

### Lean のコメント（日本語訳）

> 25-D の法則モデルの 1 つの存在・層で、\(\Gamma\) を表現の空間へ写したあとの介入法則の不変性。これは原文の 25-A(2) そのものではない。原文の \(R_i=(\mathrm{Self}_i,\mathrm{Ego}_i,\mathrm{TCZ}_i)\) の全体が、1 つの \(\Gamma_{d,a}\) から復元されるときに限る、単一層の射影のモデルである。

### 定義の説明

**1 つの層での表現の法則の不変性**です。論文の 25-A(2)（自己過程全体 \(R_i\)）そのものではなく、その単一層の射影版です。

### 証明の概略

1. 定義：全履歴・全候補での像測度の等式。

----

<a id="Tomabechi.Theorem16_25.theorem25_representationSliceLawInvariant_of_functionalCompleteness"></a>

## 補題 `theorem25_representationSliceLawInvariant_of_functionalCompleteness`

### 式

$$\text{全索引で 25-D}\ \Longrightarrow\ \text{表現の一層の法則の不変性}$$

### Lean のコメント（日本語訳）

> 全索引の 25-D は、各層 \(\Gamma\) から表現の変数への符号化が与えられれば、その 1 層の射影の介入法則の不変性を含意する。原文の 25-A(2) との同一視には、自己過程の全体を復元する、追加の符号化の条件が要る。

### 補題の説明

25-D から、表現の 1 層の法則不変性を導きます。

### 証明の概略

1. 25-D（全添字・全介入で \((\Gamma,Y^+)\) の同時法則が不変）の仮定 `hcomplete` を取る。
2. 両辺の確率測度を、符号化 \((\gamma,y)\mapsto(\mathrm{encode}(\gamma),y)\) で押し出しても等しい（`congrArg`）。これが表象スライスの法則の不変性（16 行）。

----

<a id="Tomabechi.Theorem16_25.probabilityMeasure_eq_of_measurable_leftInverse_pushforward"></a>

## 補題 `probabilityMeasure_eq_of_measurable_leftInverse_pushforward`

### 式

$$\text{decode}\circ\text{encode}=\mathrm{id},\ \text{encode}_\*\mu=\text{encode}_\*\nu\ \Longrightarrow\ \mu=\nu$$

### Lean のコメント（日本語訳）

> 可測な符号化に、可測な左逆があれば、その符号化のあとの確率法則の等式から、もとの法則の等式を復元できる。したがって、\(\Gamma\leftrightarrow R\) が可測同型で、同じ全添字・介入で不変性が成り立つ場合は、\((R,Y^+)\) の法則の条件と \((\Gamma,Y^+)\) の法則の条件は同値になる。

### 補題の説明

符号化 \(e\) に可測な左逆 \(d\) があれば、符号化後の法則が等しい 2 つの測度は、もとから等しい（\(\mu=d_\*e_\*\mu\)）。

### 証明の概略

1. \(\mu=(d\circ e)_\*\mu=d_\*(e_\*\mu)=d_\*(e_\*\nu)=\nu\)（`Measure.map_map`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_globalCompleteness_of_allEncodedRepresentationLaws"></a>

## 補題 `theorem25_globalCompleteness_of_allEncodedRepresentationLaws`

### 式

$$R\ \text{が}\ \Gamma\ \text{を可測に完全復元},\ (R,Y^+)\ \text{の法則不変}\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> \(R\) が \(\Gamma\) を可測に完全に復元し、\((R,Y^+)\) の法則の不変性が、全存在・全層にわたって成り立つなら、関係的な 25-D が従う。これは、25-A(2) をそのまま使う定理ではなく、原文にない全索引への拡張の条件を明示した、逆向きのブリッジである。

### 補題の説明

25-A(2) 型（表現の法則不変）から 25-D へ**逆向きに**橋をかける補題です。表現が完全復元可能であることと全索引での不変性が条件です。

### 証明の概略

1. `probabilityMeasure_eq_of_measurable_leftInverse_pushforward` を、\((\Gamma,Y^+)\) の法則と \((R,Y^+)\) の符号化に適用。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel"></a>

## 構造体 `Theorem25RandomizedStructuralCausalModel`

### 式

$$\Sigma:U\to\text{Candidate},\ \ \Sigma\perp\Gamma\ \ (\text{各 do}(H=h)\ \text{スライス})$$

### Lean のコメント（日本語訳）

> 候補 \(\Sigma\) を、実際の外生の確率変数として持つ SCM。独立性は、各 `do(H=h)` のスライスで、\(\Sigma\) と関係状態 \(\Gamma\) の間に `IndepFun` として課し、候補の値 \(s\) の個体化は、\(s\) が正の確率で現れることとして表す。\(H\) 自体の確率分布・大域的な \(\Sigma\perp H\) は、別にモデル化が必要である。

### 定義の説明

候補 \(\Sigma\) が確率変数（ランダム）として外生空間にあるタイプの SCM です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel.candidateHasPositiveMass"></a>

## 定義 `Theorem25RandomizedStructuralCausalModel.candidateHasPositiveMass`

### 式

$$\mathbb P(\Sigma=s)>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

候補の値 \(s\) が正の確率で現れる（個体化される）という述語です。

### 証明の概略

1. 定義：`0 < μ {u | candidateVariable u = s}` の形。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel.independentAcrossHistories"></a>

## 定義 `Theorem25RandomizedStructuralCausalModel.independentAcrossHistories`

### 式

$$\forall h,\ \Sigma\perp\Gamma[h]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各履歴のスライスで候補 \(\Sigma\) と関係状態 \(\Gamma\) が独立、という述語です。

### 証明の概略

1. 定義：各履歴で `IndepFun`。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM"></a>

## 構造体 `Theorem25GlobalHistorySCM`

### 式

$$H:U\to\text{History},\ \ \Sigma\perp(H,\Gamma[H])$$

### Lean のコメント（日本語訳）

> 大域の履歴 \(H\) を、外生の空間の上の確率変数として保持する SCM。候補 \(\Sigma\) の \(\Sigma\perp(H,\Gamma[H])\) を明示する一方、外生法則は存在・層ごとに与える。全存在・層で単一の法則を使う、原文寄りの型は `Theorem25SharedGlobalHistorySCM` である。

### 定義の説明

履歴 \(H\) 自体も確率変数として持つ SCM です（外生法則は存在・層ごと）。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistorySCM"></a>

## 構造体 `Theorem25SharedGlobalHistorySCM`

### 式

$$\text{1 つの確率空間・1 つの外生法則を全存在・層で共有}$$

### Lean のコメント（日本語訳）

> 1 つの確率空間・1 つの外生法則のもとで、全存在・層が共有する、大域履歴の SCM。`Theorem25GlobalHistorySCM` の、索引ごとの法則より、原文のモデル全体の \(H\) に忠実である。

### 定義の説明

上の SCM の、外生法則を全索引で共有する版（論文のモデルに忠実）です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistorySCM.toIndexed"></a>

## 定義 `Theorem25SharedGlobalHistorySCM.toIndexed`

### 式

$$\text{共有法則 SCM}\ \to\ \text{索引ごとの法則の SCM}$$

### Lean のコメント（日本語訳）

> 共通の法則の SCM を、法則を索引ごとに複製する、既存の一般の API へ埋め込む。

### 定義の説明

共有法則版を、索引ごとに同じ法則を複製した版（`Theorem25GlobalHistorySCM`）として見直します。

### 証明の概略

1. 定義：外生法則を全索引で同じ値にする。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints"></a>

## 定義 `Theorem25SharedGlobalHistorySCM.ofHistoryFixedPoints`

### 式

$$\Gamma=\text{stateCode}(\text{fp}(H)),\quad Y^+=\text{outputCode}(\text{fp}(H))$$

### Lean のコメント（日本語訳）

> 定理16の履歴別の固定点の族を、自己過程の状態・将来の出力の生成元とする、共有法則の SCM。`stateCode` は固定点から関係状態 \(\Gamma\) を、`outputCode` はその固定点から現行の過程の出力を読む。したがって do(Σ=s) は候補の変数だけを置換し、固定点に由来する状態・出力は変えない。候補の独立性と可測性は明示的な入力であり、定理16の固定点の条件から導いたとはしない。

### 定義の説明

**定理16 と 定理25 の接続**：履歴 \(H\) の固定点（自己）から関係状態と出力を決める SCM を構成します。候補への介入は固定点由来の部分を変えません。

### 証明の概略

1. `globalHistory` の固定点を `stateCode`/`outputCode` で読み、SCM のフィールドを定義する（独立性・可測性は仮定を渡す）。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistorySCM.ofTheorem16LayerSystem"></a>

## 定義 `Theorem25SharedGlobalHistorySCM.ofTheorem16LayerSystem`

### 式

$$\text{定理16の層システム}\ \to\ \text{固定点族}\ \to\ \text{共有法則 SCM}$$

### Lean のコメント（日本語訳）

> 原文の条件を満たす定理16の層のデータから、固定点の族を生成し、その固定点を状態・出力の符号化する、25 の共有法則の SCM へ渡す。SC 上の距離・完備性・縮小性と、確率的な候補の独立性は、明示的な入力である。出力の符号化が候補の値を参照しない条件では 25-D が成立するが、これは定理16だけから出る性質ではない。

### 定義の説明

定理16の履歴別の層システム（距離・縮小性つき）から固定点の族 `historyFixedPointsOfTheorem16LayerSystemWithSCMetric` を作り、`ofHistoryFixedPoints` に渡します。

### 証明の概略

1. `historyFixedPointsOfTheorem16LayerSystemWithSCMetric` で固定点の族。
2. `ofHistoryFixedPoints` を適用。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.toShared"></a>

## 定義 `Theorem25GlobalHistorySCM.toShared`

### 式

$$\text{外生法則がすべて等しい}\ \Longrightarrow\ \text{共有法則 SCM}$$

### Lean のコメント（日本語訳）

> 旧 API の外生法則がすべて等しい場合、その共通の値を取り出して、共有法則の SCM へ移す。

### 定義の説明

索引別の法則が実は全部同じなら、共有法則の版に移せます。

### 証明の概略

1. 共通の法則 `μ` を取り出してフィールドを書き換える。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.candidateHasPositiveMass"></a>

## 定義 `Theorem25GlobalHistorySCM.candidateHasPositiveMass`

### 式

$$\mathbb P(\Sigma_{d,a}=s)>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

候補の値が正の確率で現れる、という述語です。

### 証明の概略

1. 定義：正の測度。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.toProbabilityCausalModel"></a>

## 定義 `Theorem25GlobalHistorySCM.toProbabilityCausalModel`

### 式

$$\text{大域履歴 SCM}\ \mapsto\ (\text{baselineJointLaw},\ \text{intervenedJointLaw})$$

### Lean のコメント（日本語訳）

> 大域の履歴の変数と、履歴別の構造方程式をもつ SCM から、`do(H=h)` と `do(Σ=s)` の意味論を区別した、同時法則を生成する。基準の法則では、\(\Sigma\) を自然な変数のまま残す。

### 定義の説明

基準の法則では候補 \(\Sigma\) を自然な確率変数のまま、介入後は \(\Sigma=s\) に置換して、それぞれの同時法則を作ります。

### 証明の概略

1. 定義：像測度（基準は `candidateVariable u`、介入後は `s` を代入）。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.baselineJointLaw_apply"></a>

## 補題 `Theorem25GlobalHistorySCM.baselineJointLaw_apply`

### 式

$$\mathbb P_{\text{baseline}}(A)=\mathbb P_U\bigl((\Gamma,Y^+)(h,u,\Sigma(u))\in A\bigr)$$

### Lean のコメント（日本語訳）

> AEMeasurable の条件のもとで、生成された法則が、外生法則の通常の pushforward の適用則を満たす。

### 補題の説明

像測度の定義の確認です（基準の法則）。

### 証明の概略

1. `Measure.map_apply`（`AEMeasurable` 版）。

----

<a id="Tomabechi.Theorem16_25.Theorem25GlobalHistorySCM.intervenedJointLaw_apply"></a>

## 補題 `Theorem25GlobalHistorySCM.intervenedJointLaw_apply`

### 式

$$\mathbb P_{\text{do}(\Sigma=s)}(A)=\mathbb P_U\bigl((\Gamma,Y^+)(h,u,s)\in A\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

介入後の法則の値の公式です。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Theorem16_25.theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance"></a>

## 補題 `theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance`

### 式

$$Y^+(h,u,\Sigma(u))=Y^+(h,u,s)\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> 大域の履歴を含む SCM でも、候補の値を自然な値から置換して、出力方程式が変わらなければ、25-D が成立し、定理25の第 2 の結論に至る。履歴・関係状態との確率的な独立性は、Atman の述語へ渡す。

### 補題の説明

出力方程式が候補に依存しない（**候補の無関係性**）なら、介入しても法則は変わらず、25-D が成り立ちます。

### 証明の概略

1. 介入後と基準の写像が一致するので、像測度も等しい（`funext` と `congrArg`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance"></a>

## 補題 `theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance`

### 式

$$\text{外生法則の零集合を除いて}\ Y^+(h,u,\Sigma(u))=Y^+(h,u,s)\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> 候補の値による出力方程式の変化が、外生法則の零集合の上だけなら、生成される \((\Gamma,Y^+)\) の介入法則は、基準の法則と一致する。点ごとの不変性を、a.e. の条件へ弱めた版。

### 補題の説明

上の補題の、「ほとんど至るところ」版です。

### 証明の概略

1. 2 つの写像が a.e. 等しければ、像測度も等しい（`Measure.map_congr`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry"></a>

## 補題 `theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry`

### 式

$$\exists\tau\ (\text{測度保存}):\ (\Gamma,Y^+)(h,\tau u,s)=(\Gamma,Y^+)(h,u,\Sigma(u))\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> 大域履歴の SCM の候補の介入が、外生法則を保つ再パラメータ化で基準の過程へ移るなら、同時の pushforward 法則として 25-D が成立する。出力の点ごとの候補の非干渉を仮定しない対称性の版。

### 補題の説明

候補が出力に影響しても（点ごとには）、外生変数の**測度保存な変換 \(\tau\)** で介入後の過程が基準の過程に写るなら、**法則としては**不変です。

### 証明の概略

1. 像測度の関係：\(\tau\) が測度を保つので \(((\Gamma,Y^+)\circ\tau)_\*\mu=(\Gamma,Y^+)_\*\mu\)。
2. \((\Gamma,Y^+)(h,\tau u,s)=(\Gamma,Y^+)(h,u,\Sigma(u))\) と合わせて、介入後の法則＝基準の法則。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_globalHistorySCM_candidateIrrelevance"></a>

## 定理 `theorem25_secondConclusion_of_globalHistorySCM_candidateIrrelevance`

### 式

$$\text{候補の無関係性}\ \Longrightarrow\ \forall d,a,\ \neg\,\text{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

大域履歴の SCM で出力方程式が候補に依存しなければ、25-D が成り立ち、定理25の第 2 の結論（Atman は存在しない）が従います。

### 証明の概略

1. `theorem25_globalHistorySCM_functionalCompleteness_of_candidateIrrelevance` と `theorem25_secondConclusion_of_functionalCompleteness`。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance"></a>

## 定理 `theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance`

### 式

$$\text{a.e. の候補の無関係性}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> a.e. の構造方程式の不変性から 25-D を得て、定理25の第 2 の結論へ接続する。

### 補題の説明

上の定理の、ほとんど至るところ版です。

### 証明の概略

1. `..._of_ae_candidateIrrelevance` と `theorem25_secondConclusion_of_functionalCompleteness`。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance"></a>

## 定理 `theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance`

### 式

$$\text{共有法則 SCM}\ +\ \text{a.e. の候補の無関係性}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 単一の大域の外生法則をもつ SCM で、候補の出力が外生法則のもとで a.e. 不変なら、25.2 が成立する。

### 補題の説明

共有法則の SCM（論文のモデルに忠実）での 25.2 です。

### 証明の概略

1. `toIndexed` で索引別の版に直して、上の定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_historyFixedPointGeneratedSCM"></a>

## 定理 `theorem25_secondConclusion_of_historyFixedPointGeneratedSCM`

### 式

$$\text{固定点から状態・出力を生成する SCM}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 固定点から状態と出力を生成する SCM では 25-D が成立し、条件 25-A(2) と、大域履歴・固定点に由来する状態からの候補の独立性のもとで、Atman の候補は存在しない。

### 補題の説明

**定理16 の固定点を使った SCM（`ofHistoryFixedPoints`）では、候補への介入は出力を変えない**ので 25-D が自動的に成り立ち、Atman は存在しません。ただし、候補の独立性・可測性は入力として仮定します。

### 証明の概略

1. `ofHistoryFixedPoints` の出力は候補を参照しないので候補の無関係性が成立。
2. `theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance` を適用。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel"></a>

## 定義 `Theorem25RandomizedStructuralCausalModel.toProbabilityCausalModel`

### 式

$$\text{ランダム候補 SCM}\ \mapsto\ \text{同時法則}$$

### Lean のコメント（日本語訳）

> ランダムな \(\Sigma\) を残した基準の方程式と、`do(Σ=s)` で \(\Sigma\) だけを定数に置換した方程式から、同時法則を pushforward で生成する。Atman の候補の独立性・正の確率の条件も、因果モデルへ渡す。

### 定義の説明

ランダム候補 SCM から確率因果モデルを作ります（基準は \(\Sigma\) を確率変数のまま、介入後は定数に置換）。

### 証明の概略

1. 定義：像測度（基準は `candidateVariable u`、介入後は `s`）。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel.baselineJointLaw_apply"></a>

## 補題 `Theorem25RandomizedStructuralCausalModel.baselineJointLaw_apply`

### 式

$$\mathbb P_{\text{baseline}}(A)=\mathbb P_U((\Gamma,Y^+)(h,u,\Sigma(u))\in A)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

像測度の定義の確認です。

### 証明の概略

1. `Measure.map_apply`。

----

<a id="Tomabechi.Theorem16_25.Theorem25RandomizedStructuralCausalModel.intervenedJointLaw_apply"></a>

## 補題 `Theorem25RandomizedStructuralCausalModel.intervenedJointLaw_apply`

### 式

$$\mathbb P_{\text{do}(\Sigma=s)}(A)=\mathbb P_U((\Gamma,Y^+)(h,u,s)\in A)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

像測度の定義の確認です（介入後）。

### 証明の概略

1. `Measure.map_apply`。

----

<a id="Tomabechi.Theorem16_25.theorem25_randomizedStructuralFunctionalCompleteness_of_candidateIrrelevance"></a>

## 補題 `theorem25_randomizedStructuralFunctionalCompleteness_of_candidateIrrelevance`

### 式

$$\text{候補が出力方程式に無関係}\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> ランダムな候補 \(\Sigma\) が、出力方程式から因果的に無関係なら、構造方程式から 25-D の同時法則の不変性が従う。候補の独立性だけでなく、この出力の不変性の条件が必要な、追加のモデルの仮定である。

### 補題の説明

ランダム候補 SCM でも、**候補が出力に影響しないという条件**（独立性だけでは足りない）があれば 25-D が成り立ちます。

### 証明の概略

1. 介入後と基準の写像が等しいので像測度も等しい。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_randomizedStructuralCandidateIrrelevance"></a>

## 定理 `theorem25_secondConclusion_of_randomizedStructuralCandidateIrrelevance`

### 式

$$\Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> ランダムな候補の構造方程式が 25-D を満たす場合の、(25.2) への接続。

### 補題の説明

上の補題から定理25 第 2 結論へ接続します。

### 証明の概略

1. `theorem25_secondConclusion_of_functionalCompleteness`。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_probabilityFunctionalCompleteness"></a>

## 定理 `theorem25_secondConclusion_of_probabilityFunctionalCompleteness`

### 式

$$\text{確率測度で表した 25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 積の空間の上の確率測度で表した条件 25-D から、定理25 (25.2) を得る。

### 補題の説明

確率因果モデルを抽象的な因果コアに忘却して、`theorem25_secondConclusion_of_functionalCompleteness` を適用します。

### 証明の概略

1. `toCausalModel` と `theorem25_secondConclusion_of_functionalCompleteness`。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_structuralFunctionalCompleteness"></a>

## 定理 `theorem25_secondConclusion_of_structuralFunctionalCompleteness`

### 式

$$\text{構造方程式から生成した法則が 25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 構造方程式で生成した基準・介入の法則が 25-D を満たすなら、統計モデルへの忘却を介して、定理25 (25.2) を得る。25-D そのものは構造方程式から自動的には出ず、ここでは、生成された pushforward の法則について明示的に仮定する。

### 補題の説明

SCM 版の 25.2 です。**25-D は仮定**です。

### 証明の概略

1. `theorem25_secondConclusion_of_probabilityFunctionalCompleteness`。

----

<a id="Tomabechi.Theorem16_25.theorem25_structuralFunctionalCompleteness_of_measurePreservingSymmetry"></a>

## 補題 `theorem25_structuralFunctionalCompleteness_of_measurePreservingSymmetry`

### 式

$$\tau\ \text{測度保存},\ (\Gamma,Y^+)(\tau u,s)=(\Gamma,Y^+)(u,\text{default})\ \Longrightarrow\ \text{25-D}$$

### Lean のコメント（日本語訳）

> 各候補の介入を基準の過程へ移す、外生変数の測度保存な対称性があれば、構造方程式の同時の pushforward 法則から 25-D を導く。候補の値ごとの出力の一致は要求せず、外生の座標の測度保存な再パラメータ化を認める。

### 補題の説明

簡約 SCM 版の、測度保存の対称性による 25-D の導出です。

### 証明の概略

1. 像測度の等式：\(\tau\) が測度を保つことと写像の一致。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_structuralMeasurePreservingSymmetry"></a>

## 定理 `theorem25_secondConclusion_of_structuralMeasurePreservingSymmetry`

### 式

$$\text{測度保存の対称性}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 外生変数の測度保存な対称性から 25-D を得て、定理25の第 2 の結論へ接続する。

### 補題の説明

上の補題と `theorem25_secondConclusion_of_functionalCompleteness` を組み合わせます。

### 証明の概略

1. 上の補題と第 2 結論の核。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel"></a>

## 構造体 `Theorem25PresenceRelationModel`

### 式

$$\text{profile}(d,h,a)\in\text{Rep}\cup\{\text{none}\},\ \ \text{topMarker},\ \ \text{relationEdge}(h,d,a,r,e,b)$$

### Lean のコメント（日本語訳）

> 条件 25-B/C のデータ。`profile` は、存在ごとの層別の表現（`none` は不在の記号）を表す。上位の層は、全存在・履歴に共通する 1 元の表現 `topMarker` をもつ。`relationEdge` は、逆の役割のラベルを含む、層の間の有向の記述で、射影した存在のグラフは連結で、各存在が他者と関係する。

### 定義の説明

**25-B（存在プロファイル）・25-C（関係網）のモデル**：存在ごとの層別の表現、最上位の共通の記号（空）、存在どうしの関係の辺（役割ラベルつき）を束ねます。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel.horizontalRelationAdjacent"></a>

## 定義 `Theorem25PresenceRelationModel.horizontalRelationAdjacent`

### 式

$$d\sim e\ \Longleftrightarrow\ \exists a,b,r:\ \text{relationEdge}(h,d,a,r,e,b)$$

### Lean のコメント（日本語訳）

> 原文の 25-C2 の、関係の辺を存在の添字へ射影した、基礎となる無向グラフの 1 歩。

### 定義の説明

層を無視して、存在 \(d\) と \(e\) の間に関係の辺があるかどうかの隣接関係です。

### 証明の概略

1. 定義：存在量化と \(d\ne e\)。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel.directedStep_iff_horizontalAdjacency"></a>

## 補題 `Theorem25PresenceRelationModel.directedStep_iff_horizontalAdjacency`

### 式

$$\text{有向の辺}\ \Longleftrightarrow\ \text{射影した無向の辺}$$

### Lean のコメント（日本語訳）

> 25-C1 の逆の役割の対により、無向射影グラフの辺は、両向きの有向の関係の辺と同値になる。

### 補題の説明

逆の役割の辺が必ずあるので、有向グラフを無向に射影しても情報は失われません。

### 証明の概略

1. （→）有向の辺から射影の辺。（←）逆役割の条件（25-C1）で有向の辺を得る。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel.relationGraphConnected_iff_horizontalConnected"></a>

## 補題 `Theorem25PresenceRelationModel.relationGraphConnected_iff_horizontalConnected`

### 式

$$\text{有向の ReflTransGen}\ \Longleftrightarrow\ \text{無向射影の ReflTransGen}$$

### Lean のコメント（日本語訳）

> 現在の有向の `ReflTransGen` の表現と、原文の 25-C2 の基礎となる無向グラフの連結性は、25-C1 の逆の役割の条件のもとで同値である。よって、構造体の連結性のフィールドは、原文より強い別の仮定を、密かに置いてはいない。

### 補題の説明

**形式化の忠実性の確認**：構造体が課す連結性（有向）は、論文の連結性（無向）と同値で、強い仮定になっていません。

### 証明の概略

1. `directedStep_iff_horizontalAdjacency` で 1 歩ごとの同値を示し、`ReflTransGen` の帰納法で全体の同値。

----

<a id="Tomabechi.Theorem16_25.Theorem25IntegratedModel"></a>

## 構造体 `Theorem25IntegratedModel`

### 式

$$\text{確率的因果法則}\ +\ \text{25-B のプロファイル}\ +\ \text{25-C の関係網}$$

### Lean のコメント（日本語訳）

> 確率的な因果法則・25-B の存在プロファイル・25-C の関係網を、同じ存在・層・履歴の添字と、同じ層の状態の型 `Gamma` で束ねる。これにより、各分野が、同一のモデルの添字を共有する。

### 定義の説明

25-A〜D のモデルを 1 つに統合した構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25IntegratedModel.ObservationEventsMeasurable"></a>

## 定義 `Theorem25IntegratedModel.ObservationEventsMeasurable`

### 式

$$\text{基準の観測一致のイベントは可測}$$

### Lean のコメント（日本語訳）

> 25-B/C の基準の観測の一致を、確率事象として読むために必要な、全一致のイベントの可測性。構造体の旧来の `...Coherent` のフィールドは、測度の値 1 だけを課すため、一般のインスタンスでは、この追加の命題なしに「確率 1」と解釈しない。

### 定義の説明

「測度が 1」を「確率 1」と読むための可測性の条件です。

### 証明の概略

1. 定義：各イベントが可測集合、という命題。

----

<a id="Tomabechi.Theorem16_25.Theorem25RelationalState"></a>

## 構造体 `Theorem25RelationalState`

### 式

$$\Gamma=(\text{全層プロファイル},\ \text{縦の包摂近傍},\ \text{その層の入出関係辺})$$

### Lean のコメント（日本語訳）

> 原文の 25-C3 の関係的な状態 \(\Gamma=(\text{全層のプロファイル},\text{縦の包摂の近傍},\text{当該の層の入出の関係の辺})\)。

### 定義の説明

関係的な状態 \(\Gamma\) を具体的に定める構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel.relationalState"></a>

## 定義 `Theorem25PresenceRelationModel.relationalState`

### 式

$$\Gamma(d,h,a)$$

### Lean のコメント（日本語訳）

> 25-B/C の構造から、存在 \(d\)・履歴 \(h\)・注目する層 \(a\) の \(\Gamma\) を組み立てる。縦の近傍は現前し、\(a\) と順序が比較できる層、入出の辺は \(a\) を端点にもつ関係の辺として定義する。

### 定義の説明

25-B/C のデータから関係的な状態を組み立てる関数です。

### 証明の概略

1. 定義：プロファイル・近傍・辺をモデルから取り出す。

----

<a id="Tomabechi.Theorem16_25.Theorem25PresenceRelationModel.relationalState_incidentRelation_iff"></a>

## 補題 `Theorem25PresenceRelationModel.relationalState_incidentRelation_iff`

### 式

$$\Gamma.\text{incidentRelation}\ \Longleftrightarrow\ \text{relationEdge}$$

### Lean のコメント（日本語訳）

> \(\Gamma\) の `incidentRelation` は、その基準の存在・層から出る関係の辺を、正確に復元する。

### 補題の説明

作った \(\Gamma\) から関係の辺が正確に読み取れます。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem16_25.Theorem25C3IntegratedModel"></a>

## 構造体 `Theorem25C3IntegratedModel`

### 式

$$\Gamma\ \text{が 25-C3 の全層プロファイル・縦近傍・入出関係辺を確率 1 で符号化}$$

### Lean のコメント（日本語訳）

> 統合モデルを強め、確率変数 \(\Gamma\) そのものが、原文の 25-C3 の全層のプロファイル・縦の近傍・入出の関係の辺を、確率 1 で符号化することを要求する。

### 定義の説明

統合モデルに、「\(\Gamma\) が 25-C3 の内容を確率 1 で正確に表す」という条件を加えた構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25C3IntegratedModel.ObservationEventsMeasurable"></a>

## 定義 `Theorem25C3IntegratedModel.ObservationEventsMeasurable`

### 式

$$\text{完全な}\ \Gamma\ \text{観測の一致のイベントは可測}$$

### Lean のコメント（日本語訳）

> 完全な \(\Gamma\) の観測の確率 1 の整合を、確率事象として読む、追加の可測性の条件。

### 定義の説明

C3 版の可測性の条件です。

### 証明の概略

1. 定義：可測性の命題。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistoryC3Model"></a>

## 構造体 `Theorem25SharedGlobalHistoryC3Model`

### 式

$$\text{共有法則の履歴 SCM}\ +\ \text{25-B/C3}\ +\ \text{確率 1 の観測整合}$$

### Lean のコメント（日本語訳）

> 単一の外生法則を共有する履歴 SCM に、25-B/C3 の構造と、確率 1 の観測の整合を、同じ生成法則の上で束ねる。索引別の SCM の版と異なり、全存在・層の法則の共有が型に残る。

### 定義の説明

共有法則の SCM に 25-B/C3 を統合した構造体です。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25SharedGlobalHistoryC3Model.ObservationEventsMeasurable"></a>

## 定義 `Theorem25SharedGlobalHistoryC3Model.ObservationEventsMeasurable`

### 式

$$\text{共有法則 C3 モデルの全基準観測イベントは可測}$$

### Lean のコメント（日本語訳）

> 共有法則の C3 モデルの、全基準観測のイベントの可測性。

### 定義の説明

共有法則版の可測性の条件です。

### 証明の概略

1. 定義：可測性の命題。

----

<a id="Tomabechi.Theorem16_25.Theorem25MeasuredC3IntegratedModel"></a>

## 構造体 `Theorem25MeasuredC3IntegratedModel`

### 式

$$\text{C3 統合モデル}\ +\ \text{イベントの可測性}$$

### Lean のコメント（日本語訳）

> B/C3 の観測の一致を、本当に確率 1 の条件として使う、イベントの可測性つきの統合モデル。

### 定義の説明

可測性を加えた C3 統合モデルです。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25MeasuredSharedGlobalHistoryC3Model"></a>

## 構造体 `Theorem25MeasuredSharedGlobalHistoryC3Model`

### 式

$$\text{共有法則 C3 モデル}\ +\ \text{可測性}$$

### Lean のコメント（日本語訳）

> 共有する大域履歴 SCM の B/C3 の観測の整合を、確率論的に使うための、可測な版のラッパー。

### 定義の説明

可測性を加えた、共有法則の C3 モデルです。

### 証明の概略

1. 構造体なので証明はない。

----

<a id="Tomabechi.Theorem16_25.Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints"></a>

## 定義 `Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints`

### 式

$$\text{履歴別の固定点が}\ \Gamma\ \text{を符号化}\ \Longrightarrow\ \text{共有 C3 モデル}$$

### Lean のコメント（日本語訳）

> 実際の履歴別の固定点が、25-C3 の関係的な状態を符号化する場合、固定点から生成する SCM を、共有する大域履歴の C3 モデルへ持ち上げる。固定点と関係網の一致は、モデルの対応の仮定として受け取り、候補の独立性・可測性も入力し、これらを定理16の位相的な条件から導いたとはしない。

### 定義の説明

固定点から作った SCM を、共有法則の C3 モデルとして使えるように持ち上げます（対応の仮定を受け取る）。

### 証明の概略

1. 各フィールドに、固定点から作った SCM と仮定（対応・可測性・独立性）を渡す。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_sharedGlobalHistoryC3Model"></a>

## 定理 `theorem25_secondConclusion_of_sharedGlobalHistoryC3Model`

### 式

$$\text{共有法則 C3 モデル}\ +\ \text{25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 共通の法則を保つ、25-B/C3 の統合型でも、25-D なら、定理25の第 2 の結論が従う。

### 補題の説明

統合型（共有法則・C3）でも、25-D を仮定すれば Atman は存在しません。

### 証明の概略

1. 共有履歴 C3 モデルの SCM を確率因果モデルとして取り出し（`M.scm.toIndexed.toProbabilityCausalModel`）、25-D の仮定 `hcomplete` を渡す。
2. 確率因果モデル版の第 2 結論 `theorem25_secondConclusion_of_probabilityFunctionalCompleteness` を適用する（確率因果モデルの `toCausalModel` についての Atman 不存在）（16 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_measurableC3IntegratedModel"></a>

## 定理 `theorem25_secondConclusion_of_measurableC3IntegratedModel`

### 式

$$\text{可測な B/C3 統合モデル}\ +\ \text{25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 可測な B/C3 の統合モデルでも、25-D から定理25の第 2 の結論が従う。可測なイベントの仮定により、入力モデルの確率 1 の観測の整合を、任意の集合の上の測度の値と取り違えない。

### 補題の説明

可測性を備えた統合モデル版の 25.2 です。

### 証明の概略

1. 因果コアの定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model"></a>

## 定理 `theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model`

### 式

$$\text{可測な共有法則 B/C3}\ +\ \text{25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 可測な共有法則の B/C3 モデルの上で、25-D から定理25の第 2 の結論を得る。

### 補題の説明

共有法則・可測版の 25.2 です。

### 証明の概略

1. 因果コアの定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference"></a>

## 定理 `theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`

### 式

$$\text{候補の介入が出力を a.e. 変えない}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 可測な共有法則の C3 モデルで、候補の介入が将来の出力を a.e. 変えず、関係状態も構造方程式で固定されているなら、25-D を pushforward の法則から導いて、定理25の第 2 の結論へ接続する。

### 補題の説明

25-D を**仮定せず**、「候補が出力を（ほとんど至るところ）変えない」という構造的な条件から導く版です。

### 証明の概略

1. 出力が候補に a.e. で干渉しない（`houtput`）という仮定を、共有履歴 SCM の版 `theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance` に渡す（`M.model.scm` に適用）。
2. その定理の内部で、a.e. 非干渉から 25-D が従い、第 2 結論が得られる（19 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_measurePreservingSymmetry"></a>

## 定理 `theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_measurePreservingSymmetry`

### 式

$$\text{測度保存の対称性}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 25-B/C3 の観測の整合を備えた共有の履歴 SCM で、候補の介入ごとの外生の測度保存な対称性から 25-D を導き、25.2 の全存在・全層の結論まで接続する。C3 の確率 1 の整合の条件を保ったまま、点ごとの候補の非干渉より一般的な、ノイズの再配置を許す。

### 補題の説明

測度保存の対称性（ノイズの再配置）による版です。

### 証明の概略

1. `theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry` と第 2 結論の定理。

----

<a id="Tomabechi.Theorem16_25.theorem25_measurePreservingSymmetry_preservesSharedC3Observations"></a>

## 補題 `theorem25_measurePreservingSymmetry_preservesSharedC3Observations`

### 式

$$\text{介入後も、プロファイル・関係辺・完全 }\Gamma\text{ の観測は確率 1 で保たれる}$$

### Lean のコメント（日本語訳）

> 測度保存の対称性からの 25-D は、25.2 だけでなく、基準のモデルで確率 1 だった 25-B/C3 の観測のすべてを、候補の介入のあとも保存する。法則の不変性と、プロファイル・関係の辺・完全な \(\Gamma\) の状態の観測を、同じ共有履歴 C3 モデルの上で、まとめて返す。

### 補題の説明

介入しても（25-D により）法則が変わらないので、基準で確率 1 だった観測の整合は、介入後も確率 1 です。

### 証明の概略

1. 25-D（法則の不変性）で、介入後の測度の値が基準の測度の値に等しい。基準で確率 1 の集合は介入後も確率 1。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_historyFixedPointGeneratedMeasuredC3Model"></a>

## 定理 `theorem25_secondConclusion_of_historyFixedPointGeneratedMeasuredC3Model`

### 式

$$\text{固定点から生成した可測 C3 SCM}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 履歴別の固定点を C3 の関係状態へ符号化して生成した、可測な SCM では、候補の介入が出力を変えない、構成上の性質から 25-D が成立し、定理25の第 2 の結論へ至る。

### 補題の説明

定理16の固定点から作った C3 モデルでは、構成上、候補が出力を変えないので 25-D が成り立ち、Atman は存在しません。

### 証明の概略

1. `ofHistoryFixedPoints` の構成から候補の無関係性が成り立つ。第 2 結論の定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_Theorem16LayerSystemGeneratedMeasuredC3Model"></a>

## 定理 `theorem25_secondConclusion_of_Theorem16LayerSystemGeneratedMeasuredC3Model`

### 式

$$\S7\ \text{層系}\ \to\ \text{固定点族}\ \to\ \text{測度付き C3 モデル}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> §7 の層系から固定点の族を生成し、SC 上の縮小による一意性を経て、測度つきの C3 モデルと候補の非干渉の条件から 25.2 まで接続する、合成の定理。コードの一致・独立性・可測性・候補の非干渉は、位相的な定理16の条件から導かず、モデルの対応の条件として明示する。

### 補題の説明

定理16の層系から定理25 第 2 結論までを 1 つにつないだ、最も長い合成です。**多くの接続条件は仮定**です。

### 証明の概略

1. `historyFixedPointsOfTheorem16LayerSystemWithSCMetric` で固定点族。
2. `Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints` で C3 モデル。
3. `theorem25_secondConclusion_of_historyFixedPointGeneratedMeasuredC3Model` を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_c3IntegratedModel"></a>

## 定理 `theorem25_secondConclusion_of_c3IntegratedModel`

### 式

$$\text{C3 統合モデル}\ +\ \text{25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 完全な \(\Gamma\) の符号化を含むモデルでも、25-D から定理25 (25.2) が従う。

### 補題の説明

C3 統合モデル版の 25.2 です。

### 証明の概略

1. 因果コアの定理を適用。

----

<a id="Tomabechi.Theorem16_25.theorem16_25_conditionalProofCore"></a>

## 定理 `theorem16_25_conditionalProofCore`

### 式

$$25.1:\ \text{共通の固定点なし}\ \wedge\ 25.2:\ \forall d,a,\ \neg\,\text{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 定理16・25の最終的な論理の核を、1 つの入口に束ねる。`fixedPoints` は定理16の層系から得た、履歴別の固定点の族（存在は定理16、一意性は縮小条件）、`hhistorySensitive` は 25-A(1)、`hA2` は実確率 SCM の上の 25-A(2)、`h25D` は全存在・全層の 25-D である。結論は、25.1 と、C3 統合モデルの上の 25.2。25-A(2) は原文の条件として入力するが、この 2 つの結論の論理的な証明には使用しない。`SelfProcessSCM` と `C3IntegratedModel` の間の、無条件の同一視も仮定しない。

### 補題の説明

**定理16→25 の最終まとめ（条件付き）**：履歴別の固定点族・25-A(1)（履歴によって固定点が違う）・25-D（機能的完備性）から、25.1（共通固定点なし）と 25.2（Atman なし）を同時に結論します。**条件付き**の証明であり、各条件はモデルで検証が必要な仮定です。

### 証明の概略

1. 25.1：履歴感度 `hhistorySensitive`（\(h_1,h_2\) で固定点が異なる）を取る。全履歴共通の固定状態があれば、\(h_1,h_2\) の両方の固定点になるので、`no_common_fixed_point_of_history_separation` に矛盾する。
2. 25.2：`theorem25_secondConclusion_of_c3IntegratedModel`（因果コア。25-D が仮定）を C3 統合モデルに適用する（35 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_secondConclusion_of_integratedModel"></a>

## 定理 `theorem25_secondConclusion_of_integratedModel`

### 式

$$\text{25-B/C 統合モデル}\ +\ \text{25-D}\ \Longrightarrow\ \neg\,\text{hasAtman}$$

### Lean のコメント（日本語訳）

> 25-B、25-C の層別・関係の構造を備えた統合モデルで、条件 25-D を仮定すれば、原文の定理25 (25.2) を得る。証明の因果の部分が実際に使う前提は 25-D である。

### 補題の説明

**25-B/C は意味づけを与えるだけで、結論に使う前提は 25-D のみ**であることを明示した定理です。

### 証明の概略

1. 因果コアの定理（25-D のみを使う）を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_profileCoherent_afterIntervention"></a>

## 補題 `theorem25_profileCoherent_afterIntervention`

### 式

$$\text{25-D}\ \Longrightarrow\ \mathbb P_{\text{do}(\Sigma=s)}(\text{profile}=\text{presence.profile})=1$$

### Lean のコメント（日本語訳）

> 条件 25-D の全同時法則の不変性により、基準の分布で確率 1 だった、層別のプロファイルの観測的な一致は、任意の候補の自性への介入のあとにも、確率 1 で保たれる。

### 補題の説明

介入しても法則が変わらないので、プロファイルの観測の整合も確率 1 のままです。

### 証明の概略

1. 介入後の法則が基準の法則に等しいので、測度の値（確率 1）も等しい。

----

<a id="Tomabechi.Theorem16_25.theorem25_relationsCoherent_afterIntervention"></a>

## 補題 `theorem25_relationsCoherent_afterIntervention`

### 式

$$\text{25-D}\ \Longrightarrow\ \mathbb P_{\text{do}(\Sigma=s)}(\text{relationObservation}\Leftrightarrow\text{relationEdge})=1$$

### Lean のコメント（日本語訳）

> 同じく、基準の分布で一致している、各層の関係の辺の観測も、25-D のもとで、候補の自性への介入のあとに、確率 1 で保存される。

### 補題の説明

関係の辺の観測の整合も、介入後も確率 1 です。

### 証明の概略

1. 上と同様。

----

<a id="Tomabechi.Theorem16_25.theorem25_no_common_fixedPoint_of_historyFamily"></a>

## 定理 `theorem25_no_common_fixedPoint_of_historyFamily`

### 式

$$\exists h_1,h_2,\ \text{fp}(h_1)\neq\text{fp}(h_2)\ \Longrightarrow\ \neg\,\exists s,\ \forall h,\ F_h(s)=s$$

### Lean のコメント（日本語訳）

> 固定した履歴ごとの唯一の固定点が、少なくとも 1 組の履歴の間で異なるなら、全履歴に共通で、全履歴の作用素で固定される状態は存在しない。定理25 (25.1) の量化を、そのまま履歴の族の上で表す。

### 補題の説明

**定理25 (25.1) の最終形**：「どの履歴でも固定される共通の状態は存在しない」。共通の固定点があれば、各履歴の（唯一の）固定点に等しく、履歴間で固定点が等しくなって矛盾します。

### 証明の概略

1. 共通の固定点 \(s\) を仮定し、各履歴 \(h\) の一意性から \(s=\text{fp}(h)\)。
2. 異なる 2 履歴の固定点が等しくなり矛盾。

----

<a id="Tomabechi.Theorem16_25.theorem16_represented_fixedPoint_of_continuous_inverseLimitMap"></a>

## 定理 `theorem16_represented_fixedPoint_of_continuous_inverseLimitMap`

### 式

$$\text{原文の逆極限条件}\ +\ F\ \text{連続}\ +\ \text{同変な自己表象}\ \Longrightarrow\ \exists x,\ F(x)=x\wedge F_{\mathrm{Rep}}(R(x))=R(x)\wedge(R(x),x)\in\text{relation}$$

### Lean のコメント（日本語訳）

> 原文の逆極限の条件と、一般の連続な \(F\) から、忠実で同変な自己表象まで、一度に接続する。層別のフィードバックの連続性・自己表象の単射性は要求しない。

### 補題の説明

固定点の存在（Fan–Glicksberg）と、表象の同変性（`represented_fixedPoint_of_equivariance`）を 1 つにまとめた定理です。

### 証明の概略

1. `theorem16_fixedPoint_exists_of_continuous_inverseLimitMap` で固定点。
2. `represented_fixedPoint_of_equivariance` で表象の固定点性と関係。

----

<a id="Tomabechi.Theorem16_25.history_represented_fixedPoints_of_equivariance"></a>

## 補題 `history_represented_fixedPoints_of_equivariance`

### 式

$$\forall h,\ \exists s,\ F_h(s)=s\wedge F_{\mathrm{Rep},h}(R_h(s))=R_h(s)\wedge(R_h(s),s)\in\text{relation}_h$$

### Lean のコメント（日本語訳）

> 履歴別の固定点の族の各固定点を、履歴別の忠実で同変な表象へ移す。履歴の間で、状態の carrier・表象の空間が異なることを保持する。

### 補題の説明

各履歴で `represented_fixedPoint_of_equivariance` を適用します。

### 証明の概略

1. 各履歴で `represented_fixedPoint_of_equivariance`。

----

<a id="Tomabechi.Theorem16_25.contraction_iterates_dist_le_initial_fixedPoint"></a>

## 補題 `contraction_iterates_dist_le_initial_fixedPoint`

### 式

$$\operatorname{dist}(F^n(x),s)\le q^n\operatorname{dist}(x,s)\quad(F(s)=s)$$

### Lean のコメント（日本語訳）

> 原文の定理16の幾何的な率：初期の残差ではなく、固定点までの初期の距離で評価する。任意の距離空間の上の縮小写像で成立し、完備性は、この評価自体には不要である。

### 補題の説明

固定点 \(s\) があれば、反復の誤差は **固定点までの初期距離** の \(q^n\) 倍以下です。

### 証明の概略

1. 帰納法：\(\operatorname{dist}(F^{n+1}x,s)=\operatorname{dist}(F(F^nx),F(s))\le q\operatorname{dist}(F^nx,s)\)。

----

<a id="Tomabechi.Theorem16_25.represented_unique_fixedPoint_and_geometricIterates_of_contraction"></a>

## 定理 `represented_unique_fixedPoint_and_geometricIterates_of_contraction`

### 式

$$\exists s:\ F(s)=s,\ \text{一意},\ \operatorname{dist}(F^nx_0,s)\le q^n\operatorname{dist}(x_0,s),\ F^nx_0\to s,\ \text{表象の固定点}$$

### Lean のコメント（日本語訳）

> 原文の完備距離・縮小条件の節を、忠実で同変な自己表象と合成する。一意性・初期の固定点距離による幾何的な率・極限・表象の固定点を、同じ \(F\) について返す。

### 補題の説明

定理16の縮小条件節の**完全版**：固定点の一意存在・幾何収束（固定点までの距離で評価）・極限・表象の固定点を 1 つの定理に。

### 証明の概略

1. Banach の固定点 \(s=\)`ContractingWith.fixedPoint` を取る（\(F(s)=s\)）。
2. 幾何評価 `contraction_iterates_dist_le_initial_fixedPoint`、収束 `tendsto_iterate_fixedPoint`、一意性 `fixedPoint_unique'` を並べる。
3. 表象：同変性から \(F_{\rm Rep}(R(s))=R(s)\)、関係への所属は `R.represents s`（21 行）。

----

<a id="Tomabechi.Theorem16_25.history_fixedPoints_geometric_and_represented"></a>

## 補題 `history_fixedPoints_geometric_and_represented`

### 式

$$\forall h:\ \operatorname{dist}(F_h^nx_0,\text{fp}(h))\le q_h^n\operatorname{dist}(x_0,\text{fp}(h)),\ \to\text{fp}(h),\ \text{表象の固定点}$$

### Lean のコメント（日本語訳）

> 履歴の族が、すでに選んだ固定点について、原文の幾何的な率・極限・同変な自己表象を返す。距離・完備性は、各履歴の carrier にだけ要求し、共通の周囲の空間の距離化は要求しない。Banach の側で別の固定点を選び直して、結論の点を取り替えない。

### 補題の説明

履歴ごとに、すでに選ばれた固定点について幾何収束と表象を示します（固定点を取り替えない）。

### 証明の概略

1. 各履歴 \(h\) について、Banach 固定点が、履歴族が選んだ固定点に一致することを（`fixedPoint_unique'`）示す。
2. 幾何評価は `contraction_iterates_dist_le_initial_fixedPoint`、収束は `tendsto_iterate_fixedPoint`（上の一致で書き換え）。
3. 表象：同変性と `isFixed` から \(F_{\rm Rep}(R(s))=R(s)\)、関係は `(R h).represents`（36 行）。

----

<a id="Tomabechi.Theorem16_25.theorem16_25_geometricRepresentation_conditionalProofCore"></a>

## 定理 `theorem16_25_geometricRepresentation_conditionalProofCore`

### 式

$$\text{幾何収束・自己表象}\ +\ 25.1\ +\ 25.2$$

### Lean のコメント（日本語訳）

> 同一の履歴の固定点の族の、原文の幾何的な収束・自己表象と、25.1/25.2 を合成する。履歴の分離と 25-D は、原文の独立の条件として保持し、モデルからの導出を要求しない。

### 補題の説明

`theorem16_25_conditionalProofCore` に、幾何収束と自己表象を加えた版です。

### 証明の概略

1. `history_fixedPoints_geometric_and_represented` と `theorem16_25_conditionalProofCore` をまとめる。

----

<a id="Tomabechi.Theorem16_25.theorem16HistoryLayerSystem_to_theorem25_fullConnection"></a>

## 定理 `theorem16HistoryLayerSystem_to_theorem25_fullConnection`

### 式

$$\text{定理16の履歴別層条件}\ \Longrightarrow\ \text{幾何収束・自己表象・25.1・25.2}$$

### Lean のコメント（日本語訳）

> 定理16の履歴別の層の条件から固定点を構成し、同じ逆極限の carrier・誘導された feedback・SC 上の距離で、幾何的な収束と自己表象を得たうえで、25.1/25.2 へ一括して接続する。縮小率、25-A(1) の履歴の分離、25-A(2)、25-D は、それぞれ独立の原文の条件として残す。縮小性は、定理16の連続な固定点の存在とは別に、各履歴の SC の距離の上で入力される。

### 補題の説明

**定理16から定理25までの全接続**（条件付き）：層システムから固定点・幾何収束・表象・25.1・25.2 をまとめて結論します。縮小性・25-A・25-D は独立の仮定です。

### 証明の概略

1. 原文の履歴別の層系 `Theorem16HistoryLayerSystem` から、各履歴の固定点族を `historyFixedPointsOfTheorem16LayerSystemWithSCMetric`（与えた距離・縮小性のもと）で構成する。
2. 幾何収束・表象の部分を、同じ固定点族に対して `M.fullRepresentedFixedPointConclusion` として得る。
3. 25.1・25.2 は `theorem16_25_conditionalProofCore` に、構成した固定点族・履歴感度・25-A(2)・C3 モデル・25-D を渡して得る（67 行）。

----

<a id="Tomabechi.Theorem16_25.historyContinuousInverseLimit_fixedPoints_data"></a>

## 補題 `historyContinuousInverseLimit_fixedPoints_data`

### 式

$$\text{構成した固定点族は元の carrier と}\ F\ \text{を保持}$$

### Lean のコメント（日本語訳）

> 一般の連続な逆極限から構成した、履歴の固定点の族は、元の逆極限の carrier と \(F\) を保持する。縮小条件・自己表象・定理25への接続で、別の carrier/作用素に置き換わらないことを確認する。

### 補題の説明

構成した固定点族の `carrier` と `feedback` が、もとの逆極限と \(F\) そのものであることの確認です（取り違えがないことの形式的な保証）。

### 証明の概略

1. 定義の展開（`rfl`）。

----


## コメント修正記録

（なし）
