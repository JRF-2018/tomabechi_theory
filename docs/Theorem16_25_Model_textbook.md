# Theorem16_25_Model.lean 解説

> 対象: [`Theorem16_25_Model.lean`](../Theorem16_25_Model.lean)（定理16・25の具体モデル・反例集）。
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
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| Schauder–Tychonoff 不動点定理 | コンパクト凸集合上の連続な自己写像に固定点がある。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| variable | 以降の補題に共通して付く変数・仮定の宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem16_25_Core.lean` が証明した**一般定理**（定理16の固定点・Banach 縮小、定理25の第 1・第 2 結論）に対する、**具体的なモデルと反例の集大成**です。一般定理の仮定が実際に満たされる例（および満たされない例）を、小さな有限・1 次元のモデルで具体的に確かめます。大きく 5 つの部分からなります。

| 部分 | 内容 | 主な宣言 |
| --- | --- | --- |
| A. 状態依存移動度の適合座標モデル | 定理21型の勾配流 \(\dot x=-A(x)V'(x)\)（\(A(x)=(1+2x)^{-2}\)）を、適合座標 \(\varphi(x)=x+x^2\) で扱い、距離の縮小・履歴別の縮小写像・共通固定点なし（25.1）を示す | `metricMobility*` |
| B. 縮小性が出ない監査例 | \(A(x)=1/(1+100x^2)\) では、強凸ポテンシャルでも縮小性が出ない | `variableMobility*` |
| C. 定理25-A(2) の SCM 例 | 25-A(2)（候補介入で法則が変わらない）を満たす有限 SCM の例 | `theorem25_selfProcess*` |
| D. 定常・区間 TCZ と、有限／区間の逆系 | 定理16の toy 逆系・勾配流の逆系での固定点の存在・縮小・幾何収束・履歴別の固定点の分離 | `theorem16_*` |
| E. 定理25第2結論の「反例と構成」 | 25-B/C だけでは無我は出ない（反例）、25-D があれば出る（マスキング SCM などの構成）、固定点の符号化で 16→25 を通す | `theorem25_*` |

### 0.2 このファイルが証明していないこと（重要）

- **特殊な例であり、一般定理の代替ではありません。** すべて 1 次元／有限（Bool）の toy モデルです。「定理16・25を証明した」のではなく「一般定理の仮定を満たす（または満たさない）具体モデルが、これだけある」ことの証明です。
- **原文の一般的な認知モデルから導いたものではありません。** 特に、25-D は**モデルの設計条件**（出力が候補に依存しない、またはノイズでマスクする）として課しており、一般の認知状態方程式から導いた結果ではありません。反例（25-B/C だけでは無我が出ない）はそのことを示します。
- 状態依存移動度モデル（A）で縮小性が出るのは、**適合座標で見た距離**に限り、元の座標の距離の縮小は主張しません。軌道の存在・区間不変性は仮定で、定理16の層別作用素との同定は追加の仮定として残ります。
- 有限の固定点族（`theorem25_historyIndexedBoolFixedPoints`）は、定理16の逆極限から作ったものではない整合性の例です。

### 0.3 ファイル内の節見出し（日本語訳）

このファイルの `.lean` には、次のような節の説明コメントがあります（すでに日本語）。

> 以下の例は Core の一般固定点論証から独立している。後続の Core が使う縮小補題とその依存は、Core 側に残す。

> 制御なしの定常例と、定数制御から区間 TCZ を構成する 1 次元モデル。

> 自己スライス条件と機能的完備性条件の違いを示す有限モデル。

> ここには 1 次元・区間状態空間で作った有限層系、勾配流、履歴別の固定点の具体例を置く。一般の逆極限定理は Core に残す。

> ここには固定点の一般定理とは独立した、具体的な有限・区間モデルと、その条件の充足／不充足を示す補題を置く。

名前空間は `Tomabechi.Theorem16_25`（`open Function`、`open scoped Convex`、`open scoped RealInnerProductSpace`）。


---

<a id="Tomabechi.Theorem16_25.variableMobilityGradient"></a>

## 定義 `variableMobilityGradient`

### 式

$$V'(x)=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二次ポテンシャル \(V(x)=x^2/2\) の勾配 \(V'(x)=x\) です。状態依存移動度の監査例（後の `variableMobilityWitness`）や、適合座標の例で使います。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate"></a>

## 定義 `metricMobilityCoordinate`

### 式

$$\varphi(x)=x+x^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

**適合座標** \(\varphi(x)=x+x^2\)。状態依存移動度 \(A(x)=(1+2x)^{-2}\)（\(=1/\varphi'(x)^2\)）の流れを、座標 \(z=\varphi(x)\) では線形に近い形にするための座標変換です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityVectorField"></a>

## 定義 `metricMobilityVectorField`

### 式

$$f(x)=-\frac{x}{(1+2x)^2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態依存移動度のベクトル場 \(f(x)=-A(x)V'(x)\)（\(A(x)=(1+2x)^{-2}\)、\(V'(x)=x\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityTransformedDrift"></a>

## 定義 `metricMobilityTransformedDrift`

### 式

$$g(x)=\frac{x}{1+2x}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

適合座標へ移したあとのドリフト \(g(x)=x/(1+2x)\)（座標では \(\dot z=-g(x)\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate_hasDerivAt"></a>

## 定理 `metricMobilityCoordinate_hasDerivAt`

### 式

$$\varphi'(x)=1+2x$$

### Lean のコメント（日本語訳）

> `φ(x)=x+x²` の微分。

### 補題の説明

適合座標の導関数です。

### 証明の概略

1. `x` の微分と `x^2` の微分の和（`HasDerivAt.add`, `HasDerivAt.pow`）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate_chainRule"></a>

## 定理 `metricMobilityCoordinate_chainRule`

### 式

$$x\ge0\Rightarrow(1+2x)\,f(x)=-g(x)$$

### Lean のコメント（日本語訳）

> 適合座標は、状態依存流のベクトル場を `-x/(1+2x)` に送る。

### 補題の説明

\(\varphi'(x)f(x)=(1+2x)\cdot\bigl(-\tfrac{x}{(1+2x)^2}\bigr)=-\tfrac{x}{1+2x}\) の確認です。

### 証明の概略

1. 定義を展開し、分母 \(1+2x\ne0\)（\(x\ge0\)）で `field_simp`。

----

<a id="Tomabechi.Theorem16_25.metricMobility_coordinateFlow_hasDerivAt"></a>

## 定理 `metricMobility_coordinateFlow_hasDerivAt`

### 式

$$\dot f=f_{\rm vec}(f)\Rightarrow\frac{d}{dt}\varphi(f(t))=-g(f(t))$$

### Lean のコメント（日本語訳）

> 実際の状態依存移動度の ODE を、適合座標へ移す連鎖律。

### 補題の説明

ODE の解 \(f(t)\) の適合座標 \(\varphi(f(t))\) が、\(\dot z=-g\) を満たす。

### 証明の概略

1. `metricMobilityCoordinate_hasDerivAt` と `hf` の合成微分（`HasDerivAt.comp`）。
2. `metricMobilityCoordinate_chainRule` で整理。

----

<a id="Tomabechi.Theorem16_25.metricMobilityTransformedDrift_strongMonotone"></a>

## 定理 `metricMobilityTransformedDrift_strongMonotone`

### 式

$$x,y\in[0,1]\Rightarrow\tfrac1{27}\bigl(\varphi(x)-\varphi(y)\bigr)^2\le\bigl(g(x)-g(y)\bigr)\bigl(\varphi(x)-\varphi(y)\bigr)$$

### Lean のコメント（日本語訳）

> 適合座標における変換後ドリフトは、区間 `[0,1]` 上で `1/27` 強単調である。この評価は、状態依存流の縮小計量を構成する局所条件である。

### 補題の説明

座標 \(z=\varphi(x)\) で見たドリフトが**強単調**（率 \(1/27\)）であることの代数的な評価です。これがあるので、座標距離で見ると、流れが縮小します。

### 証明の概略

1. 区間 \([0,1]\) 上で、\(g(x)-g(y)=\frac{x-y}{(1+2x)(1+2y)}\)、\(\varphi(x)-\varphi(y)=(x-y)(1+x+y)\) と書き直す。
2. \((1+2x)(1+2y)(1+x+y)\le 27\) 型の評価（\(x,y\le1\) から）で不等式に帰着し、`nlinarith` 等で証明（50 行程度）。

----

<a id="Tomabechi.Theorem16_25.MetricMobilityState"></a>

## 構造体 `MetricMobilityState`

### 式

$$X=[0,1]$$

### Lean のコメント（日本語訳）

> 適合座標は `[0,1]` 上で単射なので、その押し戻し距離は真正の距離になる。

### 定義の説明

区間 \([0,1]\) の点を値 `value` と所属の証明で包んだ**状態型**です。この型に、適合座標が誘導する距離を入れます。

### 証明の概略

1. 構造体なので証明はなし（`value ∈ Set.Icc 0 1`）。

----

<a id="Tomabechi.Theorem16_25.instance@L114"></a>

## インスタンス `instance@L114`

### 式

$$X\ne\emptyset$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`MetricMobilityState` が空でないことのインスタンスです（点 0 を取る）。

### 証明の概略

1. \(0\in[0,1]\) を代表元として与える。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate_injective_on_state"></a>

## 定理 `metricMobilityCoordinate_injective_on_state`

### 式

$$\varphi|_{[0,1]}\ \text{は単射}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

適合座標が状態型の上で単射であること。距離が「真正の距離」（異なる点の距離が正）になるために必要です。

### 証明の概略

1. \(\varphi(x)=\varphi(y)\) なら \((x-y)(1+x+y)=0\)、\(x,y\ge0\) より \(1+x+y>0\) なので \(x=y\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityStateMetric"></a>

## インスタンス `metricMobilityStateMetric`

### 式

$$d(x,y)=|\varphi(x)-\varphi(y)|$$

### Lean のコメント（日本語訳）

> `[0,1]` 上の状態型に、適合座標が誘導する距離を入れる。

### 定義の説明

適合座標の差の絶対値を距離とする**距離空間**のインスタンスです。

### 証明の概略

1. `MetricSpace.induced`（単射な写像による押し戻し）で構成。単射性は上の補題。

----

<a id="Tomabechi.Theorem16_25.metricMobilityState_value_dist_le_dist"></a>

## 定理 `metricMobilityState_value_dist_le_dist`

### 式

$$|x-y|\le d(x,y)$$

### Lean のコメント（日本語訳）

> 適合距離は、通常の実数距離を下から抑える。

### 補題の説明

\(|\varphi(x)-\varphi(y)|=|x-y|(1+x+y)\ge|x-y|\) です。

### 証明の概略

1. \(1+x+y\ge1\) から。

----

<a id="Tomabechi.Theorem16_25.metricMobilityState_complete"></a>

## インスタンス `metricMobilityState_complete`

### 式

$$(X,d)\ \text{は完備}$$

### Lean のコメント（日本語訳）

> 適合距離で見た状態空間 `[0,1]` は完備。座標距離が通常距離を支配するため、Cauchy 列は実数座標で収束し、閉区間内に極限をもつ。

### 定義の説明

**Banach の不動点定理に必要な完備性**です。

### 証明の概略

1. Cauchy 列は通常距離でも Cauchy（`metricMobilityState_value_dist_le_dist`）なので、実数上で収束。
2. 極限は閉区間 \([0,1]\) に入る。
3. 適合座標の連続性により、適合距離でも極限に収束する。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory"></a>

## 定義 `metricMobilityExactTrajectory`

### 式

$$x(t)=\varphi^{-1}\bigl(e^{-t}\varphi(x_0)\bigr)$$

### Lean のコメント（日本語訳）

> 線形化された系の解を、適合座標内の指数流を逆変換して明示的に定義する。

### 定義の説明

座標では \(z'=-z\)（解 \(z=e^{-t}z_0\)）となる**中心 0 の明示解**です。

### 証明の概略

1. 定義のみ：初期座標 \(\varphi(x_0)\) に \(e^{-t}\) を掛けた \(z=e^{-t}\varphi(x_0)\) を、逆座標の公式 \(x=\frac{-1+\sqrt{1+4z}}2\) で元の座標へ戻す（`metricMobilityCoordinateInverse` と同じ式）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinateInverse"></a>

## 定義 `metricMobilityCoordinateInverse`

### 式

$$\varphi^{-1}(z)=\frac{-1+\sqrt{1+4z}}{2}$$

### Lean のコメント（日本語訳）

> 適合座標 `x+x²` の逆写像。

### 定義の説明

\(x^2+x=z\) の非負の解 \(x=\frac{-1+\sqrt{1+4z}}{2}\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinateInverse_mem"></a>

## 定理 `metricMobilityCoordinateInverse_mem`

### 式

$$z\in[0,2]\Rightarrow\varphi^{-1}(z)\in[0,1]$$

### Lean のコメント（日本語訳）

> `[0,2]` では逆座標が再び `[0,1]` に入り、座標写像との合成は恒等写像。

### 補題の説明

\(\varphi([0,1])=[0,2]\) なので、逆写像は \([0,2]\) を \([0,1]\) に戻します。

### 証明の概略

1. \(\sqrt{1+4z}\in[1,3]\) から \(x\in[0,1]\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate_inverse_right"></a>

## 定理 `metricMobilityCoordinate_inverse_right`

### 式

$$z\in[0,2]\Rightarrow\varphi(\varphi^{-1}(z))=z$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

逆写像の右逆性（\(\varphi\circ\varphi^{-1}=\mathrm{id}\)）。

### 証明の概略

1. 平方根の性質 \(\sqrt{w}^2=w\) と展開（`ring`）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityCoordinate_mem"></a>

## 定理 `metricMobilityCoordinate_mem`

### 式

$$x\in[0,1]\Rightarrow\varphi(x)\in[0,2]$$

### Lean のコメント（日本語訳）

> `[0,1]` の任意の状態の適合座標は `[0,2]` にある。

### 補題の説明

\(\varphi\) の単調性から \(\varphi(0)=0,\varphi(1)=2\) の間に入る。

### 証明の概略

1. \(0\le x\le1\) から \(0\le x+x^2\le2\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_coordinate"></a>

## 定理 `metricMobilityExactTrajectory_coordinate`

### 式

$$\varphi(x(t))=e^{-t}\varphi(x_0)$$

### Lean のコメント（日本語訳）

> 明示解の適合座標は、初期座標の `exp(-t)` 倍。

### 補題の説明

明示解が実際に座標で指数減衰すること。

### 証明の概略

1. \(z=e^{-t}\varphi(x_0)\ge0\)（`x.property` と \(e^{-t}>0\)）。
2. \(\sqrt{1+4z}^2=1+4z\)（`Real.sq_sqrt`）。
3. 定義を展開して、\(x+x^2=z\) を `nlinarith` で示す（13 行）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_start"></a>

## 定理 `metricMobilityExactTrajectory_start`

### 式

$$x(0)=x_0$$

### Lean のコメント（日本語訳）

> 明示解は、時刻 0 に初期状態を取る。

### 補題の説明

初期条件の確認です。

### 証明の概略

1. \(t=0\) で \(\varphi^{-1}(\varphi(x_0))=x_0\)（左逆性）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_stays"></a>

## 定理 `metricMobilityExactTrajectory_stays`

### 式

$$t\ge0\Rightarrow x(t)\in[0,1]$$

### Lean のコメント（日本語訳）

> 非負時刻では、明示解は初期値と 0 の間に留まり、したがって `[0,1]` 内にある。

### 補題の説明

**不変性**：解は区間 \([0,1]\) から出ません。

### 証明の概略

1. \(0\le\varphi(x_0)\le2\)、\(0<e^{-t}\le1\)（\(t\ge0\)）から、\(1\le1+4e^{-t}\varphi(x_0)\le9\)。
2. よって \(1\le\sqrt{1+4e^{-t}\varphi(x_0)}\le3\)（`Real.le_sqrt`、`Real.sqrt_le_iff`）。
3. 逆座標の式 \(\frac{-1+\sqrt{\cdot}}2\) が \([0,1]\) に入る（`nlinarith`）（34 行）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_coordinate_hasDerivAt"></a>

## 定理 `metricMobilityExactTrajectory_coordinate_hasDerivAt`

### 式

$$\frac{d}{dt}\varphi(x(t))=-\varphi(x(t))$$

### Lean のコメント（日本語訳）

> 明示解の適合座標は、単位率の線形安定系に従う。

### 補題の説明

座標 \(z=\varphi(x(t))\) が \(\dot z=-z\) を満たす。

### 証明の概略

1. `metricMobilityExactTrajectory_coordinate` で \(z=e^{-t}z_0\)、`Real.hasDerivAt_exp` で微分。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryFlow"></a>

## 定義 `metricMobilityHistoryFlow`

### 式

$$\varphi\bigl(x(t)\bigr)=\varphi(r)+e^{-t}\bigl(\varphi(x_0)-\varphi(r)\bigr)$$

### Lean のコメント（日本語訳）

> 履歴 r をポテンシャルの谷の中心とした、適合座標上の明示流。座標では `z' = -(z - φ(r))` であり、逆座標に戻した状態依存勾配流である。

### 定義の説明

**履歴 \(r\) を中心とする**流れです。\(r\) は定理16で、履歴 \(h\) に応じて決まる谷の中心に対応します。

### 証明の概略

1. 定義のみ（逆座標 `metricMobilityCoordinateInverse` を使う）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryFlow_coordinate_mem"></a>

## 定理 `metricMobilityHistoryFlow_coordinate_mem`

### 式

$$t\ge0\Rightarrow\varphi(r)+e^{-t}\bigl(\varphi(x_0)-\varphi(r)\bigr)\in[0,2]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴流の座標が \([0,2]\) に入ること（逆座標が定義域内に入る）。

### 証明の概略

1. \(\varphi(r),\varphi(x_0)\in[0,2]\) の凸結合なので \([0,2]\) に入る。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep"></a>

## 定義 `metricMobilityHistoryStep`

### 式

$$S_{r,T}(x)=\mathrm{flow}_r(x,T)$$

### Lean のコメント（日本語訳）

> 各履歴の中心点を固定する、明示的な勾配流の時間写像。

### 定義の説明

時刻 \(T\) の履歴流の写像です。**定理16の層別作用素の、このモデルでの具体形**にあたります（ただし同定はしていません）。

### 証明の概略

1. 定義のみ（`metricMobilityHistoryFlow` を値とし、`[0,1]` 内であることを添える）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_coordinate"></a>

## 定理 `metricMobilityHistoryStep_coordinate`

### 式

$$\varphi(S_{r,T}(x))=\varphi(r)+e^{-T}\bigl(\varphi(x)-\varphi(r)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴別の時間写像の、座標での明示式（アフィン写像）。

### 証明の概略

1. `metricMobilityHistoryFlow` の座標の式（逆写像の右逆性）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_fixes_center"></a>

## 定理 `metricMobilityHistoryStep_fixes_center`

### 式

$$S_{r,T}(r)=r$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心 \(r\) は、履歴別の時間写像の固定点です。

### 証明の概略

1. 座標の式で \(x=r\) なら \(\varphi(S(r))=\varphi(r)\)、座標の単射性で \(S(r)=r\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_contracting"></a>

## 定理 `metricMobilityHistoryStep_contracting`

### 式

$$T>0\Rightarrow S_{r,T}\ \text{は縮小率 }e^{-T}\ \text{の}\ \mathrm{ContractingWith}$$

### Lean のコメント（日本語訳）

> 履歴中心が固定された座標アフィン写像なので、各履歴の更新は、適合距離で縮小率 `exp(-T)` の `ContractingWith` になる。

### 補題の説明

**縮小性**：適合距離で \(d(S x,S y)=e^{-T}d(x,y)\)。

### 証明の概略

1. 座標の式から \(\varphi(Sx)-\varphi(Sy)=e^{-T}(\varphi(x)-\varphi(y))\)。
2. 適合距離の定義で \(d(Sx,Sy)=e^{-T}d(x,y)\)。
3. \(e^{-T}<1\)（\(T>0\)）で `ContractingWith`。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_pairwise_contraction"></a>

## 定理 `metricMobilityExactTrajectory_pairwise_contraction`

### 式

$$\forall t\in[0,T],\ d\bigl(\varphi(x(t)),\varphi(y(t))\bigr)\le e^{-t}d\bigl(\varphi(x_0),\varphi(y_0)\bigr)$$

### Lean のコメント（日本語訳）

> 明示軌道は、適合距離で、任意の 2 つの初期値の間を `exp(-t)` で縮める。

### 補題の説明

2 つの明示軌道の距離が \(e^{-t}\) で縮むこと。

### 証明の概略

1. 座標が \(e^{-t}\varphi(x_0)\) なので、差は \(e^{-t}(\varphi(x_0)-\varphi(y_0))\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExact_flow_timeMap_contracting"></a>

## 定理 `metricMobilityExact_flow_timeMap_contracting`

### 式

$$T>0\Rightarrow\text{時間写像は縮小率 }e^{-T}\ \text{の}\ \mathrm{ContractingWith}$$

### Lean のコメント（日本語訳）

> この具体的な状態依存流の時間写像は、適合距離のもとで縮小写像である。

### 補題の説明

`metricMobilityExactTrajectory` の時間 \(T\) 写像が縮小写像であること。

### 証明の概略

1. `metricMobilityExactTrajectory_pairwise_contraction` を \(t=T\) で使い、適合距離の定義に直す。

----

<a id="Tomabechi.Theorem16_25.metricMobility_flow_coordinate_dist_contracting"></a>

## 定理 `metricMobility_flow_coordinate_dist_contracting`

### 式

$$d\bigl(\varphi(f(t)),\varphi(g(t))\bigr)\le e^{-\frac1{27}(t-a)}\,d\bigl(\varphi(f(a)),\varphi(g(a))\bigr)$$

### Lean のコメント（日本語訳）

> 状態依存移動度 `A(x)=(1+2x)⁻²` の流れは、区間 `[0,1]` に留まる軌道同士で、適合座標 `φ(x)=x+x²` の距離を率 `1/27` で縮める。原座標の距離の縮小は主張しない。

### 補題の説明

**任意の（明示解でない）ODE の解 2 つ**が、区間 \([0,1]\) に留まるなら、適合座標の距離が率 \(1/27\) で縮む。Grönwall 型の議論です。

### 証明の概略

1. 座標の差 \(w(t)=\varphi(f)-\varphi(g)\) の二乗の微分が \(\le-\frac2{27}w^2\)（強単調性 `…_strongMonotone` と座標の ODE `…_coordinateFlow_hasDerivAt`）。
2. Grönwall の不等式（`norm_le_gronwallBound_of_norm_deriv_right_le` 型）で \(|w(t)|\le e^{-(t-a)/27}|w(a)|\)。

----

<a id="Tomabechi.Theorem16_25.metricMobility_flow_timeMap_contracting"></a>

## 定理 `metricMobility_flow_timeMap_contracting`

### 式

$$T>0\Rightarrow\text{時間写像は縮小率 }e^{-T/27}\ \text{の}\ \mathrm{ContractingWith}$$

### Lean のコメント（日本語訳）

> 状態依存移動度のこの一次元モデルでは、座標誘導距離を使えば、時間 `T>0` の流れ写像が `ContractingWith` になる。定理21の勾配流から Banach 条件へ接続する具体例だが、[0,1] 不変性、全初期値の軌道存在、そして定理16の層別更新則との同定は、いずれも追加仮定である。

### 補題の説明

**定理21の勾配流 → Banach 条件**の具体例です。軌道 `trajectory` は ODE 解で区間に留まる、と仮定します（存在の保証は含みません）。

### 証明の概略

1. `metricMobility_flow_coordinate_dist_contracting` を \(t=T\)、\(a=0\) で全初期値の組に適用。
2. \(e^{-T/27}<1\) で `ContractingWith`。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExact_flow_timeMap_fixes_zero"></a>

## 定理 `metricMobilityExact_flow_timeMap_fixes_zero`

### 式

$$S_T(0)=0$$

### Lean のコメント（日本語訳）

> 線形化状態依存流の時間写像は、平衡点 0 を固定する。

### 補題の説明

平衡点 0 は時間写像の固定点。

### 証明の概略

1. 初期座標 0 なら \(e^{-T}\cdot0=0\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExact_flow_fixedPoint_eq_zero"></a>

## 定理 `metricMobilityExact_flow_fixedPoint_eq_zero`

### 式

$$T>0\Rightarrow\mathrm{fixedPoint}(S_T)=0$$

### Lean のコメント（日本語訳）

> 明示的 ODE モデルの Banach 固定点は、ポテンシャルの平衡点 0 に一致する。

### 補題の説明

`ContractingWith.fixedPoint`（Banach 固定点）が 0 に一致すること。

### 証明の概略

1. `metricMobilityExact_flow_timeMap_fixes_zero` と固定点の一意性（`ContractingWith.fixedPoint_unique`）。

----

<a id="Tomabechi.Theorem16_25.metricMobility_flow_timeMap_hasUniqueFixedPoint"></a>

## 定理 `metricMobility_flow_timeMap_hasUniqueFixedPoint`

### 式

$$T>0\Rightarrow\exists!\,x^\ast,\ S_T(x^\ast)=x^\ast$$

### Lean のコメント（日本語訳）

> 完備な適合距離のもとで、この状態依存流の時間写像には Banach 固定点が一意に存在する。大域軌道の存在・区間不変性は仮定し、定理16の層別作用素との同定は行っていない。

### 補題の説明

縮小写像の**一意な固定点の存在**（完備性による）。

### 証明の概略

1. `metricMobility_flow_timeMap_contracting`（時間写像は縮小写像）を得る。
2. `hasUniqueFixedPoint_of_contraction`（縮小写像は唯一の固定点を持つ。状態空間の完備性 `metricMobilityState_complete` を内部で使う）を適用する（14 行）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryFamily_theorem25_firstConclusion"></a>

## 定理 `metricMobilityHistoryFamily_theorem25_firstConclusion`

### 式

$$r_1\ne r_2\Rightarrow\neg\exists x,\ S_{r_1,T}(x)=x\wedge S_{r_2,T}(x)=x$$

### Lean のコメント（日本語訳）

> 履歴別の時間写像を、一般の Banach 固定点族の構成へ入れ、25-A(1) に対応する中心の分離から、定理25の第 1 結論を得る。

### 補題の説明

**定理25の第1結論**（異なる履歴は共通の固定点を持たない）の、このモデルでの確認です。固定点は各履歴の中心なので、中心が異なれば共通の固定点はありません。

### 証明の概略

1. `metricMobilityHistoryStep_fixes_center` と縮小性による固定点の一意性：\(S_{r_i}\) の固定点は \(r_i\) だけ。
2. \(r_1\ne r_2\) なので共通の固定点は存在しない。

----

<a id="Tomabechi.Theorem16_25.variableMobilityWitness"></a>

## 定義 `variableMobilityWitness`

### 式

$$A(x)=\frac1{1+100x^2}$$

### Lean のコメント（日本語訳）

> 状態依存移動度が強凸性だけから縮小性を与えないことを示す、一次元の監査例。`V(x)=x²/2` と `A(x)=1/(1+100x²)` に対する、ベクトル場 `-A(x)V'(x)`。

### 定義の説明

**反例（監査例）**：移動度 \(A(x)=\frac1{1+100x^2}\) です。ポテンシャルが強凸でも、移動度が状態に依存すると、ベクトル場が距離を縮小するとは限りません。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.variableMobilityVectorField"></a>

## 定義 `variableMobilityVectorField`

### 式

$$f(x)=-\frac{x}{1+100x^2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

監査例のベクトル場 \(f=-A(x)V'(x)\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.variableMobilityPotential"></a>

## 定義 `variableMobilityPotential`

### 式

$$V(x)=\frac{x^2}2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

監査例のポテンシャル。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.variableMobilityPotential_stronglyConvex"></a>

## 定理 `variableMobilityPotential_stronglyConvex`

### 式

$$V\ \text{は任意の}\ U\ \text{上で強凸（定数 }1\text{）}$$

### Lean のコメント（日本語訳）

> 二次ポテンシャルは、任意の領域上で、強凸定数 1 をもつ。

### 補題の説明

ポテンシャルは強凸（\(c=1\)）：それでも縮小性が出ない、という対比です。

### 証明の概略

1. `Theorem21.StronglyConvexOn` の定義を展開し、\(\langle x-y,x-y\rangle=(x-y)^2\) と整理。

----

<a id="Tomabechi.Theorem16_25.variableMobilityVectorField_hasDerivAt"></a>

## 定理 `variableMobilityVectorField_hasDerivAt`

### 式

$$f'(x)=\frac{100x^2-1}{(1+100x^2)^2}$$

### Lean のコメント（日本語訳）

> この状態依存移動度のベクトル場の導関数。

### 補題の説明

\(f\) の導関数の公式です（商の微分）。

### 証明の概略

1. 商の微分と `ring`（`field_simp`）。

----

<a id="Tomabechi.Theorem16_25.variableMobilityVectorField_deriv_pos"></a>

## 定理 `variableMobilityVectorField_deriv_pos`

### 式

$$x>\tfrac1{10}\Rightarrow f'(x)>0$$

### Lean のコメント（日本語訳）

> 不変区間の右側では、強凸二次ポテンシャルでも、状態依存移動度の閉ループのベクトル場は、局所的に距離を拡大する方向を持つ。

### 補題の説明

\(x>1/10\) では \(f'>0\)（距離を**拡大**する方向）。強凸でも、ベクトル場は縮小写像のようには振る舞いません。

### 証明の概略

1. 導関数の公式で \(100x^2-1>0\)（\(x>1/10\)）。

----

<a id="Tomabechi.Theorem16_25.variableMobilityWitness_lower_bound"></a>

## 定理 `variableMobilityWitness_lower_bound`

### 式

$$|x|\le\tfrac3{10}\Rightarrow A(x)\ge\tfrac1{10}$$

### Lean のコメント（日本語訳）

> `[-3/10,3/10]` 上で、移動度は一様に 10 分の 1 以上。

### 補題の説明

区間 \([-3/10,3/10]\) で移動度が下から抑えられること（移動度が退化していないことの確認）。

### 証明の概略

1. \(100x^2\le9\) なので \(A(x)\ge\frac1{10}\)。

----

<a id="Tomabechi.Theorem16_25.variableMobilityVectorField_mul_self_nonpos"></a>

## 定理 `variableMobilityVectorField_mul_self_nonpos`

### 式

$$x\,f(x)\le0$$

### Lean のコメント（日本語訳）

> 閉区間の両端でベクトル場は内向きであり、符号は全域で原点方向。

### 補題の説明

\(x\) と \(f(x)\) の符号が逆（または 0）であること：ベクトル場は常に原点向きです。したがって区間 \([-a,a]\) は不変になります。

### 証明の概略

1. \(xf(x)=-\frac{x^2}{1+100x^2}\le0\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_finiteDomain_aemeasurable"></a>

## 定理 `theorem25_finiteDomain_aemeasurable`

### 式

$$f:U\to V\ \Rightarrow\ f\ \text{は}\ \mu\ \text{に関して a.e. 可測}$$

### Lean のコメント（日本語訳）

> 有限離散の外生空間からの写像は可測であり、その確率法則 pushforward は通常の像測度になる。

### 補題の説明

有限で、各点が可測な空間 \(U\) からの任意の写像は可測です。**有限の外生ノイズ**から作る確率モデルで、確率法則（像測度）を定義するために使います（`private`）。

### 証明の概略

1. `MeasurableSingletonClass` と有限性から、任意の写像は可測（`measurable_of_finite`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_degenerateWitness"></a>

## 定義 `theorem25_selfProcessSCM_degenerateWitness`

### 式

$$\text{外生・履歴・候補がすべて定数の SCM}$$

### Lean のコメント（日本語訳）

> 生成意味論の型検査用の退化例。外生状態・履歴・候補を定数にし、実際の `IndepFun` と介入不変な pushforward 法則から 25-A(2) を満たす。

### 定義の説明

`Theorem25SelfProcessSCM` の**最も退化した例**：すべての型が `Unit`/`Bool` 一点由来の定数です。型の整合を確かめるためのもので、内容は薄い。

### 証明の概略

1. 構造体の各フィールドを定数で与える（独立性・介入不変性は定数なので自明）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_degenerateWitness_satisfies25A2"></a>

## 定理 `theorem25_selfProcessSCM_degenerateWitness_satisfies25A2`

### 式

$$\text{Condition25A2}(\text{退化 SCM})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

退化例が 25-A(2)（候補への介入が法則を変えない）を満たす、という確認です。

### 証明の概略

1. `Theorem25SelfProcessSCM.condition25A2`（Core）を適用し、SCM の独立性・介入不変性のフィールドを渡す。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_nonconstantWitness"></a>

## 定義 `theorem25_selfProcessSCM_nonconstantWitness`

### 式

$$\text{候補 }=\text{外生 Bool},\ \text{出力も外生に依存}$$

### Lean のコメント（日本語訳）

> 候補変数と出力がともに非定数な有限 SCM。候補は外生 Bool そのもの、履歴は定数で、独立性は自明だが、観測された自己過程・出力は外生 Bool に依存して非定数となる。介入後の構造式が候補値を無視するため 25-A(2) を満たす。これは生成意味論の例であり、原文の一般認知状態方程式から候補非干渉を導いた結果ではない。

### 定義の説明

**非退化な例**：候補が実際に変動し、出力も変動する有限 SCM です。介入後の構造式が候補値を**無視する**ように作ってあるので、25-A(2)（候補に介入しても法則が変わらない）が成り立ちます。原文の認知モデルから導いたものではなく、定義の整合性の例です。

### 証明の概略

1. 構造体の各フィールドを具体的に与える（外生 Bool、構造式を場合分けで）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_nonconstantWitness_candidate_surjective"></a>

## 定理 `theorem25_selfProcessSCM_nonconstantWitness_candidate_surjective`

### 式

$$\text{候補変数は全射（両値を取る）}$$

### Lean のコメント（日本語訳）

> この有限 SCM の構造式は、候補の両値を外生空間上に実現し、出力も非定数にする。

### 補題の説明

候補が実際に `true` も `false` も取る（定数でない）ことの確認です。

### 証明の概略

1. 外生値 `true`/`false` に対し、候補の値がそれぞれ `true`/`false`。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_nonconstantWitness_candidate_true_positive"></a>

## 定理 `theorem25_selfProcessSCM_nonconstantWitness_candidate_true_positive`

### 式

$$\mu(\{\text{true}\})>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

外生法則で `true` の確率が正であること（候補が実際に確率的に `true` になる）。

### 証明の概略

1. 外生法則が一様で、`true` の測度が 1/2 であることを計算。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_nonconstantWitness_output_nonconstant"></a>

## 定理 `theorem25_selfProcessSCM_nonconstantWitness_output_nonconstant`

### 式

$$\exists u,v,\ Y(u)\ne Y(v)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

出力が外生変数に依存して非定数であること。

### 証明の概略

1. \(u=\)`true`、\(v=\)`false` を代入して異なることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessSCM_nonconstantWitness_satisfies25A2"></a>

## 定理 `theorem25_selfProcessSCM_nonconstantWitness_satisfies25A2`

### 式

$$\text{Condition25A2}(\text{非定数 SCM})$$

### Lean のコメント（日本語訳）

> 候補が実際に変動する有限外生ノイズのもとで、25-A(2) の確率版を満たす SCM 例。

### 補題の説明

非定数でも 25-A(2) を満たす例（**候補が変動しても、介入後の法則が不変**）。

### 証明の概略

1. `Theorem25SelfProcessSCM.condition25A2`（Core）を適用。介入後の構造式が候補値を無視することを確認。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessA2LawToyModel"></a>

## 定義 `theorem25_selfProcessA2LawToyModel`

### 式

$$\text{subject}=\text{false}:\text{25-A(2)の等式 },\ \text{subject}=\text{true}:\text{介入で法則が変わる}$$

### Lean のコメント（日本語訳）

> 自己過程を 1 つの型付き表現とした、有限の法則例。Subject=false では 25-A(2) の法則等式が成立し、別 subject=true では介入で法則が変わる。候補独立性のフィールドは `True` であり、確率変数の独立性は示していない。

### 定義の説明

25-A(2)（**自分自身に対してだけ**成り立つ不変性）が、**他の主体**では成り立たないことを示す法則レベルの例です。独立性の欄は `True` で埋めてあるだけ（確率変数の独立性は示していない）。

### 証明の概略

1. `Theorem25SelfProcessLawModel` の各フィールドを、`Subject` 場合分けで具体的に与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessA2LawToyModel_satisfies_condition25A2"></a>

## 定理 `theorem25_selfProcessA2LawToyModel_satisfies_condition25A2`

### 式

$$\text{Condition25A2}(\text{subject}=\text{false})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

主体 `false` について 25-A(2) が成り立つ。

### 証明の概略

1. 定義を展開し、介入後の法則と基準の法則が等しいことを確認。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfProcessA2LawToyModel_otherSubjectLawChanges"></a>

## 定理 `theorem25_selfProcessA2LawToyModel_otherSubjectLawChanges`

### 式

$$\exists h,s,\ \text{intervenedJointLaw}(\text{true},h,s)\ne\text{baselineJointLaw}(\text{true},h)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

別の主体 `true` では、介入で法則が実際に変わる。25-A(2) は主体の**一断面**での性質だ、という対比です。

### 証明の概略

1. 具体的な \(h,s\) を取って法則が異なることを計算。

----

<a id="Tomabechi.Theorem16_25.metricMobilityWitness"></a>

## 定義 `metricMobilityWitness`

### 式

$$A(x)=\frac1{(1+2x)^2}$$

### Lean のコメント（日本語訳）

> 適合座標をもつ別の状態依存移動度の例。`φ'(x)=1/√A(x)=1+2x` を満たす `A(x)=(1+2x)⁻²` を使う。

### 定義の説明

適合座標 \(\varphi(x)=x+x^2\) に対応する移動度です（\(\varphi'=1/\sqrt{A}\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityWitness_lower_bound"></a>

## 定理 `metricMobilityWitness_lower_bound`

### 式

$$x\in[0,1]\Rightarrow A(x)\ge\tfrac19$$

### Lean のコメント（日本語訳）

> `[0,1]` 上の適合移動度は一様に正定値であり、下界は `1/9`。

### 補題の説明

\((1+2x)^2\le9\) なので \(A(x)\ge1/9\)。移動度が退化しない（一様に正）。

### 証明の概略

1. \(1\le1+2x\le3\) から \((1+2x)^2\le9\)。

----

<a id="Tomabechi.Theorem16_25.metricMobilityVectorField_eq_negative_mobility_gradient"></a>

## 定理 `metricMobilityVectorField_eq_negative_mobility_gradient`

### 式

$$f(x)=-A(x)\,V'(x)$$

### Lean のコメント（日本語訳）

> 二次ポテンシャルの勾配にこの移動度を掛けたものが、モデルのベクトル場である。

### 補題の説明

`metricMobilityVectorField` が、移動度 × 勾配（\(V'(x)=x\)）の負であること。**定理21型の状態依存移動度の勾配流**になっていることの確認です。

### 証明の概略

1. 定義を展開し、`field_simp`/`ring`。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactPotential"></a>

## 定義 `metricMobilityExactPotential`

### 式

$$V_{\rm ex}(x)=\tfrac12\varphi(x)^2$$

### Lean のコメント（日本語訳）

> 二次の適合座標の二乗をポテンシャルに選ぶと、変換後の流れは厳密に線形化する。

### 定義の説明

適合座標の二乗の半分をポテンシャルに選びます。すると流れは座標 \(z=\varphi(x)\) で厳密に \(\dot z=-z\)（線形）になります。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactGradient"></a>

## 定義 `metricMobilityExactGradient`

### 式

$$V_{\rm ex}'(x)=\varphi(x)\,\varphi'(x)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

線形化ポテンシャルの勾配 \(\varphi\varphi'\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactVectorField"></a>

## 定義 `metricMobilityExactVectorField`

### 式

$$f_{\rm ex}(x)=-\frac{\varphi(x)}{1+2x}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

線形化ポテンシャルに対するベクトル場（座標で \(\dot z=-z\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactVectorField_eq_negative_mobility_gradient"></a>

## 定理 `metricMobilityExactVectorField_eq_negative_mobility_gradient`

### 式

$$f_{\rm ex}=-A\cdot V_{\rm ex}'$$

### Lean のコメント（日本語訳）

> 線形化ポテンシャルの勾配に移動度を掛けた閉ループ場。

### 補題の説明

明示解のベクトル場が、移動度 × 勾配の形であること。

### 証明の概略

1. 定義を展開して `field_simp`。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactPotential_stronglyConvex"></a>

## 定理 `metricMobilityExactPotential_stronglyConvex`

### 式

$$V_{\rm ex}\ \text{は }[0,1]\text{ 上で 1-強凸}$$

### Lean のコメント（日本語訳）

> 適合距離に合わせたポテンシャルも、`[0,1]` 上で 1-強凸である。

### 補題の説明

`Theorem21.StronglyConvexOn`（強凸の一次不等式）が \([0,1]\) で成り立つこと。**定理21の強凸性の仮定**を満たす、という確認です。

### 証明の概略

1. \(V_{\rm ex}''=\varphi'^2+\varphi\varphi''\ge1\) の評価（\(\varphi'=1+2x\ge1\)、\(\varphi''=2\)、\(\varphi\ge0\)）に相当する一次不等式を代数的に示す。

----

<a id="Tomabechi.Theorem16_25.metricMobilityExactTrajectory_hasDerivAt"></a>

## 定理 `metricMobilityExactTrajectory_hasDerivAt`

### 式

$$\dot x(t)=f_{\rm ex}(x(t))$$

### Lean のコメント（日本語訳）

> 上で定義した明示軌道は、線形化ポテンシャルの状態依存勾配流を満たす。

### 補題の説明

`metricMobilityExactTrajectory` が実際に ODE の解であること。

### 証明の概略

1. 座標の ODE（`…_coordinate_hasDerivAt`）を逆座標の微分で元の座標へ戻す（逆関数の微分）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryPotential"></a>

## 定義 `metricMobilityHistoryPotential`

### 式

$$V_r(y)=\tfrac12\bigl(\varphi(y)-\varphi(r)\bigr)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴中心 \(r\) を谷の底に移したポテンシャル。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryGradient"></a>

## 定義 `metricMobilityHistoryGradient`

### 式

$$V_r'(y)=\bigl(\varphi(y)-\varphi(r)\bigr)\varphi'(y)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴別ポテンシャルの勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryVectorField"></a>

## 定義 `metricMobilityHistoryVectorField`

### 式

$$f_r(y)=-\frac{\varphi(y)-\varphi(r)}{1+2y}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴別のベクトル場。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryPotential_hasDerivAt"></a>

## 定理 `metricMobilityHistoryPotential_hasDerivAt`

### 式

$$\frac{d}{dy}V_r=V_r'$$

### Lean のコメント（日本語訳）

> 中心移動ポテンシャルの導関数は、定義した履歴別勾配に一致する。

### 補題の説明

`metricMobilityHistoryGradient` が実際に導関数であること。

### 証明の概略

1. 合成関数の微分（`HasDerivAt.pow`, 適合座標の微分）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryVectorField_eq_negative_mobility_gradient"></a>

## 定理 `metricMobilityHistoryVectorField_eq_negative_mobility_gradient`

### 式

$$f_r=-A\cdot V_r'$$

### Lean のコメント（日本語訳）

> 中心を移したポテンシャルの、状態依存移動度の勾配ベクトル場。

### 補題の説明

履歴別のベクトル場が、移動度 × 勾配の形であること。

### 証明の概略

1. 定義を展開して `field_simp`。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryFlow_hasDerivAt"></a>

## 定理 `metricMobilityHistoryFlow_hasDerivAt`

### 式

$$t\ge0\Rightarrow\dot x_r(t)=f_r(x_r(t))$$

### Lean のコメント（日本語訳）

> 履歴中心 `r` の適合座標時間写像を逆座標へ戻した軌道は、中心移動ポテンシャルの元座標での、状態依存勾配流 ODE を満たす。

### 補題の説明

履歴流が元の座標での勾配流 ODE の解であること。

### 証明の概略

1. 座標の式 \(z(t)=\varphi(r)+e^{-t}(z_0-\varphi(r))\) の微分 \(\dot z=-(z-\varphi(r))\)。
2. 逆座標の微分で元の座標の ODE に戻す。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_unique_fixedPoint"></a>

## 定理 `metricMobilityHistoryStep_unique_fixedPoint`

### 式

$$S_{r,T}(x)=x\Rightarrow x=r$$

### Lean のコメント（日本語訳）

> 履歴中心 `r` は、その履歴の縮小写像の唯一の固定点である。

### 補題の説明

固定点が中心 \(r\) **だけ**であること。

### 証明の概略

1. 固定点 \(x\) の座標をとる：`metricMobilityHistoryStep_coordinate` で \(\varphi(x)=\varphi(r)+e^{-T}(\varphi(x)-\varphi(r))\)。
2. \(e^{-T}<1\)（\(T>0\)）なので \((1-e^{-T})(\varphi(x)-\varphi(r))=0\)、よって \(\varphi(x)=\varphi(r)\)（`nlinarith`）。
3. 座標の単射性（`metricMobilityCoordinate_injective_on_state`）で \(x=r\)（15 行）。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_fixedPoints_separate"></a>

## 定理 `metricMobilityHistoryStep_fixedPoints_separate`

### 式

$$r_1\ne r_2\Rightarrow S_{r_1,T}(r_1)\ne S_{r_2,T}(r_2)$$

### Lean のコメント（日本語訳）

> 履歴中心の異なる 2 つの線形化勾配流時間写像は、中心を別々の唯一の固定点とする。これは定理25 (25.1) の「履歴に依存する谷・縮小流」のモデル接続で、原文の一般的な自己意識更新則への同定は、追加の仮定として残る。

### 補題の説明

固定点が履歴ごとに**別々**であること（\(S_{r_i}(r_i)=r_i\) なので \(r_1\ne r_2\) から従う）。

### 証明の概略

1. `metricMobilityHistoryStep_fixes_center` で \(S_{r_i}(r_i)=r_i\)。
2. \(r_1\ne r_2\) から結論。

----

<a id="Tomabechi.Theorem16_25.metricMobilityHistoryStep_has_no_common_fixedPoint"></a>

## 定理 `metricMobilityHistoryStep_has_no_common_fixedPoint`

### 式

$$r_1\ne r_2\Rightarrow\neg\exists x,\ S_{r_1,T}x=x\wedge S_{r_2,T}x=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**共通固定点が存在しない**こと（定理25.1の具体例）。

### 証明の概略

1. 共通の固定点 \(x\) があるとして、2 つの履歴の固定点方程式の座標をとる。
2. \(e^{-T}<1\) なので \((1-e^{-T})(\varphi(r_1)-\varphi(r_2))=0\)、よって \(\varphi(r_1)=\varphi(r_2)\)。
3. 座標の単射性で \(r_1=r_2\) となり、仮定 \(r_1\ne r_2\) に矛盾（28 行）。

----

<a id="Tomabechi.Theorem16_25.stronglyConvexScalarMobilityGradientFlow_dist_contracting"></a>

## 定理 `stronglyConvexScalarMobilityGradientFlow_dist_contracting`

### 式

$$\dot x=-a\nabla V(x),\ V\ c\text{-強凸}\Rightarrow\|x(T)-y(T)\|\le e^{-acT}\|x_0-y_0\|$$

### Lean のコメント（日本語訳）

> 正の定数スカラー移動度 `A=aI` は、強凸な勾配流で時間をスケールするだけである。したがって、その時間写像は率 `exp(-a*c*T)` で縮小する。これは、定理21の状態依存移動度の族の内側にある、一般の Hilbert 空間での十分条件であり、任意の変動する `A(x)` は覆わない。

### 補題の説明

**一般の Hilbert 空間**での、定数スカラー移動度の強凸勾配流の縮小性です（変動する \(A(x)\) は含みません）。

### 証明の概略

1. 2 つの解の差の二乗 \(\|x-y\|^2\) の微分が \(\le-2ac\|x-y\|^2\)（強凸の一次不等式 `StronglyConvexOn`）。
2. Grönwall の不等式で \(\|x-y\|\le e^{-acT}\|x_0-y_0\|\)。

----

<a id="Tomabechi.Theorem16_25.metricMobility_flow_distance_to_equilibrium"></a>

## 定理 `metricMobility_flow_distance_to_equilibrium`

### 式

$$d\bigl(\varphi(f(t)),0\bigr)\le e^{-\frac1{27}(t-a)}\,d\bigl(\varphi(f(a)),0\bigr)$$

### Lean のコメント（日本語訳）

> このモデルでは、平衡点 0 への距離の減衰は、2 軌道の収縮の特殊化として従う。定理1型の 1 軌道の安定性評価に相当するが、ここでは、より強い増分収縮を先に証明している。

### 補題の説明

**平衡点への距離の指数減衰**（定理1型）です。ただし、これは 2 軌道の収縮（`metricMobility_flow_coordinate_dist_contracting`）で、片方を平衡点 0 に取った特殊化として得られます。

### 証明の概略

1. 平衡点 0 は ODE の解（定数）なので、`metricMobility_flow_coordinate_dist_contracting` で \(g\equiv0\) とする。

----

<a id="Tomabechi.Theorem16_25.stronglyConvexScalarMobilityGradientFlow_timeMap_contracting"></a>

## 定理 `stronglyConvexScalarMobilityGradientFlow_timeMap_contracting`

### 式

$$T>0\Rightarrow\text{時間写像は縮小率 }e^{-acT}\ \text{の}\ \mathrm{ContractingWith}$$

### Lean のコメント（日本語訳）

> 定理21の強凸条件に定数スカラー移動度 `A(x)=aI` を置いた連続時間写像は、全初期点からの軌道が領域内に留まるなら、率 `exp(-a*c*T)` で縮小する。この条件を満たす層別写像は、定理16の追加の縮小条件へ接続できる。

### 補題の説明

上の距離縮小を `ContractingWith`（Banach の縮小写像）の形にしたものです。

### 証明の概略

1. `stronglyConvexScalarMobilityGradientFlow_dist_contracting` を使い、\(e^{-acT}<1\)（\(a,c,T>0\)）で `ContractingWith`。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryFlow"></a>

## 定義 `theorem16_stationaryFlow`

### 式

$$x(t)=x_0$$

### Lean のコメント（日本語訳）

> 無制御の定常軌道 `x(t)=x₀`。

### 定義の説明

制御なしの、動かない軌道です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryFlow_hasDerivAt"></a>

## 定理 `theorem16_stationaryFlow_hasDerivAt`

### 式

$$\dot x=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定常軌道の導関数は 0。

### 証明の概略

1. 定数関数の微分（`hasDerivAt_const`）。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryReachable"></a>

## 定義 `theorem16_stationaryReachable`

### 式

$$\mathrm{Reach}(x_0,t)=\{x_0\}$$

### Lean のコメント（日本語訳）

> 無制御の定常流 `x(t)=x₀` における、時刻 t の到達可能集合。

### 定義の説明

各時刻で 1 点の到達可能集合。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryPotential"></a>

## 定義 `theorem16_stationaryPotential`

### 式

$$V\equiv0$$

### Lean のコメント（日本語訳）

> 監査用のトイ系の基礎ポテンシャル。

### 定義の説明

ポテンシャルを恒等的に 0 にしたトイ系です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryTCZ"></a>

## 定義 `theorem16_stationaryTCZ`

### 式

$$\mathrm{TCZ}(x_0)=\{x\mid\forall t,\ x\in\mathrm{Reach}(x_0,t)\wedge V(x)\le0\}$$

### Lean のコメント（日本語訳）

> 定理1・16 の、到達可能性とポテンシャル閾値による TCZ の定義の、定常・無制御の特殊例。初期値 x₀ からの到達可能集合は各時刻で 1 点、ポテンシャルの閾値は 0 とする。

### 定義の説明

**TCZ（目標集合）を原文どおり「到達可能 かつ ポテンシャル ≤ 閾値」で定義した**、最小の例です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_stationaryTCZ_eq_singleton"></a>

## 定理 `theorem16_stationaryTCZ_eq_singleton`

### 式

$$\mathrm{TCZ}(x_0)=\{x_0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定常例の TCZ は 1 点集合 \(\{x_0\}\)。

### 証明の概略

1. 定義を展開し、集合の外延性で \(x\in\mathrm{TCZ}\iff x=x_0\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledTrajectory"></a>

## 定義 `theorem16_intervalControlledTrajectory`

### 式

$$x(t)=u\,t$$

### Lean のコメント（日本語訳）

> 区間 TCZ 用のスカラー制御系。許容定数制御は `u∈[-1,1]`。積分軌道を `x(t)=u t` とし、この制御集合は、区間内の履歴別勾配フィードバック `u=b_h-x` も許す。

### 定義の説明

定数制御 \(u\in[-1,1]\) で \(\dot x=u\)（解 \(x=ut\)）の系です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledTrajectory_hasDerivAt"></a>

## 定理 `theorem16_intervalControlledTrajectory_hasDerivAt`

### 式

$$\dot x=u$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

解の導関数が \(u\)。

### 証明の概略

1. `hasDerivAt_id` の定数倍。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledReachable"></a>

## 定義 `theorem16_intervalControlledReachable`

### 式

$$\mathrm{Reach}(t)=\{ut\mid u\in[-1,1]\}$$

### Lean のコメント（日本語訳）

> 定数の許容制御で、時刻 t に到達する状態の集合。

### 定義の説明

時刻 \(t\) の到達可能集合：区間 \([-t,t]\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledPotential"></a>

## 定義 `theorem16_intervalControlledPotential`

### 式

$$V(x)=\bigl(x-\mathrm{clamp}_{[0,1]}(x)\bigr)^2$$

### Lean のコメント（日本語訳）

> clamp への二乗誤差で定める、連続な非負の評価コスト。零集合は `[0,1]`。

### 定義の説明

区間 \([0,1]\) からのはみ出しの二乗です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledPotential_continuous"></a>

## 定理 `theorem16_intervalControlledPotential_continuous`

### 式

$$V\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ポテンシャルの連続性。

### 証明の概略

1. clamp は連続で、二乗も連続（`fun_prop`/`Continuous.pow`）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledPotential_nonneg"></a>

## 定理 `theorem16_intervalControlledPotential_nonneg`

### 式

$$V\ge0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ポテンシャルの非負性（二乗）。

### 証明の概略

1. `sq_nonneg`。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledPotential_le_zero_iff"></a>

## 定理 `theorem16_intervalControlledPotential_le_zero_iff`

### 式

$$V(x)\le0\iff x\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零集合が \([0,1]\) であること。

### 証明の概略

1. \(V\le0\iff\) clamp との差が 0 \(\iff x\in[0,1]\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledTCZ"></a>

## 定義 `theorem16_intervalControlledTCZ`

### 式

$$\mathrm{TCZ}=\{x\mid\forall t,\ \cdots\}$$

### Lean のコメント（日本語訳）

> 原文の、到達可能・閾値の定義による、区間制御系の TCZ。

### 定義の説明

区間制御系の TCZ（到達可能かつ \(V\le0\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalControlledTCZ_eq_Icc"></a>

## 定理 `theorem16_intervalControlledTCZ_eq_Icc`

### 式

$$\mathrm{TCZ}=[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

TCZ が区間 \([0,1]\) であること。

### 証明の概略

1. 到達可能集合 \(\bigcup_t[-t,t]\) が全体になり、ポテンシャルの零集合 \([0,1]\) との共通部分が \([0,1]\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyModel"></a>

## 定義 `theorem25_selfSliceOnlyModel`

### 式

$$\text{subject}=\text{false}:\ \text{法則不変},\ \text{true}:\ \text{不変でない}$$

### Lean のコメント（日本語訳）

> 25-A(2) の主体自身に対応する 1 断面の不変性だけでは、全存在・全層を量化する 25-D は導けないことを示す、量化監査用のモデル。法則値は Bool であり、確率 SCM ではない。

### 定義の説明

**量化の監査**：主体 `false` では介入しても法則が不変（自己スライス）だが、全存在・全層についての 25-D は成り立たない、という最小モデルです。

### 証明の概略

1. `Theorem25CausalModel` の各フィールドを `Bool` の場合分けで与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyModel_satisfies_selfSliceA2"></a>

## 定理 `theorem25_selfSliceOnlyModel_satisfies_selfSliceA2`

### 式

$$\forall h,s,\ \text{intervenedLaw}(\text{false},h,s)=\text{baselineLaw}(\text{false},h)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

主体 `false` で自己スライスの不変性が成り立つ。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyModel_doesNot_satisfy25D"></a>

## 定理 `theorem25_selfSliceOnlyModel_doesNot_satisfy25D`

### 式

$$\neg\,\text{FunctionallyComplete}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全称的な 25-D は成り立たない（主体 `true` で法則が変わる）。

### 証明の概略

1. `true` の存在で、介入後の法則が基準と異なることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyProbabilityModel"></a>

## 定義 `theorem25_selfSliceOnlyProbabilityModel`

### 式

$$\text{確率版の自己スライスだけのモデル}$$

### Lean のコメント（日本語訳）

> 同じ量化の差を、$(\Gamma,Y^+)$ の同時法則をもつ、実際の有限確率モデルで再現する。`d=false` を主体自身とみなすと、その全履歴・候補介入で法則は不変だが、別の存在 `d=true` の出力は候補に依存するため、全称条件 25-D は成立しない。

### 定義の説明

上のモデルの**実際の確率測度版**です。

### 証明の概略

1. `Theorem25ProbabilityCausalModel` のフィールドを有限確率測度で具体的に与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyProbabilityModel_satisfies_selfSliceA2"></a>

## 定理 `theorem25_selfSliceOnlyProbabilityModel_satisfies_selfSliceA2`

### 式

$$\forall h,s,\ \text{intervenedJointLaw}(\text{false})=\text{baselineJointLaw}(\text{false})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率版でも自己スライスの不変性が成り立つ。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyProbabilityModel_doesNot_satisfy25D"></a>

## 定理 `theorem25_selfSliceOnlyProbabilityModel_doesNot_satisfy25D`

### 式

$$\neg\,\forall d,a,h,s,\ \text{intervenedJointLaw}=\text{baselineJointLaw}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

確率版でも全称的な 25-D は成り立たない。

### 証明の概略

1. `d=true` で、候補介入により同時法則が変わることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceOnlyProbabilityModel_hasAtman_elsewhere"></a>

## 定理 `theorem25_selfSliceOnlyProbabilityModel_hasAtman_elsewhere`

### 式

$$\mathrm{hasAtman}(\text{true})$$

### Lean のコメント（日本語訳）

> 主体自身の全履歴・全候補値で 25-A(2) 型の不変性が成り立っても、別の存在・層では、固定候補に非冗長な効果が残り得る。

### 補題の説明

**「自己スライスだけの不変性では、無我（Atman の不存在）は導けない」**という対比の例です。別の存在 `true` には `hasAtman` が成り立ちます。

### 証明の概略

1. `d=true` で、独立・固定的な個体化と、介入による法則の変化を示す。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryLayerSystem"></a>

## 定義 `theorem16_singletonHistoryLayerSystem`

### 式

$$\text{Bool 履歴ごとの一点 TCZ（全自然数層）}$$

### Lean のコメント（日本語訳）

> Bool 履歴ごとに異なる実数の一点 TCZ を、すべての自然数層へ置く toy 逆系。以下のキャリアは、上の定常・無制御系の TCZ として具体化される。射影とフィードバックは恒等写像で、一般の認知 TCZ モデルではない。

### 定義の説明

**toy の逆系**：履歴 \(h\in\)Bool に対し、各層のキャリア（その層での TCZ）を 1 点集合 \(\{h\}\)（\(h=\)true なら 1、false なら 0）とします。射影とフィードバックは恒等です。

### 証明の概略

1. `Theorem16HistoryLayerSystem` の各フィールド（キャリア・射影・フィードバック）を具体的に与え、整合条件を確認。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryLayerSystem_carrier_eq_stationaryTCZ"></a>

## 定理 `theorem16_singletonHistoryLayerSystem_carrier_eq_stationaryTCZ`

### 式

$$\text{carrier}(h,i)=\mathrm{TCZ}_{\rm stat}(\text{if }h\text{ then }1\text{ else }0)$$

### Lean のコメント（日本語訳）

> 各層の 1 点キャリアは、対応する初期値からの定常力学の TCZ そのもの。

### 補題の説明

キャリアが、上で定義した定常例の TCZ と一致すること。

### 証明の概略

1. `theorem16_stationaryTCZ_eq_singleton` で書き換え。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryLayerSystem_hasFixedPoint"></a>

## 定理 `theorem16_singletonHistoryLayerSystem_hasFixedPoint`

### 式

$$\exists x\in\varprojlim,\ \mathrm{feedback}(x)=x$$

### Lean のコメント（日本語訳）

> 上の toy 逆系は、原文の逆極限固定点存在定理を満たす。

### 補題の説明

toy 逆系に、**Core の固定点存在定理**（Fan–Glicksberg に基づく）が適用できる、という確認です。

### 証明の概略

1. Core の逆極限の固定点存在定理 `…hasFixedPoint…` に、キャリアが空でない・コンパクト凸である条件を渡す。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryLayerSystem_SC_subsingleton"></a>

## 定理 `theorem16_singletonHistoryLayerSystem_SC_subsingleton`

### 式

$$\mathrm{SC}_h\ \text{は一点集合}$$

### Lean のコメント（日本語訳）

> この toy 逆系の履歴別 SC 部分型は、一点集合である。

### 補題の説明

逆極限（SC）が 1 点なので、固定点の一意性は自明です。

### 証明の概略

1. 各層のキャリアが 1 点なので、逆極限の元も 1 点（座標がすべて \(h\) の値）。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryFixedPoints"></a>

## 定義 `theorem16_singletonHistoryFixedPoints`

### 式

$$h\mapsto x_h^\ast\in\mathrm{SC}_h$$

### Lean のコメント（日本語訳）

> 原文の逆極限存在定理が与える固定点を束ねた、Bool 履歴族。本例では SC 自体が 1 点なので、固定点の一意性は縮小性なしに従うが、これは退化した toy 例に限る。

### 定義の説明

履歴ごとの固定点の族（`HistoryFixedPoints`）。

### 証明の概略

1. 各履歴 \(h\) について、`…_hasFixedPoint` の `Classical.choose` で固定点を取る。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryFixedPoints_separate"></a>

## 定理 `theorem16_singletonHistoryFixedPoints_separate`

### 式

$$x^\ast_{\rm false}\ne x^\ast_{\rm true}$$

### Lean のコメント（日本語訳）

> 履歴別の固定点は異なる。これは、定理25-A(1) と 25.1 の toy 逆系での実例。

### 補題の説明

固定点が履歴ごとに**異なる**こと。

### 証明の概略

1. 固定点の 0 番座標が \(0\)（false）と \(1\)（true）で異なる。

----

<a id="Tomabechi.Theorem16_25.theorem16_singletonHistoryFixedPoints_noCommonFixedPoint"></a>

## 定理 `theorem16_singletonHistoryFixedPoints_noCommonFixedPoint`

### 式

$$\neg\exists s,\ \forall h,\ s\in\mathrm{SC}_h\wedge\mathrm{feedback}_h(s)=s$$

### Lean のコメント（日本語訳）

> この逆系の例で、定理25.1の、全履歴共通の固定状態の不存在を得る。

### 補題の説明

**定理25.1（共通固定状態の不存在）の toy 逆系での実例**です。

### 証明の概略

1. `…_separate` と、SC が 1 点であること（共通固定点があれば両履歴の固定点が一致して矛盾）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryLayerSystem"></a>

## 定義 `theorem16_intervalHistoryLayerSystem`

### 式

$$\text{各層 TCZ}=[0,1],\ \ \mathrm{feedback}_h\equiv\text{端点 }h$$

### Lean のコメント（日本語訳）

> 各層の TCZ を非退化な閉区間 `[0,1]` とし、履歴ごとに端点へ写す定数フィードバックを置く。射影は恒等写像なので、層間の整合性と逆極限上の連続性が成り立つ。

### 定義の説明

**非退化な逆系の例**：各層のキャリアは区間 \([0,1]\)（1 点ではない）、履歴 \(h\) のフィードバックは「端点 \(h\)（true なら 1、false なら 0）への定数写像」です。

### 証明の概略

1. `Theorem16HistoryLayerSystem` の各フィールドを具体的に与える（射影は恒等、フィードバックは定数、整合性と連続性は自明）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryLayerSystem_carrier_eq_controlledTCZ"></a>

## 定理 `theorem16_intervalHistoryLayerSystem_carrier_eq_controlledTCZ`

### 式

$$\text{carrier}(h,i)=\mathrm{TCZ}_{\rm int}=[0,1]$$

### Lean のコメント（日本語訳）

> 非退化な各層の carrier `[0,1]` は、上の制御系の実際の TCZ である。

### 補題の説明

キャリア \([0,1]\) が、定数制御系の TCZ（到達可能かつポテンシャルが 0 の集合）と一致すること。

### 証明の概略

1. `theorem16_intervalControlledTCZ_eq_Icc` で書き換え。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientCenter"></a>

## 定義 `theorem16_intervalGradientCenter`

### 式

$$b_h=\begin{cases}1&(h=\text{true})\\0&(h=\text{false})\end{cases}$$

### Lean のコメント（日本語訳）

> 各履歴 h の目標点を、強凸ポテンシャルの唯一の谷とする。

### 定義の説明

履歴 \(h\) の谷の中心（目標点）です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientPotential"></a>

## 定義 `theorem16_intervalGradientPotential`

### 式

$$V_h(x)=\tfrac12(x-b_h)^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴 \(h\) の強凸ポテンシャル（谷の底が \(b_h\)）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradient"></a>

## 定義 `theorem16_intervalGradient`

### 式

$$V_h'(x)=x-b_h$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

その勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlow"></a>

## 定義 `theorem16_intervalGradientFlow`

### 式

$$x_h(t)=b_h+e^{-t}(x-b_h)$$

### Lean のコメント（日本語訳）

> 勾配流 `x'=-(x-b_h)` の明示解。

### 定義の説明

\(\dot x=-(x-b_h)\) の閉じた解です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlow_hasDerivAt"></a>

## 定理 `theorem16_intervalGradientFlow_hasDerivAt`

### 式

$$\dot x_h=-V_h'(x_h)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

明示解が勾配流 ODE を満たす。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成と定数倍。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlow_start"></a>

## 定理 `theorem16_intervalGradientFlow_start`

### 式

$$x_h(0)=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期条件。

### 証明の概略

1. \(e^0=1\) で整理。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlow_stays"></a>

## 定理 `theorem16_intervalGradientFlow_stays`

### 式

$$x,t\in[0,1]\Rightarrow x_h(t)\in[0,1]$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\([0,1]\) の不変性（解は端点 \(b_h\) と初期値の間にある）。

### 証明の概略

1. \(x_h(t)\) は \(b_h\) と \(x\) の凸結合（\(e^{-t}\in[0,1]\)）で、どちらも \([0,1]\) に属する。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlow_control_admissible"></a>

## 定理 `theorem16_intervalGradientFlow_control_admissible`

### 式

$$b_h-x_h(t)\in[-1,1]$$

### Lean のコメント（日本語訳）

> 勾配フィードバックの入力 `b_h-x` は、TCZ 生成系と共通の許容範囲 `[-1,1]` に入る。

### 補題の説明

勾配フィードバックの制御入力が、TCZ を作る制御系と同じ許容範囲に入ること（モデルの整合性）。

### 証明の概略

1. \(b_h,x_h(t)\in[0,1]\) なので差は \([-1,1]\) に入る。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientPotential_stronglyConvex"></a>

## 定理 `theorem16_intervalGradientPotential_stronglyConvex`

### 式

$$V_h\ \text{は }[0,1]\text{ 上で 1-強凸}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**定理21の強凸性**を満たすこと。

### 証明の概略

1. `Theorem21.StronglyConvexOn` の一次不等式を \((x-y)^2\ge(x-y)^2\) で確認。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback"></a>

## 定義 `theorem16_intervalGradientFlowFeedback`

### 式

$$F_{h,i}(x)=x_h(1)=b_h+e^{-1}(x-b_h)$$

### Lean のコメント（日本語訳）

> 区間逆系の各履歴フィードバックを、上の強凸勾配流の時刻 1 写像とする。

### 定義の説明

勾配流の**時刻 1 写像**です。

### 証明の概略

1. 定義のみ（`…_stays` で区間内に収まることを添える）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback_contracting"></a>

## 定理 `theorem16_intervalGradientFlowFeedback_contracting`

### 式

$$F_{h,i}\ \text{は縮小率 }e^{-1}\ \text{の}\ \mathrm{ContractingWith}$$

### Lean のコメント（日本語訳）

> 各層の非定数フィードバック写像は、強凸勾配流の時間 1 写像なので、縮小写像である。

### 補題の説明

**縮小性**：\(|F(x)-F(y)|=e^{-1}|x-y|\)。

### 証明の概略

1. \(F(x)-F(y)=e^{-1}(x-y)\) の絶対値をとり、\(e^{-1}<1\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback_hasUniqueFixedPoint"></a>

## 定理 `theorem16_intervalGradientFlowFeedback_hasUniqueFixedPoint`

### 式

$$\exists!\,x^\ast,\ F_{h,i}(x^\ast)=x^\ast$$

### Lean のコメント（日本語訳）

> 閉区間の carrier は完備であるため、勾配流の時刻 1 写像は Banach 固定点をもつ。

### 補題の説明

区間 \([0,1]\) の完備性と縮小性から、固定点が一意に存在する（Banach）。

### 証明の概略

1. `ContractingWith.exists_fixedPoint`（完備空間上の縮小写像）と一意性。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback_iterates_tendsto_and_rate"></a>

## 定理 `theorem16_intervalGradientFlowFeedback_iterates_tendsto_and_rate`

### 式

$$F^{n}(x)\to x^\ast,\quad d(F^n(x),x^\ast)\le(e^{-1})^n\,d(x,x^\ast)$$

### Lean のコメント（日本語訳）

> 各層での反復は Banach 固定点へ収束し、誤差は `(e⁻¹)^n` 倍以下となる。これは、追加した強凸勾配流モデル内の、定理16の幾何収束節の実例。

### 補題の説明

**定理16の幾何収束節**（反復が固定点へ幾何的に収束）の具体例。

### 証明の概略

1. `ContractingWith.tendsto_iterate_fixedPoint` で収束。
2. `ContractingWith.apriori_dist_iterate_fixedPoint_le`（先験的評価）で誤差の評価。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowLayerSystem"></a>

## 定義 `theorem16_intervalGradientFlowLayerSystem`

### 式

$$\text{[0,1] の逆系、feedback}=F_{h,i}$$

### Lean のコメント（日本語訳）

> `[0,1]` TCZ の履歴別逆系で、フィードバックを、定理21型の強凸勾配流の時刻 1 写像とする。射影は恒等写像で、層間の可換性は、同じ履歴の同じ時間写像を使うことから従う。

### 定義の説明

区間逆系に、勾配流のフィードバックを載せたもの（`Theorem16HistoryLayerSystem`）です。

### 証明の概略

1. 各フィールドを具体的に与える（可換性は、各層で同じ写像であることから `rfl`）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitEquiv"></a>

## 定義 `theorem16_intervalGradientFlowInverseLimitEquiv`

### 式

$$\varprojlim\ \simeq\ [0,1]\quad(x\mapsto x_0)$$

### Lean のコメント（日本語訳）

> 恒等射影の逆極限は、第 0 座標で `[0,1]` と同型。これにより、逆極限上へ、積位相と両立する完備距離を入れられる。

### 定義の説明

逆極限（すべての座標が等しい列）が、第 0 座標を取る写像で \([0,1]\) と同型であること。

### 証明の概略

1. 恒等射影なので、逆極限の元は \(x_i=x_0\)（全 \(i\)）の列。逆写像は定数列を作る写像。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitHomeomorph"></a>

## 定義 `theorem16_intervalGradientFlowInverseLimitHomeomorph`

### 式

$$\varprojlim\ \cong\ [0,1]\ (\text{同相})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の同型が**同相写像**（位相同型）でもあること。

### 証明の概略

1. `Equiv` が連続で、逆写像も連続（積位相での座標射影の連続性と、定数列を作る写像の連続性）。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimitIsometryEquiv"></a>

## 定義 `theorem16_intervalGradientFlowInverseLimitIsometryEquiv`

### 式

$$d(x,y)=|x_0-y_0|$$

### Lean のコメント（日本語訳）

> 第 0 座標の同型で引き戻した距離は、逆極限の積部分空間位相と両立する。

### 定義の説明

逆極限に、第 0 座標の距離を入れたもの（等距離同型）。この距離は積位相と整合します。

### 証明の概略

1. `Equiv.toIsometryEquiv` 的に、距離空間構造を引き戻す。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimit_contracting"></a>

## 定理 `theorem16_intervalGradientFlowInverseLimit_contracting`

### 式

$$\mathrm{feedback}_h\ \text{は逆極限全体で縮小写像}$$

### Lean のコメント（日本語訳）

> 第 0 座標の距離は、この恒等射影の逆極限上で完備で、積部分空間位相とも両立する。この特定の対角的な逆系では、勾配流作用素も、全逆極限上の縮小写像になる。

### 補題の説明

**逆極限全体での縮小性**：この特定の「恒等射影」の逆系では、各層の縮小性がそのまま逆極限全体の縮小性になります（一般の逆系では成り立つとは限りません）。

### 証明の概略

1. 逆極限を \([0,1]\) と同一視（`…InverseLimitIsometryEquiv`）して、作用素が \(F_{h,0}\) に一致することを使う。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback_fixedValue"></a>

## 定理 `theorem16_intervalGradientFlowFeedback_fixedValue`

### 式

$$F_{h,i}(x)=x\Rightarrow x=b_h$$

### Lean のコメント（日本語訳）

> 有限時間の勾配流の固定点は、履歴別の谷中心に限られる。

### 補題の説明

固定点は谷の中心 \(b_h\) だけ。

### 証明の概略

1. \(F(x)=b_h+e^{-1}(x-b_h)=x\) から \((1-e^{-1})(x-b_h)=0\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFeedback_banachFixedPoint_value"></a>

## 定理 `theorem16_intervalGradientFlowFeedback_banachFixedPoint_value`

### 式

$$\mathrm{fixedPoint}(F_{h,i})=b_h$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Banach 固定点の値が谷の中心 \(b_h\) であること。

### 証明の概略

1. `ContractingWith.fixedPoint_isFixedPt` と上の `…_fixedValue`。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints"></a>

## 定義 `theorem16_intervalGradientFlowFixedPoints`

### 式

$$h\mapsto(\text{全座標が }b_h\text{ の列})$$

### Lean のコメント（日本語訳）

> 原文の定理16から、勾配流の時間写像の逆極限の固定点が得られ、各座標は履歴別の谷中心になる。

### 定義の説明

**定理16（固定点の存在）の適用**：Core の存在定理で固定点を取り、それがすべての座標で谷中心 \(b_h\) に等しいことを示した、履歴別の固定点の族です。

### 証明の概略

1. Core の逆極限の固定点存在定理を適用。座標ごとの固定点は `…_banachFixedPoint_value` で \(b_h\)。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoint_coordinate"></a>

## 定理 `theorem16_intervalGradientFlowFixedPoint_coordinate`

### 式

$$(x_h^\ast)_i=b_h$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定点のすべての座標が \(b_h\)。

### 証明の概略

1. `…_banachFixedPoint_value` から。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimit_iterates_tendsto"></a>

## 定理 `theorem16_intervalGradientFlowInverseLimit_iterates_tendsto`

### 式

$$\mathrm{feedback}_h^n(x)\to x_h^\ast\ \ (\text{積位相})$$

### Lean のコメント（日本語訳）

> 恒等射影の勾配流の逆系では、層別の反復の収束を、積位相で逆極限全体へ移せる。各座標の Banach 収束から `tendsto_pi_nhds` を使う。逆極限全体の距離に関する一様な縮小評価を主張するものではない。

### 補題の説明

反復が**積位相で**固定点に収束する（各座標ごとの収束から従う）。一様な距離評価は主張しません。

### 証明の概略

1. `tendsto_pi_nhds`（積位相の収束は各座標の収束と同値）。
2. 各座標は `…_iterates_tendsto_and_rate` の Banach 収束。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowInverseLimit_coordinate_rate"></a>

## 定理 `theorem16_intervalGradientFlowInverseLimit_coordinate_rate`

### 式

$$\bigl|(\mathrm{feedback}^n x)_i-(x^\ast)_i\bigr|\le e^{-n}\,\bigl|x_i-(x^\ast)_i\bigr|$$

### Lean のコメント（日本語訳）

> 逆極限の反復は、各層の座標ごとに、同じ幾何率 `exp(-n)` で誤差が減る。初期差に一様な上界がないため、これは積全体の一様距離評価ではなく、座標別の評価である。

### 補題の説明

座標ごとに幾何率 \(e^{-n}\) で収束する評価です（**座標別**であって、積全体の一様距離ではない）。

### 証明の概略

1. 各座標で `…_iterates_tendsto_and_rate` の評価を適用。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalGradientFlowFixedPoints_separate"></a>

## 定理 `theorem16_intervalGradientFlowFixedPoints_separate`

### 式

$$x^\ast_{\rm false}\ne x^\ast_{\rm true}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴別の固定点が異なる（谷中心 0 と 1）。

### 証明の概略

1. 座標 0 が \(b_{\rm false}=0\)、\(b_{\rm true}=1\) で異なる。

----

<a id="Tomabechi.Theorem16_25.theorem25_firstConclusion_of_intervalGradientFlowFixedPoints"></a>

## 定理 `theorem25_firstConclusion_of_intervalGradientFlowFixedPoints`

### 式

$$\text{固定点が分離}\Rightarrow\neg\exists s,\ \text{共通の固定状態}$$

### Lean のコメント（日本語訳）

> 強凸勾配流の履歴別逆極限固定点を、25-A(1) の履歴分離条件から、定理25.1 へ接続する。この toy モデルでは、別の定理で、固定点の座標が履歴中心になることを示している。

### 補題の説明

**定理25第1結論**への接続（履歴ごとに固定点が別なら、共通固定状態は存在しない）。

### 証明の概略

1. Core の `theorem25_firstConclusion_of_…`（履歴別固定点が分離していれば共通の固定状態が存在しない）に `hsep` を渡す。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlow_firstConclusion"></a>

## 定理 `theorem25_intervalGradientFlow_firstConclusion`

### 式

$$\neg\exists s,\ \text{共通の固定状態（履歴 false, true）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配流の区間モデルでの**定理25第1結論**そのもの。

### 証明の概略

1. `…_FixedPoints_separate` を `theorem25_firstConclusion_of_intervalGradientFlowFixedPoints` に渡す。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryFixedPoints"></a>

## 定義 `theorem16_intervalHistoryFixedPoints`

### 式

$$h\mapsto\text{(定数写像の固定点)}$$

### Lean のコメント（日本語訳）

> 非退化な区間の逆極限から、直接作る履歴別の固定点族。各 SC には連続な多数の状態があるが、フィードバックが、履歴端点への定数写像なので、固定点は一意で、2 履歴の固定点の値は異なる。縮小定数のメトリックの証明ではなく、この特殊な定数作用素の方程式から一意性を示している。

### 定義の説明

`theorem16_intervalHistoryLayerSystem`（定数フィードバック）の固定点族です。縮小性ではなく、**定数写像の固定点は定数そのもの**という方程式から一意性が出ます。

### 証明の概略

1. Core の固定点の存在定理（コンパクト・凸）を適用して固定点を取る。一意性は \(F(s)=s\iff s=\) 定数。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryFixedPoint_coordinate"></a>

## 定理 `theorem16_intervalHistoryFixedPoint_coordinate`

### 式

$$(x^\ast_h)_0=\begin{cases}1&(h)\\0&(\neg h)\end{cases}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定点の第 0 座標が履歴端点。

### 証明の概略

1. 定数写像の固定点方程式から。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryFixedPoints_separate"></a>

## 定理 `theorem16_intervalHistoryFixedPoints_separate`

### 式

$$x^\ast_{\rm false}\ne x^\ast_{\rm true}$$

### Lean のコメント（日本語訳）

> 区間 TCZ では、状態空間は非退化だが、層フィードバックが定数なので、固定点は履歴依存。

### 補題の説明

固定点が履歴ごとに異なること。

### 証明の概略

1. 第 0 座標が \(0\) と \(1\) で異なる。

----

<a id="Tomabechi.Theorem16_25.theorem16_intervalHistoryFixedPoints_noCommonFixedPoint"></a>

## 定理 `theorem16_intervalHistoryFixedPoints_noCommonFixedPoint`

### 式

$$\neg\exists s,\ \forall h,\ s\in\mathrm{SC}_h\wedge\mathrm{feedback}_h(s)=s$$

### Lean のコメント（日本語訳）

> 非退化な区間の逆系で、定理25.1の、全履歴共通の固定状態の不存在が成り立つ。

### 補題の説明

**非退化な区間でも**、全履歴に共通の固定状態は存在しない（定理25.1）。

### 証明の概略

1. `…_separate` と、固定点の一意性から（共通固定点があれば両履歴の固定点と一致して矛盾）。

----

<a id="Tomabechi.Theorem16_25.theorem25_relationalStateCoherent_afterIntervention"></a>

## 定理 `theorem25_relationalStateCoherent_afterIntervention`

### 式

$$\text{25-D 型の法則不変性}\Rightarrow P\bigl(\text{観測された関係状態}=\text{実際の関係状態}\bigr)=1\ \text{（介入後も）}$$

### Lean のコメント（日本語訳）

> 25-D の同時法則の不変性は、完全な Γ 観測の確率 1 の整合も、介入後に保存する。

### 補題の説明

25-D（介入しても同時法則が変わらない）ならば、**介入後でも「観測された関係状態が実際の関係状態に一致する」確率が 1** のまま、という定理です（25-C3 の統合モデルでの整合性の保存）。

### 証明の概略

1. 基準の法則で、観測と実際の関係状態が確率 1 で一致する（C3 の整合性の仮定）。
2. 25-D の仮定 `hcomplete` で、介入後の法則 = 基準の法則なので、同じ事象の確率が 1。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceCountermodelSCM"></a>

## 定義 `theorem25_twoExistenceCountermodelSCM`

### 式

$$D=\text{Bool},\ \text{候補 }\Sigma\in\text{Bool},\ \text{出力}=\Sigma$$

### Lean のコメント（日本語訳）

> 25-B/C と基準観測の整合だけでは 25-D は出ず、(25.2) も従わないことを示す有限例。存在は 2 点、抽象度は 1 層とし、全存在が共通の 1 元の上位表現をもち、相互関係グラフは連結である。一方、候補変数を false に固定した基準の構造方程式へ true を介入すると、将来出力が false から true に変わる。

### 定義の説明

**25-D の必要性を示す有限の反例**です。25-B（全層のプロファイル）と 25-C（関係の網）が成り立っていても、候補 \(\Sigma\) への介入が将来出力を変える構造方程式があり得ます（その場合 25-D は成り立ちません）。

### 証明の概略

1. `Theorem25StructuralCausalModel` の各フィールドを、存在 `Bool`、層 `Unit` で具体的に与える。基準では候補を `false` に固定、出力方程式は候補をそのまま出力。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistencePresenceRelations"></a>

## 定義 `theorem25_twoExistencePresenceRelations`

### 式

$$\text{全存在が共通の上位表現、相互関係グラフは連結}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の反例の**25-B/C の部分**（存在の表現と関係のグラフ）を与える `Theorem25PresenceRelationModel` です。

### 証明の概略

1. 各フィールドを具体的に与える（表現は 1 元、関係グラフは完全グラフ）。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceCountermodel"></a>

## 定義 `theorem25_twoExistenceCountermodel`

### 式

$$\text{25-B/C + 基準観測整合 の統合モデル}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

確率 SCM と presence/relations を統合した `Theorem25IntegratedModel`（反例）。

### 証明の概略

1. `theorem25_twoExistenceCountermodelSCM` と `theorem25_twoExistencePresenceRelations` を束ね、基準観測の整合を確認する。

----

<a id="Tomabechi.Theorem16_25.Theorem25TwoExistenceGamma"></a>

## 定義 `Theorem25TwoExistenceGamma`

### 式

$$\Gamma=(Z,\mathrm{Vert},\mathrm{Inc})$$

### Lean のコメント（日本語訳）

> 有限 B/C 反例を 25-C3 の完全な Γ 型にも載せた、構造方程式モデル。状態変数そのものを `(Z,Vert,Inc)` とし、基準観測の整合を満たす。

### 定義の説明

関係状態 \(\Gamma\)（表現 \(Z\)、頂点、接続関係の組）の型です。

### 証明の概略

1. 型の定義のみ。

----

<a id="Tomabechi.Theorem16_25.instance@L2302"></a>

## インスタンス `instance@L2302`

### 式

$$\text{可測空間}=\text{離散（}\top\text{）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`Theorem25TwoExistenceGamma` に最大の（離散）可測構造を入れるインスタンスです。有限なので任意の集合が可測。

### 証明の概略

1. `⊤`（最大の σ 代数）。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceRandomizedSCM"></a>

## 定義 `theorem25_twoExistenceRandomizedSCM`

### 式

$$\Sigma\sim\mathrm{Unif}(\text{Bool}),\ \Sigma\perp\Gamma\ (\text{各固定履歴で})$$

### Lean のコメント（日本語訳）

> 候補 Σ を一様な Bool 外生変数にした、非退化な有限 SCM。各固定履歴で Σ は関係状態 Γ と独立だが、`do(Σ=s)` で出力が変わる。これは 25-D の必要性を示す有限反例で、H 自体の同時分布はモデル化しない。

### 定義の説明

候補が**確率的**（一様）で、関係状態と独立でありながら、\(\mathrm{do}(\Sigma=s)\) が出力を変える。「独立性だけでは無我は導けず、25-D が必要」という確率版の反例です。

### 証明の概略

1. `Theorem25RandomizedStructuralCausalModel` の各フィールドを、外生 Bool と一様測度で具体的に与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceGlobalHistorySCM"></a>

## 定義 `theorem25_twoExistenceGlobalHistorySCM`

### 式

$$(\Sigma,H)\in\text{Bool}\times\text{Bool}\ \text{独立},\ Y^+=\Sigma$$

### Lean のコメント（日本語訳）

> Σ と大域履歴 H を独立な Bool 座標としてもつ有限 SCM。Γ は H と存在 d から 25-B/C の関係モデルで定め、将来出力は、介入候補 Σ そのものとする。

### 定義の説明

候補と**大域履歴**が同時に確率的で独立な反例です。

### 証明の概略

1. `Theorem25GlobalHistorySCM` のフィールドを、外生空間 `Bool × Bool` で具体的に与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceGlobalHistory_candidate_has_positive_mass"></a>

## 定理 `theorem25_twoExistenceGlobalHistory_candidate_has_positive_mass`

### 式

$$\forall s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各候補値 \(s\) の確率が正であること（`candidateHasPositiveMass`）。介入の対象が確率 0 の値でないことの確認です。

### 証明の概略

1. 一様測度で各値の確率は \(1/2\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceGlobalHistory_hasAtman"></a>

## 定理 `theorem25_twoExistenceGlobalHistory_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false})$$

### Lean のコメント（日本語訳）

> ランダムな大域履歴と候補の同時独立性を満たしていても、Σ 介入が将来出力を変える有限例がある。Γ は履歴一定のため、ここでは、大域独立性と 25-D の論理的独立を示す。

### 補題の説明

**独立性だけでは無我は出ない**：候補と履歴が独立でも、\(\Sigma\) 介入が出力を変えるので `hasAtman`（操作的アートマンの存在）が成り立ちます。

### 証明の概略

1. 独立・固定的な個体化の条件を確認。
2. \(\mathrm{do}(\Sigma=s)\) で出力が \(s\) に変わるので、介入後の法則が基準の法則と異なる。

----

<a id="Tomabechi.Theorem16_25.Theorem25HistoryDependentGamma"></a>

## 定義 `Theorem25HistoryDependentGamma`

### 式

$$\Gamma_h\ \text{（履歴 }h\text{ で関係ラベルが変わる）}$$

### Lean のコメント（日本語訳）

> 履歴 Bool を関係の役割ラベルへ反映する、有限の 25-B/C 構造。全存在は、全履歴で連結しつつ、実際の関係ラベルは履歴に応じて変わる。

### 定義の説明

関係状態 \(\Gamma\) の型で、**履歴 \(h\) に応じて関係ラベルが変わる**ものです。

### 証明の概略

1. 型の定義のみ。

----

<a id="Tomabechi.Theorem16_25.instance@L2462"></a>

## インスタンス `instance@L2462`

### 式

$$\text{可測空間}=\text{離散（}\top\text{）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`Theorem25HistoryDependentGamma` に離散の可測構造を入れるインスタンス。

### 証明の概略

1. `⊤`。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentPresenceRelations"></a>

## 定義 `theorem25_historyDependentPresenceRelations`

### 式

$$\text{関係ラベルが履歴に依存する presence/relations モデル}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

履歴 `Bool` に応じて関係状態が変わる `Theorem25PresenceRelationModel`。

### 証明の概略

1. 各フィールドを具体的に与える（履歴で役割ラベルを切り替える）。

----

<a id="Tomabechi.Theorem16_25.theorem25_singletonInverseLimitStateCode"></a>

## 定義 `theorem25_singletonInverseLimitStateCode`

### 式

$$\mathrm{code}(d,a,x)=\text{（}x_0\in\{0,1\}\text{ から履歴を復元した関係状態）}$$

### Lean のコメント（日本語訳）

> 先の定理16の toy 逆系の固定点の値から、履歴に依存する 25-C の関係状態を実際に符号化する。`x 0` が 0/1 のどちらかで履歴を復元し、presence model の Γ 状態と一致する。

### 定義の説明

**逆極限（定理16）→ 関係状態（定理25）の符号化**：固定点の 0 番座標 \(x_0\) が 0 か 1 かで履歴を読み取り、その履歴の関係状態を返す。

### 証明の概略

1. `x 0 = 1` なら履歴 `true`、そうでなければ `false` として、`relationalState d h a` を返す（`decide`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_singletonInverseLimitStateCode_matches"></a>

## 定理 `theorem25_singletonInverseLimitStateCode_matches`

### 式

$$\mathrm{code}(d,a,x^\ast_h)=\Gamma_{d,h,a}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

符号化が、履歴 \(h\) の固定点に対して正しい関係状態を返すこと。

### 証明の概略

1. 固定点の 0 番座標は \(h\) に対応する値（0 または 1）。符号化の定義を展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_singletonInverseLimitMeasuredC3Model"></a>

## 定義 `theorem25_singletonInverseLimitMeasuredC3Model`

### 式

$$\text{逆極限固定点}\to\text{25-B/C3 共有確率モデル}\to\text{25-D}\to\text{25.2}$$

### Lean のコメント（日本語訳）

> 逆極限固定点 → 25-B/C3 の共有確率モデル → 25-D → 25.2 の、具体的な toy の接続。履歴・存在・層は有限 Bool、TCZ 逆系は実数上の 1 点集合であり、一般の認知モデルの証明ではない。候補の非干渉は、出力が固定点の符号化だけに依存する設計条件として置く。

### 定義の説明

**定理16→25 の接続を、最後まで通した toy**：固定点の符号化（関係状態）を出力に使い、出力が候補に依存しない設計にすることで 25-D が成り立つ測度つき C3 モデルを構成します。候補非干渉は**設計条件**（導いたものではない）です。

### 証明の概略

1. `Theorem25MeasuredSharedGlobalHistoryC3Model` の各フィールドを、固定点の符号化（`…StateCode`）で与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_singletonInverseLimitMeasuredC3Model_noAtman"></a>

## 定理 `theorem25_singletonInverseLimitMeasuredC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 上の toy 構成は、実際に定理25の第 2 結論を満たす。

### 補題の説明

構成したモデルで**無我（Atman の不存在）**が成り立つこと（25-D の設計条件による）。

### 証明の概略

1. 25-D（候補介入で法則が不変）を、出力が固定点符号化だけに依存することから示し、`theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`（Core の変種）を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitStateCode"></a>

## 定義 `theorem25_intervalInverseLimitStateCode`

### 式

$$\mathrm{code}(d,a,x)=\text{（}x_0\text{ から履歴を復元）}$$

### Lean のコメント（日本語訳）

> 非退化な区間 TCZ の逆極限固定点を、25-C3 の関係状態へ写す符号化。固定点の第 0 座標が履歴の端点 0/1 であることを用いる。

### 定義の説明

区間逆系版の符号化です。

### 証明の概略

1. `x 0 = 1` かどうかで履歴を復元。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitStateCode_matches"></a>

## 定理 `theorem25_intervalInverseLimitStateCode_matches`

### 式

$$\mathrm{code}(d,a,x^\ast_h)=\Gamma_{d,h,a}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

区間逆系の固定点に対する符号化の正しさ。

### 証明の概略

1. `theorem16_intervalHistoryFixedPoint_coordinate`（第 0 座標が端点）を使う。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitMeasuredC3Model"></a>

## 定義 `theorem25_intervalInverseLimitMeasuredC3Model`

### 式

$$\text{区間 TCZ 逆系}\to\text{測度つき 25-B/C3}$$

### Lean のコメント（日本語訳）

> 非退化な区間 TCZ 逆系の固定点コードを、測度つき 25-B/C3 モデルへ接続する。25-D と 25.2 は、この構成では、候補に依存しない出力方程式から成立するため、一般の認知モデルの構造方程式から 25-D を導いた結果ではない。

### 定義の説明

区間逆系版の C3 モデル。**25-D は出力方程式の設計から成立**します（一般モデルからの導出ではない）。

### 証明の概略

1. `theorem25_singletonInverseLimitMeasuredC3Model` と同じ型の構成を、`Theorem25MeasuredSharedGlobalHistoryC3Model.ofHistoryFixedPoints` で、区間逆系の固定点族 `theorem16_intervalHistoryFixedPoints`、符号化 `theorem25_intervalInverseLimitStateCode`（とその一致 `…_matches`）、関係状態 `theorem25_historyDependentPresenceRelations` に対して行う。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitMeasuredC3Model_noAtman"></a>

## 定理 `theorem25_intervalInverseLimitMeasuredC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 非退化な区間 TCZ モデルでも、固定点コードから構成した 25.2 が成り立つ。

### 補題の説明

区間逆系の C3 モデルでも無我が成り立つ。

### 証明の概略

1. 25-D と `theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowStateCode"></a>

## 定義 `theorem25_intervalGradientFlowStateCode`

### 式

$$\mathrm{code}(d,a,x)=\text{（勾配流の固定点の }x_0\text{ から履歴を復元）}$$

### Lean のコメント（日本語訳）

> 勾配流版の逆極限固定点から、25-C3 の状態を符号化する。

### 定義の説明

勾配流の逆系版の符号化です。

### 証明の概略

1. `x 0` の値（0 か 1）で履歴を復元。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowStateCode_matches"></a>

## 定理 `theorem25_intervalGradientFlowStateCode_matches`

### 式

$$\mathrm{code}(d,a,x^\ast_h)=\Gamma_{d,h,a}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配流の固定点に対する符号化の正しさ。

### 証明の概略

1. `theorem16_intervalGradientFlowFixedPoint_coordinate`（全座標が谷中心）を使う。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowMeasuredC3Model"></a>

## 定義 `theorem25_intervalGradientFlowMeasuredC3Model`

### 式

$$\text{勾配流の逆極限固定点}\to\text{共有測度 C3 モデル}$$

### Lean のコメント（日本語訳）

> 強凸勾配流の逆極限固定点から構成した、共有測度 C3 モデル。25-D と 25.2 まで接続する。候補と出力は Unit 値なので、この例の因果の非干渉は構成上のものである。

### 定義の説明

**定理21（強凸勾配流）→ 16 → 25 を通した toy**。候補・出力が `Unit`（情報なし）なので、因果の非干渉は構成から自明です。

### 証明の概略

1. `theorem25_intervalGradientFlowStateCode` で関係状態を与え、候補・出力を `Unit` に取る。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowMeasuredC3Model_noAtman"></a>

## 定理 `theorem25_intervalGradientFlowMeasuredC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配流版の C3 モデルで無我が成り立つ。

### 証明の概略

1. 候補・出力が `Unit` なので 25-D が自明に成り立ち、`theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`（Core の変種） を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints"></a>

## 定義 `theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints`

### 式

$$\text{任意の Bool 履歴の逆極限固定点族}\ F\ \to\ \text{非定数の候補・出力をもつ共有 C3 モデル}$$

### Lean のコメント（日本語訳）

> 非定数の候補・出力を持つ共有 C3 モデルを、任意の Bool 履歴の逆極限固定点族から作る。符号化の一致と候補の独立性は、明示的な条件として受け取る。

### 定義の説明

**非定数の候補・出力を持つ**版：固定点の族 \(F\) と、符号化 `code`（`hCode`）、出力が履歴に一致する条件 `hOutput` を受け取ります。

### 証明の概略

1. 外生を `Bool × Bool`（候補、履歴）にし、出力方程式を固定点由来の値（履歴）として与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model"></a>

## 定義 `theorem25_intervalGradientFlowRandomizedMeasuredC3Model`

### 式

$$F=\text{勾配流の固定点族}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の `…fromFixedPoints` に、勾配流の固定点族を入れたインスタンス。

### 証明の概略

1. `theorem25_intervalRandomizedMeasuredC3Model_fromFixedPoints` に勾配流の固定点族、符号化の一致、出力が履歴に一致することを渡す。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedSelfProcessSCM"></a>

## 定義 `theorem25_intervalGradientFlowRandomizedSelfProcessSCM`

### 式

$$
\text{共有 SCM の外生法則・履歴・候補・状態出力の構造式}\ \Rightarrow\ \text{25-A(2) の自己過程 SCM}
$$

### Lean のコメント（日本語訳）

> 同じ履歴別固定点 C3-SCM を、25-A(2) の自己過程 SCM として読む射影。外生法則・履歴変数・候補変数・状態出力の構造式を、元の共有 SCM からそのまま取る。

### 定義の説明

上の勾配流の固定点族から作った**共有 SCM**（`theorem25_intervalGradientFlowRandomizedMeasuredC3Model`）を、定理 25 の条件 25-A(2) を述べるための**自己過程 SCM**（`Theorem25SelfProcessSCM`）として読み替えます。外生の法則・入力の履歴の変数・候補の変数・状態と出力の構造式は、すべて元の共有 SCM のものを**そのまま**使い、別の SCM を作り直しません（主体 \(d\)・行為 \(a\) は `false` に固定して取り出します）。基準の方程式は、候補変数を出力方程式に入れたもの、介入した方程式は、候補を任意の値 \(s\) に置き換えたものです。

### 証明の概略

1. 各フィールドに、元の共有 SCM の対応するフィールド（外生法則・`globalHistory`・`candidateVariable`・`stateEquation`・`outputEquation`・可測性の補題）を代入する。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2"></a>

## 定理 `theorem25_intervalGradientFlowRandomizedSelfProcessSCM_satisfies25A2`

### 式

$$
\mathrm{Condition25A2}:\quad \text{候補への介入は }(\Gamma,Y^+)\text{ の同時法則を変えない}
$$

### Lean のコメント（日本語訳）

> 上の射影で定理 25-A(2) を証明する。候補と入力履歴は同じ積確率空間の独立座標であり、介入前後の状態・出力は固定点符号化で一致する。

### 補題の説明

上の自己過程 SCM について、条件 **25-A(2)** が成り立つことです。候補（二値）と入力の履歴は、同じ積の確率空間（一様測度の積）の**独立な座標**です。介入した方程式と、基準の方程式は、状態が履歴だけで決まり、出力も固定点の符号化で履歴に一致するので、候補を置き換えても、\((\Gamma,Y^+)\) の同時法則は変わりません。

### 証明の概略

1. 25-A(2) を与える一般の補題 `condition25A2` を適用する。
2. 候補と履歴が独立であること：一様測度の積の座標なので、`indepFun_prod`。
3. 介入前後の同時法則の一致：二つの像の測度が、各点で（出力が候補に依らず固定点の値である）等しいので、`map_congr`。点ごとの等式は、固定点の座標の補題（`theorem16_intervalGradientFlowFixedPoint_coordinate`）による。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomizedMeasuredC3Model_noAtman"></a>

## 定理 `theorem25_intervalGradientFlowRandomizedMeasuredC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

非定数の候補・出力のモデルでも無我が成り立つ（出力が候補に依存しないため）。

### 証明の概略

1. 出力が履歴だけの関数なので 25-D が成り立ち、`theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`（Core の変種） を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass"></a>

## 定理 `theorem25_intervalGradientFlowRandomized_candidate_has_positive_mass`

### 式

$$\forall s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

候補が実際に確率的である（各値の確率が正）こと。

### 証明の概略

1. 一様測度で各値の確率は \(1/2\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalGradientFlowRandomized_output_eq_history"></a>

## 定理 `theorem25_intervalGradientFlowRandomized_output_eq_history`

### 式

$$Y^+(d,a,h,u,s)=h$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

出力方程式が履歴 \(h\) に等しい（候補 \(s\) と外生 \(u\) に依存しない）。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitRandomizedMeasuredC3Model"></a>

## 定義 `theorem25_intervalInverseLimitRandomizedMeasuredC3Model`

### 式

$$\text{候補と履歴が独立な Bool 座標、出力}=\text{固定点由来}$$

### Lean のコメント（日本語訳）

> 候補と履歴を独立な Bool 座標として持ち、固定点由来の出力を、履歴に応じて 0/1 へ変える。したがって、候補変数・将来出力はいずれも非定数だが、do 介入は固定点由来の出力を変えない。

### 定義の説明

区間逆系版の、非定数の候補・出力をもつ C3 モデル（候補への介入は出力を変えない）。

### 証明の概略

1. `…fromFixedPoints` に区間逆系の固定点族 `theorem16_intervalHistoryFixedPoints` を入れる。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitRandomizedMeasuredC3Model_noAtman"></a>

## 定理 `theorem25_intervalInverseLimitRandomizedMeasuredC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 非定数の候補・履歴依存の出力を持つ、区間逆系 C3 モデルでも、25-D から 25.2 が従う。

### 補題の説明

非定数の候補と出力をもつ区間逆系の C3 モデルで、無我が成り立つ。

### 証明の概略

1. 出力が固定点由来で候補に依存しないので 25-D が成り立ち、`theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model_outputAENoninterference`（Core の変種）を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitRandomized_candidate_has_positive_mass"></a>

## 定理 `theorem25_intervalInverseLimitRandomized_candidate_has_positive_mass`

### 式

$$\forall s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

> このモデルの候補は、各値に正の確率を持つため、25.2 は、候補値の空事象化に頼らない。

### 補題の説明

候補の各値が確率正で起こるので、「候補値の事象が確率 0 だから介入しても関係ない」という抜け道を使っていない、という確認です。

### 証明の概略

1. 一様測度で各値の確率は \(1/2\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_intervalInverseLimitRandomized_output_eq_history"></a>

## 定理 `theorem25_intervalInverseLimitRandomized_output_eq_history`

### 式

$$Y^+(d,a,h,u,s)=h$$

### Lean のコメント（日本語訳）

> 各履歴のもとで、候補の介入値によらず、将来出力は、逆極限固定点の端点値に等しい。したがって、出力は、履歴 false/true で 0/1 と変わる一方、候補介入では変化しない。

### 補題の説明

出力は履歴で決まり、候補にも外生ノイズにも依存しない。

### 証明の概略

1. 出力方程式の定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalSCM"></a>

## 定義 `theorem25_historyDependentGlobalSCM`

### 式

$$\text{履歴に応じて }\Gamma\text{ の役割辺が変わる大域履歴 SCM}$$

### Lean のコメント（日本語訳）

> 履歴に応じて Γ の役割辺が変わる、大域履歴 SCM。候補 Σ は、大域履歴と履歴別 Γ の組から独立な、直積座標である。

### 定義の説明

25-D を**課さない**履歴依存の大域履歴 SCM（反例用）。

### 証明の概略

1. `Theorem25GlobalHistorySCM` のフィールドを、外生 `Bool × Bool`、履歴依存の関係状態で与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalSCM"></a>

## 定義 `theorem25_selfSliceA2GlobalSCM`

### 式

$$d=\text{false}:\text{候補介入が法則を変えない},\ \ d=\text{true}:\text{候補が因果的に作用}$$

### Lean のコメント（日本語訳）

> 主体の断面 `d=false` では、候補介入が出力法則を変えない一方、別の存在 `d=true` では、候補が因果的に作用する、大域履歴 SCM。

### 定義の説明

**自己スライスだけ 25-A(2) が成り立つ**大域履歴 SCM（確率版）。

### 証明の概略

1. 出力方程式を、存在 `d` で場合分け（`false` では候補を無視、`true` では候補を出力）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalSCM_satisfies_selfA2"></a>

## 定理 `theorem25_selfSliceA2GlobalSCM_satisfies_selfA2`

### 式

$$\forall a,h,s,\ \text{intervenedJointLaw}(\text{false},a,h,s)=\text{baselineJointLaw}(\text{false},a,h)$$

### Lean のコメント（日本語訳）

> γ を自己過程の表現として読む場合、固定した主体の断面 `d=false` では、25-A(2) 型の `(Γ,Y⁺)` の同時法則の不変性が、全履歴・全候補値で成立する。

### 補題の説明

主体断面 `d=false` での同時法則の不変性（自己版 25-A(2)）。

### 証明の概略

1. `d=false` で出力方程式が候補を無視するため、介入後の同時法則が基準と一致。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2SharedSCM"></a>

## 定義 `theorem25_selfSliceA2SharedSCM`

### 式

$$\text{外生法則を共有する型へ}$$

### Lean のコメント（日本語訳）

> 25-B/C3 の統合型へ渡すため、A(2) 変種の SCM を、1 つの外生法則共有型にする。

### 定義の説明

上の SCM を、すべての索引で**同じ外生法則**を使う共有型（`Theorem25SharedGlobalHistorySCM`）に直したもの。

### 証明の概略

1. 外生法則を一様積法則に固定して詰め直す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentSharedSCM"></a>

## 定義 `theorem25_historyDependentSharedSCM`

### 式

$$\text{25-D を課さない履歴依存 SCM を共有法則型へ}$$

### Lean のコメント（日本語訳）

> 25-D を課さない履歴依存 SCM も、全索引で同じ一様積法則を使う、共有法則型にできる。

### 定義の説明

`theorem25_historyDependentGlobalSCM` の共有法則型。

### 証明の概略

1. 外生法則を一様積法則に固定して詰め直す。

----

<a id="Tomabechi.Theorem16_25.theorem25_uniformBool"></a>

## 定義 `theorem25_uniformBool`

### 式

$$\mu=\mathrm{Unif}(\text{Bool})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Bool 上の一様測度（`private`）。

### 証明の概略

1. `ProbabilityTheory.uniformOn Set.univ`。

----

<a id="Tomabechi.Theorem16_25.theorem25_uniformUniv_measurePreserving_of_equiv"></a>

## 定理 `theorem25_uniformUniv_measurePreserving_of_equiv`

### 式

$$e:\Omega\simeq\Omega\ \Rightarrow\ \text{一様法則を保存}$$

### Lean のコメント（日本語訳）

> 有限離散空間上の一様法則は、任意の可測な全単射で保存される。有限群の平行移動が一様ノイズの対称性となる際の基礎補題。

### 補題の説明

一様分布は、全単射による入れ替えで変わらない（「一様ノイズの対称性」の基礎）。

### 証明の概略

1. `MeasurePreserving` を、各点の測度が \(1/|\Omega|\) で等しいことと、全単射の下での点の対応から示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_uniformUniv_addTranslation_measurePreserving"></a>

## 定理 `theorem25_uniformUniv_addTranslation_measurePreserving`

### 式

$$x\mapsto x+g\ \text{は一様法則を保存}$$

### Lean のコメント（日本語訳）

> 有限加法群の一様ノイズは、平行移動で不変。有限群ノイズの候補依存な再配置を構成するとき、Bool の xor に依存しない一般形として用いる。

### 補題の説明

有限加法群での平行移動が一様法則を保存すること（上の補題の特殊化）。

### 証明の概略

1. `x ↦ x + g` は全単射（`Equiv.addRight`）で可測なので、`theorem25_uniformUniv_measurePreserving_of_equiv` を適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_boolXorMeasurePreserving"></a>

## 定理 `theorem25_boolXorMeasurePreserving`

### 式

$$x\mapsto x\oplus b\ \text{は一様法則を保存}$$

### Lean のコメント（日本語訳）

> Bool の一様法則は、固定ビットとの xor で保存される。

### 補題の説明

Bool 上の xor（= \(\mathbb Z/2\) の加法）が一様測度を保存します（`private`）。

### 証明の概略

1. 上の一般補題の `Bool` 版。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM"></a>

## 定義 `theorem25_historyDependentMaskingSharedSCM`

### 式

$$Y^+=\bigl(\text{候補を含む式}\bigr)\oplus\text{一様ノイズ}$$

### Lean のコメント（日本語訳）

> 候補値は出力方程式に実際に入るが、独立な一様ノイズがあるため、候補介入後も `(Γ,Y⁺)` の同時法則が変わらない、共有法則 SCM。

### 定義の説明

**ノイズでマスクした出力**：候補値は出力方程式に入りますが、独立な一様ノイズ（xor）で隠されるので、介入しても出力の**分布**は変わりません（25-D が成り立つ）。

### 証明の概略

1. 出力方程式を `xor ノイズ (xor 候補 …)` の形で与え、外生を `Bool × (Bool × Bool)` にする。

----

<a id="Tomabechi.Theorem16_25.theorem25_maskingChange_measurePreserving"></a>

## 定理 `theorem25_maskingChange_measurePreserving`

### 式

$$\tau_s(u_1,(u_2,u_3))=\bigl(u_1,(u_2,u_3\oplus u_1\oplus s)\bigr)\ \text{は一様積法則を保存}$$

### Lean のコメント（日本語訳）

> ノイズ座標を候補値に応じて xor 変換する写像は、独立な一様積法則を保存する。

### 補題の説明

マスキングで使う**外生ノイズの変換**が、一様積法則を保存すること（`private`）。

### 証明の概略

1. 第 3 座標の xor は一様測度を保存し（`theorem25_boolXorMeasurePreserving`）、積測度の他の座標は固定。積測度の保存を `MeasurePreserving.prod` 型で組み立てる。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry`

### 式

$$\forall d,a,h,s,\ \exists\tau\ \text{測度保存},\ (\Gamma,Y^+_s)\circ\tau=(\Gamma,Y^+_{\text{natural}})$$

### Lean のコメント（日本語訳）

> マスキング構造方程式の、候補介入を基準過程へ移す、外生ノイズの測度保存対称性。

### 補題の説明

介入後の過程 \((\Gamma,Y^+_s)\) と、自然な候補での過程 \((\Gamma,Y^+)\) が、**測度を保存する外生の変換 \(\tau\) でつながる**ことを述べます。これが 25-D（同時法則の不変性）の本質です。

### 証明の概略

1. \(\tau=\tau_s\)（`theorem25_maskingChange_measurePreserving`）を取る。
2. 出力方程式の xor が \(\tau\) で打ち消し合うことを、各ビットの場合分けで確認。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_satisfies25D"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_satisfies25D`

### 式

$$\forall d,a,h,s,\ \text{intervenedJointLaw}=\text{baselineJointLaw}$$

### Lean のコメント（日本語訳）

> ノイズマスキングの構造方程式から、全履歴・全候補介入について 25-D を導く。

### 補題の説明

**25-D を構造方程式から導出**（このマスキング SCM の場合）。

### 証明の概略

1. `…_measurePreservingSymmetry` の \(\tau\) による像測度の等式から、同時法則が等しい（Core の `theorem25_globalHistorySCM_functionalCompleteness_of_measurePreservingSymmetry`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_output_depends_on_candidate"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_output_depends_on_candidate`

### 式

$$\exists u,\ Y^+(u,\text{false})\ne Y^+(u,\text{true})$$

### Lean のコメント（日本語訳）

> 25-D の分布不変性にもかかわらず、候補値が変われば、同じ外生点の出力は変わり得る。

### 補題の説明

**分布は不変でも、点ごとには候補が出力を変える**ことの確認です。

### 証明の概略

1. 特定の外生点 \(u\) を取り、候補 `false`/`true` で出力が異なることを計算。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_intervention_changes_output_pointwise"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_intervention_changes_output_pointwise`

### 式

$$\exists u,s,\ Y^+(u,s)\ne Y^+(u,\text{natural 候補})$$

### Lean のコメント（日本語訳）

> 自然な候補値での出力と、do 介入後の出力が、同じ外生点で食い違う例が、各索引にある。したがって、25-D の分布不変性は、構造方程式上の点ごとの因果作用までは否定しない。

### 補題の説明

**25-D は「分布の不変性」であって「点ごとの因果作用の不在」ではない**ことを示す補題です。介入で出力が点ごとには変わります。

### 証明の概略

1. 各索引 \((d,a,h)\) で、具体的な外生点 \(u\) と候補 \(s\) を取って、出力方程式の値が異なることを計算。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_noAtman"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> マスキング SCM の 25-D から、全存在・全層の 25.2 を導く。

### 補題の説明

マスキング SCM で**無我（定理25第2結論）**が成り立つ。

### 証明の概略

1. `…_satisfies25D` と `theorem25_secondConclusion_of_probabilityFunctionalCompleteness`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedSCM_state_is_theorem16Code"></a>

## 定理 `theorem25_historyDependentMaskingSharedSCM_state_is_theorem16Code`

### 式

$$\Gamma=\mathrm{code}(x^\ast_h)\quad(\text{定理16の固定点の符号化})$$

### Lean のコメント（日本語訳）

> マスキング SCM の関係状態は、強凸勾配流から得た、定理16の履歴別の逆極限固定点を、`theorem25_intervalGradientFlowStateCode` で符号化した値に一致する。したがって、同じモデル内で、定理16の固定点 → 25-C3 の Γ 状態 → 対称性による 25-D → 25.2 の接続を検査できる。

### 補題の説明

**一本のモデルで 16→25 がつながる**ことの確認：マスキング SCM の関係状態 \(\Gamma\) は、定理16の固定点（強凸勾配流）の符号化そのものです。

### 証明の概略

1. 状態方程式の定義の展開と、`theorem25_intervalGradientFlowStateCode_matches` の関係。

----

<a id="Tomabechi.Theorem16_25.theorem25_uniformBoolProduct_measure_univ"></a>

## 定理 `theorem25_uniformBoolProduct_measure_univ`

### 式

$$(\mu\otimes\mu)(\Omega)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Bool の一様測度の積の全体の測度が 1（確率測度であること）。`private`。

### 証明の概略

1. 各因子の確率が 1 であることから、積測度の全体の測度は \(1\cdot1=1\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalSCM_candidate_has_positive_mass"></a>

## 定理 `theorem25_historyDependentGlobalSCM_candidate_has_positive_mass`

### 式

$$\forall s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

履歴依存の大域履歴 SCM で、候補の各値が正確率をもつこと。

### 証明の概略

1. 一様測度で各値の確率は \(1/2\)（外生が `Bool × Bool` の一様積）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalSCM_candidate_has_positive_mass"></a>

## 定理 `theorem25_selfSliceA2GlobalSCM_candidate_has_positive_mass`

### 式

$$\forall d,a,s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

A(2) 変種の SCM でも、候補の各値が正確率をもつこと。

### 証明の概略

1. 同様。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalSCM_hasAtman"></a>

## 定理 `theorem25_historyDependentGlobalSCM_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{false})$$

### Lean のコメント（日本語訳）

> 履歴依存の Γ を持つ SCM でも、大域独立性と、候補介入の因果効果が両立する。

### 補題の説明

履歴依存の関係状態をもっていても、候補が独立なら、候補介入の因果効果（Atman）が残り得る。25-D を課さなければ無我は出ません。

### 証明の概略

1. 候補の独立性と、介入による出力の変化から `hasAtman` の定義を満たす。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalSCM_hasAtman_elsewhere"></a>

## 定理 `theorem25_selfSliceA2GlobalSCM_hasAtman_elsewhere`

### 式

$$\mathrm{hasAtman}(\text{true},\text{false})$$

### Lean のコメント（日本語訳）

> ランダムな候補 Σ が、実際に大域履歴・関係状態から独立な SCM でも、主体の断面の 25-A(2) 型の不変性は、別の存在の Atman の効果を排除しない。

### 補題の説明

**自己スライスだけの不変性では、別の存在の Atman を排除できない**（確率版の反例）。

### 証明の概略

1. 存在 `true` で候補が出力に作用し、独立・固定的な個体化もあることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGamma_distinguishes_histories"></a>

## 定理 `theorem25_historyDependentGamma_distinguishes_histories`

### 式

$$\Gamma_{\text{履歴 false}}\ne\Gamma_{\text{履歴 true}}$$

### Lean のコメント（日本語訳）

> 25-C3 の辺の成分を調べると、2 つの履歴における Γ 状態は異なる。

### 補題の説明

履歴によって関係状態が実際に変わる（履歴依存性が非自明）こと。

### 証明の概略

1. 辺の成分を具体的に比べて異なることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalC3Model"></a>

## 定義 `theorem25_historyDependentGlobalC3Model`

### 式

$$\text{履歴依存大域 SCM を 25-B/C3 統合型へ}$$

### Lean のコメント（日本語訳）

> 履歴依存の大域 SCM を、25-B/C3 の統合型へ束ねる。Γ は関係状態そのものであり、基準の生成法則のもとで、プロファイル・辺・完全状態の各観測が、確率 1 で一致する。

### 定義の説明

25-B/C3 の観測の整合（確率 1 での一致）を備えた統合モデル。

### 証明の概略

1. `Theorem25C3IntegratedModel` のフィールドを埋める（観測は Γ の成分、確率 1 の一致は Γ が関係状態そのものであることから）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalC3Model_observationEventsMeasurable"></a>

## 定理 `theorem25_historyDependentGlobalC3Model_observationEventsMeasurable`

### 式

$$\text{観測イベントは可測}$$

### Lean のコメント（日本語訳）

> 履歴依存の有限 C3 の反例では、B/C3 の基準観測のイベントが、実際に可測である。

### 補題の説明

有限離散状態型なので、観測イベントは可測集合です。

### 証明の概略

1. 離散（`⊤`）の可測構造なので任意の集合が可測。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGamma_prodBool_eventMeasurable"></a>

## 定理 `theorem25_historyDependentGamma_prodBool_eventMeasurable`

### 式

$$\{\omega\mid P(\omega_1)\}\ \text{は可測}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Γ と Bool の積空間で、Γ 成分だけで決まる事象が可測（`private`）。

### 証明の概略

1. 離散可測構造から、Γ の部分集合は可測で、積の第 1 射影の逆像も可測。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentSharedC3Model"></a>

## 定義 `theorem25_historyDependentSharedC3Model`

### 式

$$\text{25-D を課さない履歴依存 B/C3 例を共有 C3 型に}$$

### Lean のコメント（日本語訳）

> 25-D を課さない履歴依存の B/C3 例も、同じ一様積法則の共有 C3 型に束ねる。これにより、25-B/C3 と大域法則の共有だけでは、25.2 に足りないことを、具体例で示す。

### 定義の説明

**反例のための共有 C3 モデル**：25-B/C3 と外生法則の共有があっても、25-D がなければ無我は出ない。

### 証明の概略

1. 上の `…GlobalC3Model` と同様に束ねる（外生法則を共有型に）。

----

<a id="Tomabechi.Theorem16_25.theorem25_uniformBoolTriple_measure_univ"></a>

## 定理 `theorem25_uniformBoolTriple_measure_univ`

### 式

$$(\mu\otimes(\mu\otimes\mu))(\Omega)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

3 つの Bool の一様積測度の全体の測度が 1（`private`）。

### 証明の概略

1. 各因子が確率測度であることから。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedC3Model"></a>

## 定義 `theorem25_historyDependentMaskingSharedC3Model`

### 式

$$\text{マスキング SCM を 25-B/C3 の観測統合型へ}$$

### Lean のコメント（日本語訳）

> ノイズマスキング SCM を、25-B/C3 の観測統合型にも接続する。観測事象は Γ 成分だけで決まり、状態方程式は、全外生点で関係状態そのものなので、候補依存の出力ノイズがあっても、基準観測の確率 1 の整合は維持される。

### 定義の説明

マスキング SCM に **C3 観測の整合**を加えたモデル。

### 証明の概略

1. 観測イベントを Γ 成分だけで決まるものとして与え、状態方程式が常に関係状態そのものであることから、確率 1 の一致を示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedC3Model_observationEventsMeasurable"></a>

## 定理 `theorem25_historyDependentMaskingSharedC3Model_observationEventsMeasurable`

### 式

$$\text{観測イベントは可測}$$

### Lean のコメント（日本語訳）

> ノイズマスキング C3 モデルの観測イベントは、有限離散状態型上で可測である。

### 補題の説明

観測イベントの可測性。

### 証明の概略

1. 離散可測構造から自明。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingMeasuredSharedC3Model"></a>

## 定義 `theorem25_historyDependentMaskingMeasuredSharedC3Model`

### 式

$$\text{確率 1 の C3 観測イベント可測性を備えた型へ}$$

### Lean のコメント（日本語訳）

> ノイズマスキング例を、確率 1 の C3 観測イベント可測性を備えた型へ持ち上げる。

### 定義の説明

マスキング C3 モデルを、観測イベントの可測性の証明つきの型（`Theorem25MeasuredSharedGlobalHistoryC3Model`）に格上げしたもの。

### 証明の概略

1. `…_observationEventsMeasurable` を添えて構成。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedC3Model_noAtman"></a>

## 定理 `theorem25_historyDependentMaskingSharedC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> C3 観測を統合済みのノイズマスキング例でも、25-D から定理25の第 2 結論が従う。

### 補題の説明

C3 を統合したマスキング例でも無我が成り立つ。

### 証明の概略

1. `theorem25_historyDependentMaskingSharedSCM_measurePreservingSymmetry`（外生ノイズの測度保存対称性）を、`theorem25_measurePreservingSymmetry_preservesSharedC3Observations`（対称性の合成定理）に渡す。
2. その第 1 成分が、全存在・全層で Atman が存在しないこと（8 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentMaskingSharedC3Model_c3CoherentAfterIntervention"></a>

## 定理 `theorem25_historyDependentMaskingSharedC3Model_c3CoherentAfterIntervention`

### 式

$$P_{\text{介入後}}\bigl(\text{プロファイル・辺・完全 }\Gamma\text{ 観測が基準 C3 と一致}\bigr)=1$$

### Lean のコメント（日本語訳）

> マスキング例では、候補介入の後も、プロファイル・関係の辺・完全な Γ 観測が、すべて確率 1 で、基準の C3 構造に一致する。25.2 と同じ、対称性の合成定理の、観測整合の成分である。

### 補題の説明

**介入後も C3 の観測が基準構造に確率 1 で一致する**こと。

### 証明の概略

1. 同じ対称性の合成定理 `theorem25_measurePreservingSymmetry_preservesSharedC3Observations` に、マスキング例の測度保存対称性を渡す。
2. その第 2 成分が、介入後もプロファイル・関係の辺・完全 \(\Gamma\) 観測が確率 1 で基準の C3 構造に一致するという結論（8 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentGlobalC3Model_hasAtman"></a>

## 定理 `theorem25_historyDependentGlobalC3Model_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{false})$$

### Lean のコメント（日本語訳）

> 25-B/C3 の確率 1 の整合を束ねた後でも、大域独立の候補は、Atman の効果を持てる。

### 補題の説明

25-B/C3 の整合性を課しても、25-D がなければ無我は出ない（反例）。

### 証明の概略

1. `theorem25_historyDependentGlobalSCM_hasAtman` を C3 型に持ち上げる。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentSharedSCM_hasAtman"></a>

## 定理 `theorem25_historyDependentSharedSCM_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{false})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有法則型でも、25-D を課さない履歴依存 SCM には Atman が成り立つこと。

### 証明の概略

1. `theorem25_historyDependentGlobalSCM_hasAtman` を共有法則型に移す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentSharedC3Model_hasAtman"></a>

## 定理 `theorem25_historyDependentSharedC3Model_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{false})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有 C3 型でも、25-D を課さなければ Atman が成り立つこと。

### 証明の概略

1. 同様。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSCM"></a>

## 定義 `theorem25_historyDependentFunctionallyCompleteSCM`

### 式

$$Y^+\ \text{が候補 }\Sigma\text{ に依存しない比較 SCM}$$

### Lean のコメント（日本語訳）

> 同じ履歴依存の 25-B/C3 の関係構造で、出力を候補 Σ に非依存とした比較 SCM。これは、25-A(2)/25-D を構造方程式で実現した、条件付きのモデルである。

### 定義の説明

**25-D を満たす比較モデル**：関係構造は反例のモデルと同じで、出力だけを候補に依存しないようにしたものです。25-D を（導出ではなく）構造方程式で**実現**した、条件付きのモデル。

### 証明の概略

1. 出力方程式から候補 \(\Sigma\) への依存を取り除く。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSCM_satisfies25D"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteSCM_satisfies25D`

### 式

$$\forall d,a,h,s,\ \text{intervenedJointLaw}=\text{baselineJointLaw}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

出力が候補に依存しないので、同時法則が介入で変わらない（25-D）。

### 証明の概略

1. 介入後の過程と基準の過程が、同じ外生変数の同じ関数になることから、像測度が等しい。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSCM_noAtman"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteSCM_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 履歴依存の 25-B/C3 構造のまま 25-D を課すと、定理25の第 2 結論が成立する。

### 補題の説明

同じ関係構造でも、25-D があれば無我が成り立つ（反例との対比）。

### 証明の概略

1. `…_satisfies25D` と `theorem25_secondConclusion_of_globalHistorySCM_ae_candidateIrrelevance`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSharedSCM"></a>

## 定義 `theorem25_historyDependentFunctionallyCompleteSharedSCM`

### 式

$$\text{共有法則型へ}$$

### Lean のコメント（日本語訳）

> 履歴依存の B/C3 機能完備例を、全存在・層で単一の外生法則を共有する型へ移す。

### 定義の説明

上の比較 SCM を共有法則型にしたもの。

### 証明の概略

1. 外生法則を一様積法則に固定して詰め直す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyIndexedBoolFixedPoints"></a>

## 定義 `theorem25_historyIndexedBoolFixedPoints`

### 式

$$h\mapsto x_h^\ast:=h$$

### Lean のコメント（日本語訳）

> Bool 履歴を固定点値として返す、各履歴で一意な固定点の族。これは有限の整合性の例であり、定理16の逆極限条件から、この族を構成したとは主張しない。

### 定義の説明

**有限の整合性例**：履歴 \(h\)（Bool）の固定点を \(h\) そのものとした `HistoryFixedPoints`。定理16の逆極限から作ったものではありません。

### 証明の概略

1. `HistoryFixedPoints` のフィールドを `Bool` 上で与える（固定点 \(=h\)、一意性は自明）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyIndexedBoolFixedPoints_separate"></a>

## 定理 `theorem25_historyIndexedBoolFixedPoints_separate`

### 式

$$x^\ast_{\rm false}\ne x^\ast_{\rm true}$$

### Lean のコメント（日本語訳）

> 履歴別の固定点が異なる、という 25-A(1) 型の条件を満たす、有限の固定点族。

### 補題の説明

固定点の分離（25-A(1) 型）。

### 証明の概略

1. `false ≠ true`。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM"></a>

## 定義 `theorem25_historyDependentFixedPointSharedSCM`

### 式

$$Y^+=x^\ast_h$$

### Lean のコメント（日本語訳）

> 履歴ごとの固定点の値を、将来出力として記録する、共有法則 SCM。基準出力を履歴 `h` とし、候補介入の後も同じ `h` を返すので、25-D が成立する。有限モデルで、履歴固定点の「現行過程」出力と、25-D の介入不変性が両立することを示す。

### 定義の説明

出力 \(Y^+\) として**履歴の固定点値**を返す SCM（候補介入後も同じ \(h\)）。固定点（定理25-A(1)）と 25-D の両立を示すモデルです。

### 証明の概略

1. 出力方程式を `fun d a h u s => (固定点 h).1` にする。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_output_is_fixedPoint"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_output_is_fixedPoint`

### 式

$$Y^+(d,a,h,u,s)=x^\ast_h$$

### Lean のコメント（日本語訳）

> この有限 SCM の将来出力は、同じ履歴添字の一意な固定点の値そのものである。

### 補題の説明

出力が固定点の値であること。

### 証明の概略

1. 出力方程式の定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_output_is_inverseLimitFixedPoint"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_output_is_inverseLimitFixedPoint`

### 式

$$
Y^+(d,a,h,u,s)=\bigl[\,x^\ast_h(0)=1\,\bigr]
$$

### Lean のコメント（日本語訳）

> 定理 16 の履歴別逆極限固定点を Bool 出力へ読むと、25 の SCM が同じ履歴で記録する固定点出力と一致する。出力の二値化は第 0 層が 1 であるかで行う。

### 補題の説明

定理 16 の**履歴別の逆極限の固定点**を、第 0 層の値が 1 かどうかで二値化（Bool に）すると、25 の SCM が同じ履歴で記録している固定点の出力と**一致**します。つまり、25 の SCM の出力は、定理 16 の層系から得た固定点の値の、二値化そのものです。

### 証明の概略

1. 出力方程式が履歴 \(h\) を返すことを展開する。
2. 履歴で場合分けして、固定点の第 0 座標が履歴の中心（0 または 1）であること（`theorem16_intervalGradientFlowFixedPoint_coordinate`・`theorem16_intervalGradientCenter`）から、二値化と一致することを `simp` で示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_inverseLimitOutputs_separate"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_inverseLimitOutputs_separate`

### 式

$$
\bigl[x^\ast_{\text{false}}(0)=1\bigr]\ne\bigl[x^\ast_{\text{true}}(0)=1\bigr]
$$

### Lean のコメント（日本語訳）

> 履歴ごとの逆極限固定点は実際に異なり、25-SCM の出力二値化も異なる。この等式は、別に作った Bool 固定点の族ではなく定理 16 の層系から得た値を使う。

### 補題の説明

二つの履歴の逆極限の固定点は実際に**異なり**、その第 0 層での二値化（25 の SCM の出力）も異なります。この結論は、別に作った Bool の固定点の族ではなく、**定理 16 の層系から得た値**を使っています。

### 証明の概略

1. 固定点の第 0 座標が履歴の中心であること（false で 0、true で 1）を代入し、二値化が `false ≠ true` になることを `simp` で示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_satisfies_selfProcessA2"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_satisfies_selfProcessA2`

### 式

$$
\mathrm{intervenedJointLaw}(d,a,h,s)=\mathrm{baselineJointLaw}(d,a,h)
$$

### Lean のコメント（日本語訳）

> 同じ履歴付き SCM では、任意の主体・層・履歴で候補介入が `(Γ,Y⁺)` の同時法則を変えない。したがって固定点由来の出力接続と 25-A(2) が両立する。

### 補題の説明

同じ履歴つきの SCM について、任意の主体・層・履歴で、候補を介入で置き換えても、\((\Gamma,Y^+)\) の同時法則が変わりません（25-A(2) の内容）。したがって、**固定点から得た出力の接続**と **25-A(2)** は両立します。

### 証明の概略

1. 二つの同時法則が、同じ確率空間（一様測度の積）の像として等しいことを示す（`Subtype.ext`）。
2. 状態は関係状態 `relationalState d h a`、出力は履歴 \(h\) で、どちらも候補・介入値に依らないので、像を取る写像が（定義的に）一致し、`rfl`。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_state_is_relationalState"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_state_is_relationalState`

### 式

$$\Gamma=\text{relationalState}(d,h,a)$$

### Lean のコメント（日本語訳）

> 同 SCM の Γ の状態方程式は、25-B/C の関係モデルから作る、全 C3 状態そのもの。

### 補題の説明

関係状態が 25-B/C の関係モデルの状態と一致すること。

### 証明の概略

1. 状態方程式の定義の展開。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_satisfies25D"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_satisfies25D`

### 式

$$\forall d,a,h,s,\ \text{intervenedJointLaw}=\text{baselineJointLaw}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

出力が候補に依存しないので 25-D が成り立つ。

### 証明の概略

1. `theorem25_globalHistorySCM_functionalCompleteness_of_ae_candidateIrrelevance`（出力方程式が候補に a.e. で依らないなら 25-D）を適用する。
2. 出力方程式が候補 \(s\) に全く依存しない（固定点値を返す）ので、a.e. の条件は `rfl`（13 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFixedPointSharedSCM_noAtman"></a>

## 定理 `theorem25_historyDependentFixedPointSharedSCM_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

固定点出力の SCM で、無我が成り立つ。

### 証明の概略

1. `…_satisfies25D` と `theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.theorem25_jointFiniteConsistency_witness"></a>

## 定理 `theorem25_jointFiniteConsistency_witness`

### 式

$$\text{固定点の分離}\ \wedge\ \text{関係状態の一致}\ \wedge\ \text{25-D}\ \wedge\ \text{無我}$$

### Lean のコメント（日本語訳）

> 1 つの有限な履歴添字のもとで、25-A(1) 型の履歴別固定点の差と、B/C の履歴の関係状態・25-D・25.2 を、同時に実現する整合性の証人。A1 の固定点族自体は、逆極限モデルではないため、定理16のモデル構成まで完了したものとは区別する。

### 補題の説明

**有限の整合性の証人**：(i) 履歴ごとに固定点が異なる、(ii) 関係状態が一致する、(iii) 25-D が成り立つ、(iv) 無我が成り立つ、を**同じモデルで同時に**示します。ただし固定点族は逆極限から作ったものではないため、定理16の構成の完了ではありません。

### 証明の概略

1. 各成分を、`theorem25_historyIndexedBoolFixedPoints_separate`、`…_state_is_relationalState`、`…_satisfies25D`、`…_noAtman` で与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSharedSCM_noAtman"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteSharedSCM_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有法則型の機能完備 SCM で、無我が成り立つ。

### 証明の概略

1. `theorem25_historyDependentFunctionallyCompleteSharedSCM` の 25-D と `theorem25_secondConclusion_of_sharedGlobalHistorySCM_ae_candidateIrrelevance`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.measure_map_prod_fst_event_congr"></a>

## 定理 `measure_map_prod_fst_event_congr`

### 式

$$f_1=g_1\Rightarrow(\mu\circ f^{-1})(A\times O)=(\mu\circ g^{-1})(A\times O)$$

### Lean のコメント（日本語訳）

> 同じ第 1 成分をもつ、2 つの積値の写像は、第 1 成分だけで定まる事象に、同じ測度を与える。

### 補題の説明

第 1 成分が同じなら、第 1 成分だけで決まる事象の確率も同じ（`private`）。

### 証明の概略

1. 事象の逆像が \(\{ω\mid f(ω)_1\in A\}=\{ω\mid g(ω)_1\in A\}\) で同じ。像測度の定義（`Measure.map_apply`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2_baselineObservation_eq"></a>

## 定理 `theorem25_selfSliceA2_baselineObservation_eq`

### 式

$$\mu_{\rm A2}(A\times\cdot)=\mu_{\rm C3}(A\times\cdot)$$

### Lean のコメント（日本語訳）

> A(2) 変種と、既存の C3 モデルは、Γ の観測事象上で同じ測度を持つ。

### 補題の説明

A(2) 変種の SCM と既存の C3 統合モデルの、Γ 観測の事象での基準測度が一致すること（`private`）。

### 証明の概略

1. `measure_map_prod_fst_event_congr` を適用（Γ 成分が同じなので）。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalC3Model"></a>

## 定義 `theorem25_selfSliceA2GlobalC3Model`

### 式

$$\text{自己スライス A(2) + 25-B/C3 観測整合}$$

### Lean のコメント（日本語訳）

> 自己スライス A(2) と 25-B/C3 の観測整合を、同じ共有法則 SCM に束ねた具体例。

### 定義の説明

自己スライスの 25-A(2) と C3 の観測整合が、**同じ SCM で共存**する例。

### 証明の概略

1. `theorem25_selfSliceA2SharedSCM` に C3 の観測整合（`theorem25_selfSliceA2_baselineObservation_eq` で既存 C3 モデルから移送）を添える。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalC3Model_satisfies_selfA2"></a>

## 定理 `theorem25_selfSliceA2GlobalC3Model_satisfies_selfA2`

### 式

$$\forall a,h,s,\ \text{intervenedJointLaw}(\text{false})=\text{baselineJointLaw}(\text{false})$$

### Lean のコメント（日本語訳）

> 統合 C3 モデルでも、自己スライス A(2) は成立する。

### 補題の説明

統合モデルでも自己スライスの不変性が保たれる。

### 証明の概略

1. `theorem25_selfSliceA2GlobalSCM_satisfies_selfA2` を移す。

----

<a id="Tomabechi.Theorem16_25.theorem25_selfSliceA2GlobalC3Model_hasAtman_elsewhere"></a>

## 定理 `theorem25_selfSliceA2GlobalC3Model_hasAtman_elsewhere`

### 式

$$\mathrm{hasAtman}(\text{true},\text{false})$$

### Lean のコメント（日本語訳）

> C3 の観測整合と自己スライス A(2) を保つ統合例でも、別の存在には Atman がある。

### 補題の説明

自己スライスの不変性と C3 の整合があっても、別の存在では Atman が残る。

### 証明の概略

1. `theorem25_selfSliceA2GlobalSCM_hasAtman_elsewhere` を移す。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteC3Model"></a>

## 定義 `theorem25_historyDependentFunctionallyCompleteC3Model`

### 式

$$\text{25-D 成立 SCM + 25-B/C3 の全観測整合}$$

### Lean のコメント（日本語訳）

> 25-D が成立する SCM にも、25-B/C3 の完全な基準観測整合を束ねる。候補出力を置き換えても、Γ の周辺法則は、同じ状態方程式から生成される。

### 定義の説明

25-D を満たす比較モデルに C3 の観測整合を加えた統合モデル。

### 証明の概略

1. `Theorem25C3IntegratedModel` のフィールドを埋める（Γ が状態方程式から生成され、候補出力を置換しても Γ の周辺法則が同じ）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSharedC3Model"></a>

## 定義 `theorem25_historyDependentFunctionallyCompleteSharedC3Model`

### 式

$$\text{機能完備な共有法則 SCM + C3 の全観測整合}$$

### Lean のコメント（日本語訳）

> 機能完備な共有法則 SCM と、25-B/C3 の全観測整合を、1 つの具体モデルに束ねる。既存の C3 統合モデルと共有法則モデルは、同じ一様積測度を使い、候補出力だけが異なる。Γ だけで定まる観測事象について、両方の pushforward の測度が一致することを移送する。

### 定義の説明

共有法則型の機能完備モデルに C3 観測整合を移送したもの。

### 証明の概略

1. 既存の C3 統合モデル `theorem25_historyDependentFunctionallyCompleteC3Model` の関係データ・観測・符号化を引き継ぎ、SCM を共有法則版 `theorem25_historyDependentFunctionallyCompleteSharedSCM` に置き換えて構造を組み立てる。
2. 残りの 3 つの観測整合（プロファイル・関係の辺・完全な \(\Gamma\)）は、基準法則で \(\Gamma\) だけで決まる事象の確率が、既存モデルと共有法則モデルで一致する（同じ状態方程式・同じ一様積測度）ことから移す（`measure_map_prod_fst_event_congr` 型の議論）（約 90 行）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSharedC3Model_observationEventsMeasurable"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteSharedC3Model_observationEventsMeasurable`

### 式

$$\text{観測イベントは可測}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

観測イベントの可測性。

### 証明の概略

1. 離散可測構造から自明。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteMeasuredSharedC3Model"></a>

## 定義 `theorem25_historyDependentFunctionallyCompleteMeasuredSharedC3Model`

### 式

$$\text{可測性つきの型へ}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上のモデルを、観測イベントの可測性の証明つきの型に持ち上げたもの。

### 証明の概略

1. `…_observationEventsMeasurable` を添えて構成。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteSharedC3Model_noAtman"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteSharedC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有法則 C3 型の機能完備モデルで、無我が成り立つ。

### 証明の概略

1. 25-D と `theorem25_secondConclusion_of_measurableSharedGlobalHistoryC3Model`（Core の変種）。

----

<a id="Tomabechi.Theorem16_25.theorem25_historyDependentFunctionallyCompleteC3Model_noAtman"></a>

## 定理 `theorem25_historyDependentFunctionallyCompleteC3Model_noAtman`

### 式

$$\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)$$

### Lean のコメント（日本語訳）

> 履歴依存の 25-B/C3 モデルで、25-D の法則不変性を満たす比較構成では、統合後も、25-D から定理25の第 2 結論が従う。

### 補題の説明

C3 統合後も、25-D があれば無我が成り立つ。

### 証明の概略

1. `theorem25_secondConclusion_of_c3IntegratedModel`（Core の変種）を、統合モデルの確率因果モデルに適用。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceRandomizedIntegratedModel"></a>

## 定義 `theorem25_twoExistenceRandomizedIntegratedModel`

### 式

$$\text{非退化 SCM と 25-B/C のデータを同じ索引・Γ 型に統合}$$

### Lean のコメント（日本語訳）

> 非退化な SCM を、25-B/C の存在・関係データと、同じ索引・Γ の状態型に束ねた、統合例。基準分布でのプロフィール・辺の観測整合も確認する。

### 定義の説明

確率的な候補をもつ SCM と、25-B/C の存在・関係データを統合した例（基準分布で観測整合）。

### 証明の概略

1. `Theorem25IntegratedModel` のフィールドを埋める（SCM は `theorem25_twoExistenceRandomizedSCM`、関係データは `theorem25_twoExistencePresenceRelations`）。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceRandomizedC3IntegratedModel"></a>

## 定義 `theorem25_twoExistenceRandomizedC3IntegratedModel`

### 式

$$\text{C3 統合型へ}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の統合例を、25-C3 の完全な観測整合を備えた型 `Theorem25C3IntegratedModel` に持ち上げたもの。

### 証明の概略

1. `theorem25_twoExistenceRandomizedIntegratedModel` に、完全な Γ 観測の整合を添える。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceRandomized_candidate_has_positive_mass"></a>

## 定理 `theorem25_twoExistenceRandomized_candidate_has_positive_mass`

### 式

$$\forall s,\ \Sigma=s\ \text{の確率}>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

候補の各値が正の確率をもつこと。

### 証明の概略

1. 一様測度で各値の確率は \(1/2\)。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceRandomized_hasAtman"></a>

## 定理 `theorem25_twoExistenceRandomized_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\ast)$$

### Lean のコメント（日本語訳）

> 非退化な Σ 独立モデルでも、候補値の介入は将来出力を変える。したがって、25-B/C だけでは、ランダムな候補の範囲でも、Atman の不在は導けない。

### 補題の説明

**確率的な候補でも、25-B/C だけでは無我は導けない**。

### 証明の概略

1. 候補 \(\Sigma\) の独立性と、`do(Σ=s)` による出力の変化を示し、`hasAtman` の定義を満たす。

----

<a id="Tomabechi.Theorem16_25.theorem25_C3Randomized_do_not_imply_noAtman"></a>

## 定理 `theorem25_C3Randomized_do_not_imply_noAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\ast)\quad(\text{25-B/C3 統合型でも})$$

### Lean のコメント（日本語訳）

> 非退化な SCM を、25-B/C3 の統合型まで持ち上げても、25-D なしには Atman が除けない。

### 補題の説明

C3 統合型でも、25-D なしでは無我が出ないこと。

### 証明の概略

1. `theorem25_twoExistenceRandomized_hasAtman` を統合型に移す。

----

<a id="Tomabechi.Theorem16_25.Theorem25TwoLayerGamma"></a>

## 定義 `Theorem25TwoLayerGamma`

### 式

$$\Gamma=\text{（物理層・上位層をもつ 2 層格子上の状態）}$$

### Lean のコメント（日本語訳）

> 物理層と上位層を、異なる点として持つ、2 層格子上の Γ の状態。

### 定義の説明

2 層（物理層と上位層）の関係状態の型。

### 証明の概略

1. 型の定義のみ。

----

<a id="Tomabechi.Theorem16_25.instance@L4777"></a>

## インスタンス `instance@L4777`

### 式

$$\text{可測空間}=\text{離散（}\top\text{）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

`Theorem25TwoLayerGamma` の離散可測構造。

### 証明の概略

1. `⊤`。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoLayerPresenceRelations"></a>

## 定義 `theorem25_twoLayerPresenceRelations`

### 式

$$\text{層}=\text{Bool 格子},\ \text{存在}=\text{Bool 二点}$$

### Lean のコメント（日本語訳）

> 層を Bool の格子、存在を Bool の 2 点とする、25-B/C のデータ。両層に現前し、相互の辺は連結。

### 定義の説明

2 層・2 存在の 25-B/C データ（全存在が両層に現前し、辺が連結）。

### 証明の概略

1. `Theorem25PresenceRelationModel` のフィールドを具体的に与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoLayerRandomizedSCM"></a>

## 定義 `theorem25_twoLayerRandomizedSCM`

### 式

$$\text{一様な Bool 候補 }\Sigma\perp\Gamma\ (\text{各固定履歴で})$$

### Lean のコメント（日本語訳）

> Bool 一様の候補を、2 層の完全な Γ の状態へ接続した、25-B/C3 のモデル。Γ は、2 層のプロファイルと、その垂直近傍、水平の入出辺を保持し、候補 Σ は、各固定履歴で Γ から独立。

### 定義の説明

2 層の完全な Γ をもつ確率 SCM。

### 証明の概略

1. `Theorem25RandomizedStructuralCausalModel` のフィールドを、2 層 Γ と一様な候補で与える。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoLayerRandomized_hasAtman"></a>

## 定理 `theorem25_twoLayerRandomized_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{true})$$

### Lean のコメント（日本語訳）

> 2 層 Bool 格子の 25-B/C3 モデルでも、25-D を外すと、上位層に Atman の候補が残る。したがって、第 2 結論の欠落は、1 層格子だけの退化現象ではない。

### 補題の説明

**2 層でも 25-D なしには無我は出ない**（1 層だけの退化現象ではない）。

### 証明の概略

1. 上位層（`true`）で、候補介入が出力を変えることを示す。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoLayerRandomizedC3Model"></a>

## 定義 `theorem25_twoLayerRandomizedC3Model`

### 式

$$\text{2 層の完全 }\Gamma\text{ の C3 統合型}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

2 層の SCM を、C3 の完全な観測整合を備えた型に持ち上げたもの。

### 証明の概略

1. `theorem25_twoLayerRandomizedSCM` と `theorem25_twoLayerPresenceRelations` を束ねる。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoLayerRandomizedC3_hasAtman"></a>

## 定理 `theorem25_twoLayerRandomizedC3_hasAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\text{true})$$

### Lean のコメント（日本語訳）

> 2 層の完全な Γ の観測を統合した C3 モデルでも、同じ Atman の候補が残る。

### 補題の説明

C3 統合型でも同じ結論。

### 証明の概略

1. `theorem25_twoLayerRandomized_hasAtman` を移す。

----

<a id="Tomabechi.Theorem16_25.theorem25_twoExistenceCountermodelC3"></a>

## 定義 `theorem25_twoExistenceCountermodelC3`

### 式

$$\text{有限 B/C 反例を C3 の完全な }\Gamma\text{ 型に}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最初の有限反例（`theorem25_twoExistenceCountermodelSCM`）を、C3 の完全な Γ 型の統合モデルに載せたもの。

### 証明の概略

1. `Theorem25C3IntegratedModel` のフィールドを埋める。

----

<a id="Tomabechi.Theorem16_25.theorem25_BC_do_not_imply_noAtman"></a>

## 定理 `theorem25_BC_do_not_imply_noAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\ast)$$

### Lean のコメント（日本語訳）

> この有限モデルは、条件 25-B/C と、基準のプロファイル・関係の観測との確率 1 の整合を満たすが、候補介入の前後で出力法則が変わり、Atman(d,α) が成立する。よって、25-D は、独立な実質条件である。

### 補題の説明

**25-B/C では無我は導けない**：25-B/C と観測整合を満たしても、候補介入で出力が変われば Atman が成り立ちます。したがって **25-D は独立の実質条件**です。

### 証明の概略

1. `theorem25_twoExistenceCountermodelSCM` で、候補介入により出力が `false` から `true` に変わることを示し、`hasAtman` の定義を満たす。

----

<a id="Tomabechi.Theorem16_25.theorem25_C3_do_not_imply_noAtman"></a>

## 定理 `theorem25_C3_do_not_imply_noAtman`

### 式

$$\mathrm{hasAtman}(\text{false},\ast)\quad(\text{C3 の }\Gamma\text{ を保持しても})$$

### Lean のコメント（日本語訳）

> 25-C3 の Γ を実際の状態型として保持しても、25-B/C のみから 25-D は導けない。本例は、各固定履歴で候補値を定数の確率変数として、関係状態から独立にする、退化モデルである。ランダムな Σ と履歴 H の同時分布をもつ、一般の確率的個体化モデルまでは表さない。

### 補題の説明

C3 の Γ を実際の状態型にしても、25-B/C だけからは 25-D は導けない。ただし本例は**退化モデル**（候補が定数）で、一般の確率的モデルまでは表しません。

### 証明の概略

1. `theorem25_twoExistenceCountermodelC3` で、候補介入により出力が変わること。

----


## コメント修正記録

（なし）
