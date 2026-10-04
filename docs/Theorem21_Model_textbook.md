# Theorem21_Model.lean 解説

> 対象: [`Theorem21_Model.lean`](../Theorem21_Model.lean)（定理21の具体モデルへの適用（有限再構成カーネル・1次元2次例））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の**具体モデルへの適用**です。(1) **有限個の再構成カーネル**（`MeanFieldReconstruction.lean`）から作った実効ポテンシャルに、定理21の大域力学の定理（`Theorem21GlobalResults.lean`）を適用する 2 つの**条件付きの結果**と、(2) 具体的な **1 次元の 2 次モデル** \(V_0=0\)、\(S=-x^2/2\)（臨場感カーネル）、移動度が恒等、\(\dot x=-x\) の例です。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `theorem21_finite_reconstruction_global_dynamics_from_threshold` | 有限の重み付き再構成カーネルのパッケージ → 大域力学（正確な劣水準集合版） |
| `theorem21_finite_reconstruction_partial_invariant_region` | 同、任意の前向き不変な部分領域版 |
| `theorem21_quadratic_identity_special_case` | 1 次元 2 次モデル（**特殊ケース**） |

### 0.3 このファイルが証明していないこと（重要）

- 1 次元 2 次モデル（`theorem21_quadratic_identity_special_case`）は、**特殊ケースであり一般定理の証明ではありません**。基礎ポテンシャルは 0、臨場感ポテンシャルは \(-x^2/2\)、移動度は恒等、閉ループは \(x'=-x\) です。
- 有限の再構成カーネルの条件（\(C^2\)・勾配・Hessian の下界・中心での勾配ゼロ）、移動度の \(C^1\) 性・強制性、不変領域の仮定などは**明示的な仮定**です（モデルから導く作業は個別）。
- 有限測度の平均・微分の交換などの共有補題は、依存関係上 `MeanFieldReconstruction.lean` に残っています。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21：具体モデルへの適用**
>
> このモジュールは、一般の定理21の結果の、有限の再構成カーネルへの適用と、明示的な 1 次元の 2 次の例を集める。有限台の微分・平均の補題は、一般の展開も使うので、`Theorem21.lean` に残してある。

（注：現在は共有補題は `MeanFieldReconstruction.lean` にあります。）名前空間は `Tomabechi.Theorem21`。`open RealInnerProductSpace`、`open Filter`、`open scoped Topology NNReal ContDiff`。

---

<a id="Tomabechi.Theorem21.theorem21_finite_reconstruction_global_dynamics_from_threshold"></a>

## 定理 `theorem21_finite_reconstruction_global_dynamics_from_threshold`

### 式

$$\text{有限の重み付き再構成カーネルのパッケージ}\ +\ p>p_{\text{crit}}\ \Longrightarrow\ \text{最小点・大域軌道・指数減衰}$$

### Lean のコメント（日本語訳）

> 有限の重み付きの再構成カーネルのパッケージから、大域の状態依存の移動度の定理への、アダプタ。そのパッケージは、`finite_reconstruction_kernel_conditions` から得られる。

### 補題の説明

有限個の原子（重み \(w_a\)）の平均で作った臨場感カーネル \(S=\sum_aw_ak_a\) に、`theorem21_state_dependent_mobility_from_threshold`（Theorem21GlobalResults）を適用します。

### 証明の概略

1. `finite_reconstruction_kernel_conditions`（MeanFieldReconstruction）で、\(S\) の \(C^1\)・勾配・Hessian・中心・曲率の条件を得る。
2. `theorem21_state_dependent_mobility_from_threshold` に渡す。

----

<a id="Tomabechi.Theorem21.theorem21_finite_reconstruction_partial_invariant_region"></a>

## 定理 `theorem21_finite_reconstruction_partial_invariant_region`

### 式

$$\text{有限の再構成カーネル}\ +\ \text{任意の前向き不変な部分領域}\ \Longrightarrow\ \text{定理21の結論}$$

### Lean のコメント（日本語訳）

> 有限の重み付きの再構成カーネルは、論文のより一般的な、不変な部分的な劣水準の定式化も支える。カーネルの仮定が、平均化したポテンシャルの導関数と曲率を与え、コンパクト性が、有限次元の閉ループ場の、一様な局所解と Lipschitz 定数を与える。

### 補題の説明

上の定理の、不変領域を任意の部分集合にした版です（`theorem21_state_dependent_mobility_from_threshold_on_invariant_region`）。

### 証明の概略

1. 有限カーネルの条件を導き、コンパクト性から一様な局所解とリプシッツ定数を得て、不変領域版の定理を適用する。

----

<a id="Tomabechi.Theorem21.theorem21_quadratic_identity_special_case"></a>

## 定理 `theorem21_quadratic_identity_special_case`

### 式

$$V_0\equiv0,\ S=-\tfrac{x^2}{2},\ A=\mathrm{id},\ \dot x=-x:\quad\text{内部の最小点}\ x^\*=0,\ \ \varphi(t)\le\varphi(a)e^{-2(t-a)},\ \ |x(t)-x^\*|\le\sqrt{2\varphi(a)}\,e^{-(t-a)}$$

### Lean のコメント（日本語訳）

> 定理21の、具体的な 1 次元の 2 次のインスタンス。これは、特殊な場合であり、一般の定理ではない：基礎のポテンシャルは零、偏りのポテンシャルは \(-x^2/2\)、移動度は恒等、閉ループの ODE は \(x'=-x\) である。

### 補題の説明

最も簡単な具体例：実効ポテンシャル \(V_{\text{eff}}(x)=0-1\cdot(-x^2/2)=x^2/2\)（谷の底は 0）で、解は \(x(t)=x(a)e^{-(t-a)}\)。定理21の結論（最小点・指数減衰）が成り立つことを確認します。**特殊ケース**です。

### 証明の概略

1. 具体データ：\(V\equiv0\)、\(S(x)=-x^2/2\)、\(\nabla V=0\)、\(\nabla S=-x\)、Hessian \(H_V=0\)、\(H_S=\langle-1,\cdot\rangle\)。閉球 \(\bar B(0,2)\)、\(m=1\)、\(\beta=0\)、\(B=0\)。
2. 一般定理 `theorem21_identity_mobility_global_exponential_case`（恒等移動度）の前提（\(C^1\) 性、Fréchet 微分の表示、Hessian の評価、中心の勾配 0、閾値 \(p>0\) など）を、1 つずつ確認する。
3. 結論（最小点の存在と指数減衰）を、この具体データで書き下す（86 行）。

----


## コメント修正記録

（なし）
