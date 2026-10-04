# Tomabechi/Examples/Theorem26_ValueZeroSet.lean 解説

> 対象: [`Tomabechi/Examples/Theorem26_ValueZeroSet.lean`](../Tomabechi/Examples/Theorem26_ValueZeroSet.lean)（定理26の Python 例（値の零集合）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 空（くう）⊤ | 抽象度の束の最大元。最高抽象度。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理26（涅槃寂静）の Python 例（`examples/theorem26_value_zero_set.py`）の Lean 根拠です。Python 例は \(\dot x=-\lambda x\)（\(\lambda=1\)）、最高抽象度の走行コスト \(3x^2\)、割引率 \(\rho=1\)、空未満の走行コスト 1 のスカラーモデルを使います。これは `Theorem24_26_Model` のモデルと**同一パラメータ**なので、ここでは新しい証明をせず、Python の各数値・主張が既存モデルの宣言から出ることを対応づけます。

- **L0 定義対応**：`Theorem24_26_Model.flow/runningCost/value/lowerValue` が、Python の \(x(t)=x_0e^{-\lambda t}\)、\(V_\top=3x^2\)、\(J^\ast\)、\(J^\ast_a\) に対応する。
- **L1/L2**：\(J^\ast_\top(x_0)=x_0^2\)（\(x_0\in\{0,\tfrac12,1,2\}\)）、空未満 \(J^\ast_a=1/\rho=1\)、零苦集合 \(\{0\}\)、(26.2) の指数評価。
- **L3**：\(\theta=\tfrac34\) の劣位集合 \(\{3x^2\le\theta\}\) の境界 \(x=\tfrac12\) でも \(J^\ast>0\)（**有界化であって滅尽ではない**）。

### 0.2 このファイルが証明していないこと

- 証明対象は Python の数値出力ではなく、**モデルが定理26の条件を満たし、結論が従うこと**です。
- 制御空間は 1 点の特殊モデル（最適性は自明）です（今後の課題。トップの `README.md` を参照）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理26の Python 例（`examples/theorem26_value_zero_set.py`）の Lean 根拠
>
> Python 例は \(\dot x=-\lambda x\)（\(\lambda=1\)）、最高抽象度の走行コスト \(3x^2\)、割引率 \(\rho=1\)、空未満の走行コスト 1 のスカラーモデルを使う。これは `Theorem24_26_Model` のモデルと同一パラメータなので、ここでは新しい証明をせず、Python の各数値・主張が既存モデルの宣言から出ることを対応づける。
>
> * L0 定義対応：`Theorem24_26_Model.flow/runningCost/value/lowerValue` が Python の \(x(t)=x_0e^{-\lambda t}\)、\(V_\top=3x^2\)、\(J^\ast\)、\(J^\ast_a\) に対応する。
> * L1/L2：\(J^\ast_\top(x_0)=x_0^2\)（\(x_0\in\{0,\frac12,1,2\}\)）、空未満 \(J^\ast_a=1/\rho=1\)、零苦集合 \(\{0\}\)、(26.2) の指数評価。
> * L3：\(\theta=\frac34\) の劣位集合 \(\{3x^2\le\theta\}\) の境界 \(x=\frac12\) でも \(J^\ast>0\)（有界化であって滅尽ではない）。
>
> 証明対象は Python の数値出力ではなく、モデルが定理26の条件を満たし結論が従うことである。

名前空間は `Tomabechi.Examples.Theorem26`（`open Tomabechi.Theorem24_26_Model`）。

---

<a id="Tomabechi.Examples.Theorem26.J_top_values"></a>

## 定理 `J_top_values`

### 式

$$J(0)=0,\ J(\tfrac12)=\tfrac14,\ J(1)=1,\ J(2)=4\quad(T=0)$$

### Lean のコメント（日本語訳）

> Python の `J_top = [J(x0) for x0 in [0, 0.5, 1, 2]]` の厳密値 \(x_0^2\)（\(T=0\)）。

### 補題の説明

最高抽象度の最適値 \(J=x_0^2\) の 4 点での値（`Theorem24_26_Model.value_eq_sq`）。

### 証明の概略

1. `value_eq_sq` で各点 \(x_0^2\) を計算（`norm_num`）。

----

<a id="Tomabechi.Examples.Theorem26.J_sub_value"></a>

## 定理 `J_sub_value`

### 式

$$J_{\rm low}(T)=1=\tfrac1\rho>0$$

### Lean のコメント（日本語訳）

> Python の `J_sub`（空未満の層、走行コスト 1、\(\rho=1\)）は常に \(1=1/\rho>0\)。

### 補題の説明

空未満の層（走行コスト一定）では、最適値は常に正（\(1/\rho=1\)）。**定理24の「一切皆苦」**に対応します。

### 証明の概略

1. `lowerValue_eq_one`（Model）と \(0<1\)。

----

<a id="Tomabechi.Examples.Theorem26.top_zero_target"></a>

## 定理 `top_zero_target`

### 式

$$N_\top(T)=\{0\}$$

### Lean のコメント（日本語訳）

> Python の零苦集合 \(N_\top=\{0\}\)（最高抽象度）。

### 補題の説明

最高抽象度の**零苦の目標集合**は原点だけ。

### 証明の概略

1. `zeroTarget_eq_singleton`（Model）。

----

<a id="Tomabechi.Examples.Theorem26.exponential_bounds"></a>

## 定理 `exponential_bounds`

### 式

$$s\ge0\Rightarrow W_{\rm along}(s)\le x^2e^{-2s}\ \wedge\ \mathrm{dist}(\mathrm{flow}(s),N)\le|x|e^{-s}$$

### Lean のコメント（日本語訳）

> (26.2) の指数評価。Python の `bound=W0 e^{-λ_W t}`、`dist_bound=√W0 e^{-λ_W t/2}`（\(T=0\)）。

### 補題の説明

**(26.2) の指数評価**：Lyapunov 関数と目標集合までの距離が指数的に減衰します。

### 証明の概略

1. `model_theorem26_exponential_convergence`（Model）に \(T=0\) を代入し、\(W_{\rm along}(0)=x^2\)、\(\sqrt{x^2}=|x|\) で整理。

----

<a id="Tomabechi.Examples.Theorem26.bounded_but_not_extinguished"></a>

## 定理 `bounded_but_not_extinguished`

### 式

$$3(\tfrac12)^2=\tfrac34\ \wedge\ J(\tfrac12)=\tfrac14>0\ \wedge\ \tfrac12\notin N(0)$$

### Lean のコメント（日本語訳）

> 有界化と滅尽の違い：\(\theta=\frac34\) の劣位集合 \(\{3x^2\le\theta\}\) の境界 \(x=\frac12\) は、走行コストが \(\theta\) 以下だが \(J^\ast=\frac14>0\)。零苦集合 \(\{0\}\) には入っていない。

### 補題の説明

**有界化（苦を閾値以下に抑える）と滅尽（苦を 0 にする）は違う**：走行コスト \(3x^2\) が閾値 \(\theta=\frac34\) に収まっても、最適値は正で、零苦集合には入っていません。

### 証明の概略

1. \(3\cdot(\frac12)^2=\frac34\) を計算（`norm_num`）。
2. `J_top_values` で \(J(\frac12)=\frac14>0\)。
3. `zeroTarget_eq_singleton`（Model）で零苦集合が \(\{0\}\)、\(\frac12\notin\{0\}\)（`norm_num`）。

----


## コメント修正記録

（なし）
