# Tomabechi/Examples/Theorem22_HStage.lean 解説

> 対象: [`Tomabechi/Examples/Theorem22_HStage.lean`](../Tomabechi/Examples/Theorem22_HStage.lean)（定理22・H-stage 不変領域の Python 例の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22・H-stage の不変領域の Python 例（`examples/theorem22_h_stage_invariant_region.py`）の Lean 根拠です。Python 例は 1 次元モデル
$$\tilde V(x)=\tfrac x2+\tfrac{x^2}2,\quad U=[-1,1],\quad\dot x=-(x+\tfrac12),\quad x_0=\tfrac12$$
で、`Theorem22_InvariantRegion_Model.lean` の `toy*` と**同一**です。ここでは Python が確認する各項目を既存の宣言へ対応づけ、Python の厳密解 \(x(t)=x^\ast+(x_0-x^\ast)e^{-t}\)（\(x^\ast=-\tfrac12\)）が閉ループ方程式を解くこと、およびその上での
$$\tilde V(x(t))-\tilde V(x^\ast)=e^{-2t}\bigl(\tilde V(x_0)-\tilde V(x^\ast)\bigr)$$
を追加で示します。

### 0.2 このファイルが証明していないこと

- **範囲拡張の例**（旧入力は不成立・緩和入力は成立）であり、**原文の定理22の反例ではありません**。
- 一般の H-stage 入力の構成ではなく、1 次元の toy モデルです。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理22/H-stage 不変領域の Python 例（`examples/theorem22_h_stage_invariant_region.py`）の Lean 根拠
>
> Python 例は \(\tilde V(x)=x/2+x^2/2\)、局所球 \(U=[-1,1]\)、閉ループ \(\dot x=-(x+\frac12)\)、初期点 \(x_0=\frac12\) の 1 次元モデルで、`Theorem22_InvariantRegion_Model.lean` の `toy*` と**同一**である。ここでは Python が確認する各項目を既存の宣言へ対応づけ、Python の厳密解 \(x(t)=x^\ast+(x_0-x^\ast)e^{-t}\) が閉ループ方程式を解くこと、およびその上での \(\tilde V(x(t))-\tilde V(x^\ast)=e^{-2t}(\tilde V(x_0)-\tilde V(x^\ast))\) を追加する。
>
> これは範囲拡張の例（旧入力は不成立・緩和入力は成立）であり、原文の定理22の反例ではない。

名前空間は `Tomabechi.Examples.Theorem22HStage`（`open Tomabechi.Theorem22InvariantRegionModel`）。

---

<a id="Tomabechi.Examples.Theorem22HStage.old_sublevel_endpoints"></a>

## 定理 `old_sublevel_endpoints`

### 式

$$\tilde V(-\tfrac32)=\tilde V(\tfrac12)\ \wedge\ -\tfrac32\notin[-1,1]$$

### Lean のコメント（日本語訳）

> Python の `sub=(x*-s, x*+s)=(-3/2, 1/2)`：端点で \(\tilde V\) が等しく、左端は球 \([-1,1]\) の外。

### 補題の説明

**旧入力が不成立**であることの確認：部分準位集合 \((-\frac32,\frac12)\) の左端が局所球 \([-1,1]\) の外に出るので、旧入力（部分準位集合が球に入る）は成り立ちません。

### 証明の概略

1. `toyPotential` の定義を展開して、両端の値 \(\tilde V(-\frac32)=\tilde V(\frac12)\) を計算（`norm_num`）。
2. \(|-\frac32|=\frac32>1\) から球の外。

----

<a id="Tomabechi.Examples.Theorem22HStage.invariant_interval_inward"></a>

## 定理 `invariant_interval_inward`

### 式

$$0\le f(-\tfrac12)\ \wedge\ f(\tfrac12)\le0$$

### Lean のコメント（日本語訳）

> Python の `invariant`：端点で閉ループ場が内向き（`field(-½)=0≥0`、`field(½)=-1≤0`）。

### 補題の説明

**緩和入力の不変性**：区間の左端で場が 0 以上、右端で 0 以下なので、区間が前向き不変です。

### 証明の概略

1. `toyClosedLoopField` の定義 \(f(x)=-(x+\frac12)\) に端点を代入して計算。

----

<a id="Tomabechi.Examples.Theorem22HStage.exact_solution"></a>

## 定理 `exact_solution`

### 式

$$\frac{d}{ds}\bigl(-\tfrac12+e^{-s}\bigr)=f\bigl(-\tfrac12+e^{-t}\bigr)\ \wedge\ -\tfrac12+e^{-0}=\tfrac12$$

### Lean のコメント（日本語訳）

> Python の厳密解 \(x(t)=x^\ast+(x_0-x^\ast)e^{-t}\)（\(x^\ast=-\frac12\)、\(x_0=\frac12\)）は \(\dot x=-(x+\frac12)\) を解き、初期値は \(\frac12\)。

### 補題の説明

厳密解が閉ループ方程式を解くこと。

### 証明の概略

1. `Real.hasDerivAt_exp` の合成で \(\frac{d}{ds}e^{-s}=-e^{-s}\)、場の値 \(-(x+\frac12)=-e^{-t}\) と一致。初期値は \(-\frac12+1=\frac12\)。

----

<a id="Tomabechi.Examples.Theorem22HStage.potential_gap_decay"></a>

## 定理 `potential_gap_decay`

### 式

$$\tilde V(x(t))-\tilde V(x^\ast)=e^{-2t}\bigl(\tilde V(x_0)-\tilde V(x^\ast)\bigr)$$

### Lean のコメント（日本語訳）

> Python の `gap = V(x(t))-V(x*) = e^{-2t}(V(x0)-V(x*))` の厳密式。

### 補題の説明

**ポテンシャル差の厳密な指数減衰**：\(\tilde V(x)-\tilde V(x^\ast)=\frac12(x-x^\ast)^2\) で、\(x-x^\ast=e^{-t}\) なので \(e^{-2t}\) になります。

### 証明の概略

1. `toy_potential_square_completion`（既存：\(\tilde V(x)-\tilde V(-\frac12)=\frac12(x+\frac12)^2\)）を 3 か所に使う。
2. \(x(t)+\frac12=e^{-t}\) で \(\frac12e^{-2t}\)、初期値では \(\frac12\)。比をとって等式。

----


## コメント修正記録

（なし）
