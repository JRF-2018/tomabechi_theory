# Theorem1_Model.lean 解説

> 対象: [`Theorem1_Model.lean`](../Theorem1_Model.lean)（定理1の1次元例への一般定理の適用）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`theorem1_example.lean` の 1 次元の線形の例の結論（TCZ への指数収束、**\(\theta\ge0\) について一般**）を、**一般の定理1**（`Theorem1.lean`）を使って**もう一度導く**ファイルです。一般の定理を、まず**閾値 0 の目標 \(\{0\}\)** に適用し、\(\{0\}\subseteq\mathrm{TCZ}_\theta\) なので距離の比較で \(\mathrm{TCZ}_\theta\) への収束に移します。

### 0.2 このファイルが証明していないこと（重要）

- 一般の定理1が、この例の仮定（Lyapunov 関数の下降・指数減衰など）を満たすことの確認であり、**1 次元の線形の例**であることに変わりはありません。
- 有限ホライズンの最適性が定理1の下降の仮定を導くことの証明ではありません（ファイル冒頭のコメントのとおり）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> **1 次元の例に適用した定理1**
>
> このファイルは、例の完全な \(\theta\ge0\) の結論を保つ。一般の定理1の結果を、まず閾値 0 の集合 \(\{0\}\) に適用し、次に \(\{0\}\subseteq\mathrm{TCZ}\ \theta\) を使う。この比較は、例の TCZ が常に 0 を含むので有効である。これは、なお 1 次元の線形の例であり、有限ホライズンの最適性が、定理1の下降の仮定を導くことの証明ではない。

`open Real` のみ（名前空間なし）。

---

<a id="convergence_to_TCZ_via_Theorem1"></a>

## 定理 `convergence_to_TCZ_via_Theorem1`

### 式

$$\theta\ge0\ \Longrightarrow\ \text{ExponentiallyConvergesToTCZ}\ (x_0e^{-\lambda t})\ (\mathrm{TCZ}_\theta)\ \lambda$$

### Lean のコメント（日本語訳）

> （コメントなし：ファイル冒頭のコメントのとおり、一般の定理1を閾値 0 の集合 \(\{0\}\) に適用し、\(\{0\}\subseteq\mathrm{TCZ}_\theta\) で比較する。）

### 補題の説明

`theorem1_example.lean` の `convergence_to_TCZ` と同じ結論を、**一般の定理1から**導きます。

### 証明の概略

1. 一般の定理 `theorem1_closed_loop_tcz_decay_from_v_derivative_and_quadratic_growth`（`Theorem1.lean`：\(V\) の導関数の評価と 2 次の増大条件から、閉ループの TCZ への距離の指数減衰）を、閾値 0 の目標 \(\{0\}\) に適用。`residual1`（閾値 0 の残差）が \(x_0^2/2\) なので、定数は \(|x_0|\) になる。
2. \(\{0\}\subseteq\mathrm{TCZ}_\theta\)（\(\theta\ge0\)）なので、距離は単調：\(\operatorname{dist}(x,\mathrm{TCZ}_\theta)\le\operatorname{dist}(x,\{0\})\)（`hdist_subset`）。
3. 定数を \(\max\) などでまとめて、`ExponentiallyConvergesToTCZ` の形にする。

----


## コメント修正記録

（なし）
