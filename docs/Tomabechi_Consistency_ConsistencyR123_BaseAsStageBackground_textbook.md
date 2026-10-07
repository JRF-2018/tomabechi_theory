# Tomabechi/Consistency/ConsistencyR123_BaseAsStageBackground.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_BaseAsStageBackground.lean`](../Tomabechi/Consistency/ConsistencyR123_BaseAsStageBackground.lean)（定理21の V₀ としての共有基礎評価）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理 21 の (21.3) が課す \(V_0\) についての条件が、**\(V_0=\)共有の基礎評価 `N.base.V0`**（認知座標の Euclid 表示）と読んだ場合にも、実際に成り立つことを示すファイルです。(21.3) は、局所球 \(U_b=\bar B_r(x_b)\) 上で \(V_0,S_\mu\in C^2(U_b)\)、\(\|\nabla V_0\|\le B\)、\(\nabla^2V_0\succeq-\beta I\) を課します。原文は §2.1 の基礎評価と同じ記号 \(V_0\) を使います。モデルの段 \(n\) では、背景の地形 \(R_n\) を別の関数として置いていました（原文の §11 が許す読み）が、ここでは基礎評価と読みます。

箱の内部では、`N.base.V0` は \(1+8\cdot\mathrm{symbolDistance}\)（箱内で \(1+2(x_0-x_1)^2\)）で、二次式です。原点中心の Euclid 球 \(\bar B_r(0)\)（\(0<r<1/4\)）は箱の内部に入るので、

* \(V_0\) は球上の各点で \(C^2\)、
* 勾配は \(G(z)=4\langle d,z\rangle d\)（\(d=e_0-e_1\)）で、\(\|G(z)\|\le 8r\)（\(B=8r\)）、
* ヘシアンは \(4\langle d,\cdot\rangle d\)（半正定値）で、\(\nabla^2V_0\succeq-\beta I\)（\(\beta=0\)）。

### 0.2 このファイルが証明していないこと

* これは (21.3) の \(V_0\) についての**条件の充足**です。完全な `MeanFieldStageInput`（臨場感 \(S\)、中心、勾配条件 \(p>p_{\mathrm{crit}}\)、部分準位、障壁など）を、\(V_0=\) `N.base.V0` で組み直したものではありません。
* 箱の内部の球に限ります（箱の境界・外部では \(V_0\) は二次式でない）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 定理21 の (21.3) は、局所球 U_b = B̄_r(x_b) 上で V₀, S_μ ∈ C²(U_b)、‖∇V₀‖ ≤ B、∇²V₀ ≽ −βI を課す。原文は §2.1 の基礎評価と同じ記号 V₀ を使う。モデルの段 n では背景地形 R_n を別の関数として置いていた（R_n の読み、§11 が許す）が、ここでは V₀ = 共有基礎評価 N.base.V0（認知座標の Euclid 表示）と読んだ場合に、(21.3) が実際に成り立つことを示す。…（以下、上の三点と範囲の注意）。

---

<a id="Tomabechi.Consistency.R123.closedBall_subset_interior_box"></a>

## 補題 `closedBall_subset_interior_box`

### 式

$$
r<\tfrac14\ \Rightarrow\ \bar B_r(0)\subset\mathrm{int}(\mathrm{box})
$$

### Lean のコメント（日本語訳）

> 原点中心の球r<1/4は箱の内部に入る。

### 補題の説明

原点中心の閉球 \(\bar B_r(0)\)（\(r<1/4\)）は、箱の**内部**に入ります。

### 証明の概略

1. 開球 \(B_{1/4}(0)\) に入ること、開球が箱に含まれることから、内部の極大性（`interior_maximal`）。

----

<a id="Tomabechi.Consistency.R123.baseHessian21"></a>

## 定義 `baseHessian21`

### 式

$$
H(w)=4\langle d,w\rangle\,d
$$

### Lean のコメント（日本語訳）

> 勾配場G(z)=8•∇symbolDistance(z)は線形写像4⟨d,·⟩dで、ヘシアンは半正定値。

### 定義の説明

勾配の場 \(G(z)=8\,\nabla\mathrm{symbolDistance}(z)\) は線形写像 \(4\langle d,\cdot\rangle d\) で、そのヘシアンは半正定値です（\(d=e_0-e_1\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.baseGradient21_eq"></a>

## 補題 `baseGradient21_eq`

### 式

$$
8\,\nabla\mathrm{symbolDistance}(z)=H(z)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基礎評価の勾配は、\(H(z)\) に等しいです。

### 証明の概略

1. 定義を展開して、スカラー倍の計算。

----

<a id="Tomabechi.Consistency.R123.baseHessian21_psd"></a>

## 補題 `baseHessian21_psd`

### 式

$$
\langle H(w),w\rangle\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(H\) は半正定値です。

### 証明の概略

1. \(\langle H(w),w\rangle=4\langle d,w\rangle^2\ge0\)。

----

<a id="Tomabechi.Consistency.R123.baseHessian21_bound"></a>

## 補題 `baseHessian21_bound`

### 式

$$
\|H(z)\|\le 8\|z\|
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\|H(z)\|\le 8\|z\|\) です。

### 証明の概略

1. \(|\langle d,z\rangle|\le\|d\|\|z\|\)（Cauchy–Schwarz）、\(\|d\|^2=2\)。

----

<a id="Tomabechi.Consistency.R123.SharedBaseBackground21"></a>

## 構造体 `SharedBaseBackground21`

### 式

$$
V_0\in C^2,\ \|\nabla V_0\|\le 8r,\ \nabla^2V_0\succeq0\ \text{（球 }\bar B_r(0),\ r<\tfrac14\text{）}
$$

### Lean のコメント（日本語訳）

> 定理21(21.3)のV₀を共有基礎評価で読んだときの条件。球B̄_r(0)、0<r<1/4。

### 定義の説明

定理 21 の (21.3) の \(V_0\) を、共有の基礎評価で読んだときの条件です（球 \(\bar B_r(0)\)、\(0<r<1/4\)）。フィールドは、球上の各点で \(C^2\)、勾配が \(H\)、勾配の微分が \(H\)、勾配の大きさが \(8r\) 以下（\(B=8r\)）、ヘシアンの下界（\(\beta=0\)）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedBaseBackground21"></a>

## 定理 `SharedModelSignature.sharedBaseBackground21`

### 式

$$
\mathrm{SharedBaseBackground21}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基礎評価の領域の条件のもとで、(21.3) の \(V_0\) についての条件が成り立ちます。

### 証明の概略

1. 球は箱の内部に入る（`closedBall_subset_interior_box`）。内部では \(N.\mathrm{base}.V_0\) が二次式（箱の内部の近傍で一致）なので、\(C^2\) と勾配が従う。
2. 勾配の大きさとヘシアンの下界は、`baseHessian21_bound` と `baseHessian21_psd`。

----

<a id="Tomabechi.Consistency.R123.sharedModel_baseBackground21"></a>

## 定理 `sharedModel_baseBackground21`

### 式

$$
\mathrm{SharedBaseBackground21}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、(21.3) の \(V_0\) の条件を満たします。

### 証明の概略

1. 前の定理に、`sharedModel_baseDomain` を渡す。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_base_background21"></a>

## 定理 `final_consistency_v2_with_base_background21`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedBaseBackground21}(N)
$$

### Lean のコメント（日本語訳）

> 最終存在宣言v2に、V₀を共有基礎評価と読んだ(21.3)の充足を加えた存在宣言。

### 補題の説明

最終の存在宣言の第 2 版に、\(V_0\) を共有の基礎評価と読んだ (21.3) の充足を加えた存在宣言です。

### 証明の概略

1. 第 2 版の存在宣言から \(N\) を取り、その基礎評価の領域の部品から、前の定理で (21.3) を得る。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
