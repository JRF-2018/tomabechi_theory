# Tomabechi/Consistency/ConsistencyR123_SharedBaseDomain.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedBaseDomain.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedBaseDomain.lean)（基礎評価の領域 X := box を明示）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**基礎評価の状態領域を \(X:=\mathrm{box}\) と明示する**ファイルです。原文は、定理 1・4・20・24 で、同じ基礎評価 \(V_0\) を、状態領域 \(X\) の全体で使います。共有の基礎評価 \(V_0=1+\mathrm{potential}\) は、個人の閾値の残差 \(\max(x_i^2-\theta,0)\) を含むので、箱 \(\mathrm{box}=\{x\mid\forall i,\ |x_i|\le\tfrac14\}\) の外では、定理 20 の Euclid の二次式への拡張 \(1+8\cdot\mathrm{symbolDistance}\)（箱内では \(1+2D\) に一致）とは一致しません。

そこで、**状態領域を \(X:=\mathrm{box}\) と明示**します。

* 箱は、全方策のもとで前向き不変です（有限層の実軌道）。
* 箱の内部で、基礎評価は定理 1 の評価・有限層の実走行費・定理 20 の箱内の値 \(1+2D\) と一致します。
* 定理 20 の Euclid 拡張は、箱内で基礎評価と一致し、箱の内部の各点の近傍で一致します（微分条件は内部の開集合で比較できる）。
* 箱の外では、一致しない点が存在します（\(X\) を箱より広げると、別の評価になることの記録）。

### 0.2 このファイルが証明していないこと

* 箱の外の評価の統一（案 2）は行っていません。定理 1・4・20・24 の量化は、**箱の上のもの**として読みます。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文は 1・4・20・24 で同じ基礎評価 V₀ を状態領域 X 全体で使う。共有基礎評価 N.base.V0 = 1 + DA.potential は個人の閾値残差 max((xᵢ)²−θ,0) を含むので、箱 box = {x | ∀ i, |xᵢ| ≤ 1/4} の外では、定理20のEuclid二次式拡張 1 + 8·symbolDistance（箱内で 1+2D に一致）とは一致しない。そこで状態領域を X := box と明示する。…（以下、上の四点と、案2を行っていない旨）。

---

<a id="Tomabechi.Consistency.R123.SharedBaseDomain"></a>

## 構造体 `SharedBaseDomain`

### 式

$$
X:=\mathrm{box}\text{ 上で、基礎評価 }V_0\text{ が定理1・費用・定理20と一致}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態領域を \(X:=\mathrm{box}\) と明示する受入の型です。フィールドは、箱が有限層の任意のゲイン方策のもとで前向き不変、箱内で共有基礎評価が定理 1 の評価に一致、箱内で有限層の実走行費が共有基礎評価に一致（全方策）、箱内で定理 20 の値 \(1+2D\) に一致、Euclid 拡張が箱内で共有基礎評価に一致して箱の内部の各点の近傍で一致、箱の外では一致しない点がある（領域を \(X:=\mathrm{box}\) に限る理由）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.baseDomain_outside_example"></a>

## 補題 `baseDomain_outside_example`

### 式

$$
\exists z\notin\mathrm{box},\ \text{拡張}(z)\ne V_0(z)
$$

### Lean のコメント（日本語訳）

> 箱外の不一致の具体例：座標(1,1)。拡張は1、共有基礎評価は1+2·(1−1/10)。

### 補題の説明

箱の外での**不一致の具体例**です。座標 \((1,1)\) で、Euclid の拡張は \(1\)、共有基礎評価は \(1+2\,(1-\tfrac1{10})\) です。

### 証明の概略

1. \((1,1)\) が箱の外であることを座標で確かめる。
2. 拡張と共有基礎評価の定義を展開して、数値を比べる。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedBaseDomain"></a>

## 定理 `SharedModelSignature.sharedBaseDomain`

### 式

$$
\mathrm{SharedBaseDomain}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

追加条件のもとで、署名は基礎評価の領域の条件を満たします。

### 証明の概略

1. 前向き不変性は、有限層の軌道の保存式と、箱の不変性の補題。
2. 各一致は、基礎評価の補題（`theorem1_matches`・`theorem20_box_value`）と、追加条件の有限層の費用の式。
3. 箱の外の不一致は、前の補題。

----

<a id="Tomabechi.Consistency.R123.sharedModel_baseDomain"></a>

## 定理 `sharedModel_baseDomain`

### 式

$$
\mathrm{SharedBaseDomain}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、基礎評価の領域の条件を満たします。

### 証明の概略

1. 追加条件の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_base_domain"></a>

## 定理 `final_consistency_with_base_domain`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedBaseDomain}(N)
$$

### Lean のコメント（日本語訳）

> 先行する受入型に、基礎評価の領域（X := box）を加えた存在宣言。

### 補題の説明

先行する受入の型に、基礎評価の領域（\(X:=\mathrm{box}\)）を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は、`sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
