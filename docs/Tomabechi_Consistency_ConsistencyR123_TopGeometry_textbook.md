# Tomabechi/Consistency/ConsistencyR123_TopGeometry.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_TopGeometry.lean`](../Tomabechi/Consistency/ConsistencyR123_TopGeometry.lean)（共通束の頂点の状態の、内積空間の構造）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共通束の**頂点の状態の型**（型の同一視で \(E_2=\mathbb R^2\) に等しい）に、**内積空間の構造**を移し、既存の距離との一致を証明するファイルです。定理20（勾配流）など、内積空間を要求する一般の定理を、頂点の状態の上で使うための準備です。インスタンスはこのファイルの中で**局所的**に使い、共有署名の距離は**変更しません**。

* ノルム・内積を型の同一視から移し、既存の距離に一致すること、完備であることを示す。
* 頂点の状態と \(E_2\) の間の**線形等長同型**が、既存の頂点を保つ写像と一致すること。
* 既存の距離構造を**定義として含む**解析用のノルム・内積・同型（`sharedTopCompatible*`）。

### 0.2 このファイルが証明していないこと

* 技術的な構成のファイルで、数学的な新しい主張はありません（距離・完備性の同一性の確認です）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 頂点の型同定から解析構造を移し、既存の距離との一致を証明する。インスタンスはこのファイル内で局所的に使い、共有署名の距離を変更しない。

---

<a id="Tomabechi.Consistency.R123.chartNorm"></a>

## 定義 `chartNorm`

### 式

$$
\text{型の同一視 }S=E_2\text{ から移すノルム}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

型 \(S\) が \(E_2\) と等しいという同一視から、\(S\) にノルム付き加法群の構造を移します。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.chartInner"></a>

## 定義 `chartInner`

### 式

$$
\text{同じ同一視から移す内積}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同じ同一視から、内積空間の構造を移します。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopNorm"></a>

## 定義 `sharedTopNorm`

### 式

$$
\text{頂点の状態型のノルム付き加法群}
$$

### Lean のコメント（日本語訳）

> 頂点の型同定から得るノルム付き加法群。

### 定義の説明

共通束の頂点の状態の型に、型の同一視から得る**ノルム付き加法群**の構造を与えます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.instance@L23"></a>

## インスタンス `instance@L23`

### 式

$$
\text{頂点の状態型はノルム付き加法群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の構造を、このファイルの中だけで使う局所インスタンスにします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopInner"></a>

## 定義 `sharedTopInner`

### 式

$$
\text{同じノルムに対応する実内積}
$$

### Lean のコメント（日本語訳）

> 同じノルムに対応する実内積。

### 定義の説明

同じノルムに対応する**実内積**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.chartDist"></a>

## 補題 `chartDist`

### 式

$$
d_S(x,y)=d_{E_2}(\mathrm{cast}\,x,\mathrm{cast}\,y)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

移したノルムの距離は、同一視した先の距離に一致します。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 同一視で場合分け（`subst`）して、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R123.instance@L32"></a>

## インスタンス `instance@L32`

### 式

$$
\text{頂点の状態型は実内積空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の内積を、このファイルの中だけで使う局所インスタンスにします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopMetric_eq_normMetric"></a>

## 補題 `sharedTopMetric_eq_normMetric`

### 式

$$
\text{既存の頂点の距離}=\text{移したノルムの距離}
$$

### Lean のコメント（日本語訳）

> 既存の頂点距離を変えずに一般解析入口を使える。

### 補題の説明

既存の頂点の距離は、移したノルムから決まる距離と**一致**します。したがって、既存の距離を変えずに、一般の解析の入口（内積空間を要求する定理20など）を使えます。

### 証明の概略

1. 距離の外延性。各二点で `chartDist` と、既存の距離の定義（同一視を通した距離）を比べる。

----

<a id="Tomabechi.Consistency.R123.chartLinear"></a>

## 定義 `chartLinear`

### 式

$$
S\simeq_{\ell i}E_2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

同一視から得る、\(S\) から \(E_2\) への**線形等長同型**です。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.chartComplete"></a>

## 補題 `chartComplete`

### 式

$$
S\ \text{は完備}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

移したノルムで、\(S\) は完備です。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 同一視で場合分けして、\(E_2\) の完備性。

----

<a id="Tomabechi.Consistency.R123.chartLinear_apply"></a>

## 補題 `chartLinear_apply`

### 式

$$
\mathrm{chartLinear}(x)=\mathrm{cast}\,x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この同型は、型の変換（cast）そのものです。型の同一視（`S = E2`）に沿った補助の構成です（`private`）。

### 証明の概略

1. 同一視で場合分け（`rfl`）。

----

<a id="Tomabechi.Consistency.R123.sharedTopComplete"></a>

## 補題 `sharedTopComplete`

### 式

$$
\text{頂点は完備}
$$

### Lean のコメント（日本語訳）

> 移されたノルムと同じ既存距離で頂点は完備。

### 補題の説明

頂点の状態の型は、既存の距離で**完備**です。

### 証明の概略

1. 既存の距離は移したノルムの距離（前の補題）。`chartComplete`。

----

<a id="Tomabechi.Consistency.R123.sharedTopLinearIsometryEquiv"></a>

## 定義 `sharedTopLinearIsometryEquiv`

### 式

$$
\text{頂点の状態}\simeq_{\ell i}E_2
$$

### Lean のコメント（日本語訳）

> 頂点型同定は実線形等長同型でもある。

### 定義の説明

頂点の型の同一視は、**実線形の等長同型**でもあります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopLinearIsometryEquiv_apply"></a>

## 補題 `sharedTopLinearIsometryEquiv_apply`

### 式

$$
\text{同型}=\mathrm{fullCommonTopStateEquiv}
$$

### Lean のコメント（日本語訳）

> 解析用の線形同型は既存の頂点保存写像と同じ写像である。

### 補題の説明

解析に使う線形同型は、既存の頂点を保つ写像と、**同じ写像**です。

### 証明の概略

1. `chartLinear_apply`。

----

<a id="Tomabechi.Consistency.R123.replacePseudo"></a>

## 定義 `replacePseudo`

### 式

$$
\text{擬距離を置き換えたノルム付き加法群}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ノルム付き加法群の擬距離の構造を、等しい別の擬距離に置き換えたものです。距離の「定義的な一致」を得るための補助の構成です（`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.replacePseudo_eq"></a>

## 補題 `replacePseudo_eq`

### 式

$$
\mathrm{replacePseudo}\ g\ m=g
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

置き換えても、元の構造と等しいです。

### 証明の概略

1. 等式 \(m=g\) で場合分けして `rfl`。

----

<a id="Tomabechi.Consistency.R123.replaceInner"></a>

## 定義 `replaceInner`

### 式

$$
\text{置き換えたノルムに対応する内積}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

置き換えたノルムに対応する、同じ内積です（補助、`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.replaceIso"></a>

## 定義 `replaceIso`

### 式

$$
\text{置き換えたノルムでの等長同型}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

置き換えたノルムに対応する、等長同型です（補助、`private`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopCompatibleNorm"></a>

## 定義 `sharedTopCompatibleNorm`

### 式

$$
\text{既存の距離構造を定義的に含むノルム}
$$

### Lean のコメント（日本語訳）

> 既存の距離構造を定義的に含む解析用ノルム。

### 定義の説明

**既存の距離の構造を定義として含む**、解析用のノルムです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopCompatibleInner"></a>

## 定義 `sharedTopCompatibleInner`

### 式

$$
\text{既存距離を含むノルムに対応する内積}
$$

### Lean のコメント（日本語訳）

> 既存距離を含むノルムに対応する、同じ実内積。

### 定義の説明

既存の距離を含むノルムに対応する、同じ実内積です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedTopCompatibleMetric"></a>

## 補題 `sharedTopCompatibleMetric`

### 式

$$
\text{距離構造は定義的に一致}
$$

### Lean のコメント（日本語訳）

> 既存の距離構造と解析構造の親インスタンスは定義的に一致する。

### 補題の説明

既存の距離の構造と、解析の構造の親のインスタンスは、**定義として一致**します。

### 証明の概略

1. `rfl`（定義から）。

----

<a id="Tomabechi.Consistency.R123.sharedTopCompatibleIso"></a>

## 定義 `sharedTopCompatibleIso`

### 式

$$
\text{既存距離を保つ内積空間構造での、頂点の等長同型}
$$

### Lean のコメント（日本語訳）

> 既存距離を保つ内積空間構造での頂点等長同型。

### 定義の説明

既存の距離を保つ内積空間の構造での、頂点の**等長同型**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.replaceIso_apply"></a>

## 補題 `replaceIso_apply`

### 式

$$
\mathrm{replaceIso}(x)=\mathrm{iso}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

置き換えた同型は、元の同型と同じ写像です（補助、`private`）。

### 証明の概略

1. 等式で場合分けして `rfl`。

----

<a id="Tomabechi.Consistency.R123.sharedTopCompatibleIso_apply"></a>

## 補題 `sharedTopCompatibleIso_apply`

### 式

$$
\text{同型}=\mathrm{fullCommonTopStateEquiv}
$$

### Lean のコメント（日本語訳）

> 距離構造を合わせた解析同型も元の頂点写像と同じである。

### 補題の説明

距離の構造を合わせた解析の同型も、元の頂点の写像と同じです。

### 証明の概略

1. `replaceIso_apply` と `sharedTopLinearIsometryEquiv_apply`。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
