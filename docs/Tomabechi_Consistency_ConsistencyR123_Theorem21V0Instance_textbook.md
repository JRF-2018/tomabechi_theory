# Tomabechi/Consistency/ConsistencyR123_Theorem21V0Instance.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Theorem21V0Instance.lean`](../Tomabechi/Consistency/ConsistencyR123_Theorem21V0Instance.lean)（定理21を V₀ = 共有基礎評価で適用した実例）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 21 を、\(V_0=\)共有の基礎評価で適用した実例**を作るファイルです。以前は、(21.3) の \(V_0\) の条件（\(C^2\)・\(\|\nabla V_0\|\le B\)・\(\nabla^2V_0\succeq-\beta I\)）だけを `V₀ = N.base.V0` について示しました。ここでは、**定理 21 の単独の実例**を作ります。

* 背景 \(V_0=\) `N.base.V0` ∘ 座標、偏り \(S(x)=-\|x\|^2/2\)（\(m=1\)）、\(\kappa=1\)、
* 中心 \(x_b=0\)（合意点）、球 \(\bar B_{1/8}(0)\)（箱の内部）、移動度は恒等、
* \(B=8r=1\)、\(\beta=0\)、臨場感の利得 \(p=9>p_{\rm crit}=\max\{\beta,B/r\}/(\kappa m)=8\)、
* 初期点は \(\|x_0\|=1/16\)、部分準位は原文どおり \(\{x\in U_b\mid\tilde V(x)\le\tilde V(x_0)\}\)。

`MeanFieldStageInput` を構成して、定理 21 の四つの結論（一意の最小点・距離・指数収束・直接 KL CMI）の一般の入口 `meanField_stage_theorem21_four_conclusions_directKL` を適用します。

### 0.2 このファイルが証明していないこと

* 中心 0・球の大きさ・初期点・利得は、**具体的な値の一つ**です（存在の実例）。
* 段の背景の地形 \(R_n\)（22/23-B）とは**別の入力**で、\(R_n=\) `N.base.V0` とは主張しません。
* 情報の部分（ゴールの分布・行為）は、C3 の上位層の法則を使います。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 以前は (21.3) の V₀ の条件（C²・‖∇V₀‖≤B・∇²V₀≽−βI）だけを V₀ = N.base.V0 について示した。ここでは定理21の単独の実例を作る：背景 V₀ = N.base.V0∘coords、偏り S(x) = −‖x‖²/2（m=1）、κ=1、中心 x_b = 0（合意点）、球 B̄_{1/8}(0)（箱の内部）、移動度は恒等、B = 8r = 1、β = 0、臨場感利得 p = 9 > p_crit = max{β, B/r}/(κm) = 8。初期点は ‖x₀‖ = 1/16 で、部分準位は原文どおり {x ∈ U_b | Ṽ(x) ≤ Ṽ(x₀)}。MeanFieldStageInput を構成して、定理21の四結論の一般入口 meanField_stage_theorem21_four_conclusions_directKL を適用する。範囲：中心 0・球の大きさ・初期点・利得は具体値の一つ（存在の実例）。段の背景地形 R_n（22/23-B）とは別の入力で、R_n ＝ N.base.V0 とは主張しない。情報の部分は C3 の上位層の law を使う。

---

<a id="Tomabechi.Consistency.R123.v0Background"></a>

## 定義 `v0Background`

### 式

$$
V_0(z)=N.\mathrm{base}.V_0(\mathrm{coords}(z),0)
$$

### Lean のコメント（日本語訳）

> 背景V₀=N.base.V0の認知座標（Euclid）表示（sharedModel）。

### 定義の説明

背景 \(V_0=\) `N.base.V0` の、認知座標（Euclid）表示です（`sharedModel` について）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0AveragePresentation"></a>

## 定義 `v0AveragePresentation`

### 式

$$
S(x)=-\tfrac12\|x\|^2\ \text{を、上位層の Dirac 平均で表す}
$$

### Lean のコメント（日本語訳）

> 偏りの平均場S(x)=−‖x‖²/2を上位層のDirac平均で表す平均化表現（中心は全原子で0）。

### 定義の説明

偏りの平均場 \(S(x)=-\|x\|^2/2\) を、上位層の Dirac 平均で表す**平均化表現**です（中心は、全原子で 0）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Radius"></a>

## 定義 `v0Radius`

### 式

$$
r=\tfrac18
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

球の半径 \(r=1/8\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Initial"></a>

## 定義 `v0Initial`

### 式

$$
x_0=\tfrac1{16}e_0
$$

### Lean のコメント（日本語訳）

> 初期点x₀=(1/16)e₀、‖x₀‖=1/16=r/2。

### 定義の説明

初期点 \(x_0=\tfrac1{16}e_0\) です（\(\|x_0\|=1/16=r/2\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Initial_norm"></a>

## 補題 `v0Initial_norm`

### 式

$$
\|x_0\|=\tfrac1{16}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期点の大きさは \(1/16\) です。

### 証明の概略

1. ノルムのスカラー倍（`norm_smul`）で計算。

----

<a id="Tomabechi.Consistency.R123.v0MeanField"></a>

## 定義 `v0MeanField`

### 式

$$
S(x)=-\tfrac12\|x\|^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

偏りの平均場 \(S(x)=-\tfrac12\|x\|^2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0AveragePresentation_integral"></a>

## 補題 `v0AveragePresentation_integral`

### 式

$$
\text{平均化表現の積分値}=S(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平均化表現の積分値は、平均場 \(S(x)\) に等しいです。

### 証明の概略

1. Dirac 測度の積分（`integral_dirac`）に帰着して計算する。

----

<a id="Tomabechi.Consistency.R123.v0Background_eq"></a>

## 補題 `v0Background_eq`

### 式

$$
\|x\|\le\tfrac18\ \Rightarrow\ V_0=1+8\,\mathrm{symbolDistance}
$$

### Lean のコメント（日本語訳）

> 球‖x‖≤1/8上でV₀=1+8·symbolDistance（箱内の二次式）。

### 補題の説明

球 \(\|x\|\le1/8\) の上で、\(V_0=1+8\cdot\mathrm{symbolDistance}\)（箱の内部の二次式）です。

### 証明の概略

1. 球が箱の内部に入ること（`closedBall_subset_interior_box`）。
2. 箱の上の拡張の一致（`extension_eq_on_box`）で書き換える。

----

<a id="Tomabechi.Consistency.R123.symbolDistance_nonneg'"></a>

## 補題 `symbolDistance_nonneg'`

### 式

$$
0\le\mathrm{symbolDistance}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

象徴の目標への距離は非負です。

### 証明の概略

1. 既存の補題 `c1EuclideanSymbolDistance_nonneg`。

----

<a id="Tomabechi.Consistency.R123.symbolDistance_le"></a>

## 補題 `symbolDistance_le`

### 式

$$
\mathrm{symbolDistance}(x)\le\tfrac12\|x\|^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

象徴の目標への距離は、\(\tfrac12\|x\|^2\) 以下です。

### 証明の概略

1. Cauchy–Schwarz の不等式 \(|\langle d,x\rangle|\le\|d\|\|x\|\) と、\(\|d\|^2=2\)。

----

<a id="Tomabechi.Consistency.R123.v0Sublevel"></a>

## 定義 `v0Sublevel`

### 式

$$
\{x\in\bar B_{1/8}(0)\mid\tilde V(x)\le\tilde V(x_0)\}
$$

### Lean のコメント（日本語訳）

> 部分準位：球内でṼ(x)≤Ṽ(x₀)（κ=1、p=9）。

### 定義の説明

**部分準位**です。球の内部で、\(\tilde V(x)\le\tilde V(x_0)\)（\(\kappa=1\)、\(p=9\)）となる点の集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Sublevel_norm_le"></a>

## 補題 `v0Sublevel_norm_le`

### 式

$$
x\in\text{部分準位}\ \Rightarrow\ \|x\|\le\tfrac1{10}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

部分準位の点は、大きさが \(1/10\) 以下です（球の内部に入る）。

### 証明の概略

1. 背景の式（`v0Background_eq`）で書き換え、`symbolDistance` の上下界（前の二つの補題）から \(\|x\|\) の上界を `nlinarith` で出す。

----

<a id="Tomabechi.Consistency.R123.v0StageInput"></a>

## 定義 `v0StageInput`

### 式

$$
\text{定理21の }\mathrm{MeanFieldStageInput}
$$

### Lean のコメント（日本語訳）

> 定理21のMeanFieldStageInput：V₀=N.base.V0、偏り−‖x‖²/2、中心0、球B̄_{1/8}(0)。

### 定義の説明

定理 21 の `MeanFieldStageInput` です。背景 \(V_0=\) `N.base.V0`、偏り \(-\|x\|^2/2\)、中心 0、球 \(\bar B_{1/8}(0)\)、移動度は恒等、\(B=8r=1\)、\(\beta=0\)、臨場感の利得 \(p=9\)。各条件（\(C^2\)・勾配の大きさ・ヘシアン・部分準位の包含・コンパクト性など）を、上の補題で埋めて組み立てます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Stage_theorem21"></a>

## 定義 `v0Stage_theorem21`

### 式

$$
\text{定理21の四結論（一意最小点・距離・指数収束・直接 KL CMI）}
$$

### Lean のコメント（日本語訳）

> 定理21の四結論（一意最小点・距離・指数収束・直接KL CMI）を、V₀=N.base.V0の段へ適用。

### 定義の説明

定理 21 の**四つの結論**（一意の最小点・距離・指数収束・直接 KL CMI）を、\(V_0=\) `N.base.V0` の段へ適用したものです。

### 証明の概略

1. 一般の入口 `meanField_stage_theorem21_four_conclusions_directKL` に、段の入力と、情報の部分（C3 の上位層の法則）を渡す。

----

<a id="Tomabechi.Consistency.R123.V0StageConclusion"></a>

## 定義 `V0StageConclusion`

### 式

$$
\text{実例の結論（四結論）の命題}
$$

### Lean のコメント（日本語訳）

> 実例の結論（定理21の四結論）の命題。

### 定義の説明

実例の結論（定理 21 の四結論）の命題です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Stage_theorem21_holds"></a>

## 定理 `v0Stage_theorem21_holds`

### 式

$$
\mathrm{V0StageConclusion}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実例の結論が成り立ちます。

### 証明の概略

1. `v0Stage_theorem21`。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem21V0"></a>

## 構造体 `SharedTheorem21V0`

### 式

$$
\text{背景}=\text{基礎評価}\wedge\text{中心 }0\wedge p>p_{\rm crit}\wedge\text{初期点が中心でない}\wedge\text{四結論}
$$

### Lean のコメント（日本語訳）

> 定理21をV₀=共有基礎評価で適用した実例の受入型。

### 定義の説明

定理 21 を \(V_0=\)共有の基礎評価で適用した実例の**受入の型**です。フィールドは、背景が `N.base.V0`、中心が 0、利得が臨界値を超える（\(p_{\rm crit}=\max\{\beta,B/r\}/(\kappa m)=8<9=p\)）、初期点が中心でない、結論（四結論）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_theorem21V0"></a>

## 定理 `sharedModel_theorem21V0`

### 式

$$
\mathrm{SharedTheorem21V0}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、実例の受入の型を満たします。

### 証明の概略

1. 背景・中心は定義から `rfl`。利得の臨界値の不等式は数値計算。初期点が中心でないことは、大きさが \(1/16\ne0\) から。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v4"></a>

## 定理 `final_consistency_v4`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedTheorem21V0}(N)
$$

### Lean のコメント（日本語訳）

> v4：v3の全受入型に、V₀=共有基礎評価での定理21の実例を加えた存在宣言。

### 補題の説明

第 4 版です。第 3 版の全受入の型に、\(V_0=\)共有の基礎評価での定理 21 の実例を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
