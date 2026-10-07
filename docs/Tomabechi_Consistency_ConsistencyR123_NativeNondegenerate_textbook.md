# Tomabechi/Consistency/ConsistencyR123_NativeNondegenerate.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_NativeNondegenerate.lean`](../Tomabechi/Consistency/ConsistencyR123_NativeNondegenerate.lean)（非退化性を N 自身の field から読む）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 固定点 | \(F(x)=x\) をみたす点。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**非退化性を、\(N\) 自身のフィールドから読む**ファイルです。従来の非退化性 N3 は、正のゴールエントロピーを、C3 の定数 `inputMass` から読んでいました（`N.informationLaw` からではない）。また、N6 の履歴固定点の分離は、`N.legacy` に格納した固定点を読んでいました。ここでは、次を \(N\) 自身の量で述べ直します。

* `N.informationLaw (N.stageAddress 0)` の条件付きゴールエントロピー（事前核の積分）が正。直接 CMI が \(\log 2>0\) であることと、\(I(G;Y\mid X)\le H(G\mid X)\) から出します（定数 `inputMass` を読まない）。
* `N.scm` 自身の \(\Gamma\)（状態の式）が、履歴 false/true で異なる主体・層・標本がある。定理 16/25 の固定点の履歴の分離を、SCM 側から読んだものです。

### 0.2 このファイルが証明していないこと

* 一般の \(N\) についての導出ではなく、**`sharedModel` についての証明**です（存在宣言に必要な範囲）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 従来の非退化性 N3 は、正のゴールエントロピーを C3 の定数 inputMass から読んでいた（N.informationLaw からではない）。また N6 の履歴固定点の分離は N.legacy に格納した固定点を読んでいた。ここでは次を N の native な量で述べ直す。…（以下、上の二点）。一般の N についての導出ではなく、sharedModel についての証明である（存在宣言に必要な範囲）。

---

<a id="Tomabechi.Consistency.R123.lawGoalEntropy"></a>

## 定義 `lawGoalEntropy`

### 式

$$
\int H(G\mid X=x)\,dP_X(x)
$$

### Lean のコメント（日本語訳）

> 情報lawの条件付きゴールエントロピー∫H(G|X=x)dP_X。確率測度でないときは0。

### 定義の説明

情報の法則の**条件付きゴールエントロピー** \(\int H(G\mid X=x)\,dP_X\) です。確率測度でないときは 0 とします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.lawGoalEntropy_upper_pos"></a>

## 補題 `lawGoalEntropy_upper_pos`

### 式

$$
0<H(G\mid X)\ \ (\text{上位層})
$$

### Lean のコメント（日本語訳）

> 上位層のlawでは、条件付きゴールエントロピーは直接CMI（=log 2）以上で、特に正。

### 補題の説明

上位層の法則では、条件付きゴールエントロピーは、直接 CMI（\(=\log 2\)）以上で、特に**正**です。

### 証明の概略

1. 確率測度性から場合分けを除く。
2. 一般の不等式 \(I(G;Y\mid X)\le H(G\mid X)\)（`directCMI_le_inputGoalEntropy_of_finite`）と、上位層の CMI の評価値 \(\log 2>0\) を使う。

----

<a id="Tomabechi.Consistency.R123.SharedNativeNondegenerate"></a>

## 構造体 `SharedNativeNondegenerate`

### 式

$$
\text{情報が正}\ \wedge\ \text{SCM の }\Gamma\text{ が履歴で分離}
$$

### Lean のコメント（日本語訳）

> N自身の量で読む非退化性。

### 定義の説明

\(N\) **自身の量**で読む非退化性です。フィールドは、(1) `N.informationLaw (N.stageAddress 0)` の直接 CMI（定理 19 の評価）と、条件付きゴールエントロピーが、ともに正、(2) `N.scm` 自身の \(\Gamma\) が、履歴 false/true で異なるような、主体・層・標本がある（定理 16/25 の固定点の履歴の分離を、SCM から読む）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.informationPositive"></a>

## 補題 `SharedDataPreservation.informationPositive`

### 式

$$
0<\mathrm{score}\ \wedge\ 0<H(G\mid X)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式のもとで、段 0 の情報の法則について、直接 CMI の評価値と、条件付きゴールエントロピーがともに正です。

### 証明の概略

1. 段 0 の住所は底でない（正の層）ことを、保存式（`stageAddress`）と補題で示す。
2. 底でない点の情報の法則は上位層のもの。上位層の評価値は \(\log 2\)、条件付きゴールエントロピーは上の補題。

----

<a id="Tomabechi.Consistency.R123.sharedModel_scm_gamma_separates"></a>

## 補題 `sharedModel_scm_gamma_separates`

### 式

$$
\exists d,a,u,\ \Gamma(d,a,\text{false},u)\ne\Gamma(d,a,\text{true},u)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有モデルの SCM の \(\Gamma\)（状態の式）が、履歴 false と true で異なる主体・層・標本があります。

### 証明の概略

1. 主体 false・底の層・標本 (false, false) を取る。
2. SCM の状態の式が、定理 16/25 の固定点の符号（`commonConceptStateCode`）であることから、履歴 false と true の固定点が異なること（定理 16/25 の固定点の分離）に帰着。

----

<a id="Tomabechi.Consistency.R123.sharedModel_nativeNondegenerate"></a>

## 定理 `sharedModel_nativeNondegenerate`

### 式

$$
\mathrm{SharedNativeNondegenerate}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、\(N\) 自身の量で読む非退化性を満たします。

### 証明の概略

1. 前の二つの補題を組にする。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_native_nondegeneracy"></a>

## 定理 `final_consistency_with_native_nondegeneracy`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedNativeNondegenerate}(N)
$$

### Lean のコメント（日本語訳）

> 先行する受入型に、N自身の量で読む非退化性を加えた存在宣言。

### 補題の説明

先行する受入の型に、\(N\) 自身の量で読む非退化性を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は、`sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
