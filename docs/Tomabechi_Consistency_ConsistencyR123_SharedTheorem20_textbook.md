# Tomabechi/Consistency/ConsistencyR123_SharedTheorem20.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedTheorem20.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedTheorem20.lean)（共有署名の定理20の原文条件）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| PL 不等式 | \(\lVert\nabla D\rVert^2\ge2\mu D\)。値と勾配の大きさを結び、指数収束を出す条件（Polyak–Łojasiewicz）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| Hausdorff（T2） | 異なる 2 点を開集合で分けられる位相。極限が一意。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**定理20の原文条件**を作るファイルです。基礎評価を `N.base` から読み、Euclid 拡張は箱の中でこの値に一致し、箱の外では同じ基準値をもつ二次式を使います。勾配・移動度・場の一致、PL 型の恒等式・距離の誤差・一点 K のコンパクト性と不変性を、原文の条件の入口に供給します。原文の象徴の零集合は**全域の合意の超平面**で、初期集合の一点 K とは区別します。

### 0.2 このファイルが証明していないこと

* 箱の外の評価は、二次式への拡張（具体的な選択）です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 基礎評価を N.base から読む。Euclidean 拡張は箱内でこの値に一致し、箱外では同じ baseline をもつ二次式を使う。勾配・移動度・場の一致、PL・距離誤差・一点 K のコンパクト性/不変性を原文条件入口へ供給する。原文の象徴零集合は全域合意超平面。初期集合の一点 K とは区別する。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.theorem20BaseExtension"></a>

## 定義 `SharedModelSignature.theorem20BaseExtension`

### 式

$$
N.\mathrm{base}.V_0(0,0)+8\,D_{\mathrm{symb}}(x)
$$

### Lean のコメント（日本語訳）

> Nに一度だけ格納したbaselineを保つEuclidean二次拡張。

### 定義の説明

共有署名 \(N\) に**一度だけ**格納した基準値（baseline）を保つ、Euclid 表示の二次の拡張です（\(V_0(0,0)+8D_{\mathrm{symb}}\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.theorem20BaseExtension_eq"></a>

## 補題 `theorem20BaseExtension_eq`

### 式

$$
N.\mathrm{theorem20BaseExtension}=\mathrm{sharedT20V0}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この拡張は、共通基礎評価のファイルの `sharedT20V0`（\(1+8D_{\mathrm{symb}}\)）に等しいです。

### 証明の概略

1. \(N.\mathrm{base}.V_0(0,0)=1\)（共通基礎評価の式に原点を代入して計算）。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem20Inputs"></a>

## 構造体 `SharedTheorem20Inputs`

### 式

$$
\text{定理20の全解析入力（共有署名を読む）}
$$

### Lean のコメント（日本語訳）

> 共有署名を読む定理20の全解析入力。flow自体は既存のEuclidean表現を使い、Nの一点adapterとの一致を必須化する。

### 定義の説明

共有署名を読む、**定理20の全解析入力**です。流れ自体は既存の Euclid 表現を使い、\(N\) の一点のアダプタとの**一致を必須**とします。フィールドは、(1) 箱の中で拡張が基礎評価に一致、(2) 流れの射影が \(N\) のアダプタの流れに一致、(3) 場 \(=-M\nabla V_{\mathrm{eff}}\)、(4) \(V_0\)・\(P\)・\(D\) の勾配、(5) \(D\) の非負性・零点、目標の非空・閉、傾き、(6) 移動度の逆・対称・強制性、(7) 結合 A・増幅 B の条件、(8) PL 型の恒等式、(9) 距離の誤差、(10) 一点 K のコンパクト性・前向き不変性、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem20Inputs"></a>

## 定理 `SharedKernelInputs.theorem20Inputs`

### 式

$$
\mathrm{SharedTheorem20Inputs}(N)
$$

### Lean のコメント（日本語訳）

> 共有基礎評価・一点flowを保存するNから、原文条件の全入力を構成する。

### 補題の説明

共有基礎評価と一点の流れを保存する \(N\) から、原文の条件の**全入力を構成**します。

### 証明の概略

1. 箱の中の一致は保存式と `theorem20BaseExtension_eq`、流れの射影は一点アダプタの保存式、場・勾配・距離・目標・傾き・移動度・PL・誤差は、前のファイルの補題を対応させる。
2. 一点 K のコンパクト性・前向き不変性は、K が線分の像であること（前のファイル）から。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem20Inputs.full_conclusion"></a>

## 定理 `SharedTheorem20Inputs.full_conclusion`

### 式

$$
\mathrm{SharedT20OriginalConclusions}(x,t_0)
$$

### Lean のコメント（日本語訳）

> このNの基礎評価を一般原文条件入口へ渡し、全一点初期対に適用する。指数距離、距離残差、strict下降、逆計量恒等式は元の全結論に含まれる。この射影では距離残差・距離評価・極限を読み出す。

### 補題の説明

この \(N\) の基礎評価を、一般の原文条件の入口に渡し、**すべての一点の初期対**に適用します。指数の距離、距離の残差、厳密な下降、逆計量の恒等式は、元の全結論に含まれます。

### 証明の概略

1. 定理20の入口（`theorem20_policy_flow_original_condition_conclusion`）に、`N.theorem20BaseExtension`・移動度・勾配・場・一点 K・入力のフィールドを渡す。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem20Inputs.point_conclusion"></a>

## 定理 `SharedTheorem20Inputs.point_conclusion`

### 式

$$
\text{距離の残差・距離評価・極限}
$$

### Lean のコメント（日本語訳）

> 全原文条件結論から距離残差・距離評価・極限を読み出す。

### 補題の説明

全原文条件の結論から、距離の残差・距離の評価・極限を読み出します。

### 証明の概略

1. 前の定理の結論の各成分を取り出す。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
