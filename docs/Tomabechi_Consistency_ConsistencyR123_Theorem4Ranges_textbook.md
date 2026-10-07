# Tomabechi/Consistency/ConsistencyR123_Theorem4Ranges.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Theorem4Ranges.lean`](../Tomabechi/Consistency/ConsistencyR123_Theorem4Ranges.lean)（定理4の値域条件 (M6.1) を N の述語に入れる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文 §6 は、定理 4 に \(V_0\ge0\)、\(P\in[0,1]\)、\(Q\in[-1,1]\)、\(\kappa>0\) を課し、\(\tilde V=V_0-\kappa PQ\ge-\kappa\) を述べます。以前は \(P=\exp(-F)\in(0,1]\)、\(Q=1\) の値域の補題を、共有基礎評価の側に置きました（`commonBasePresenceP_mem` など）が、\(N\) の述語には入っていませんでした。ここでは、\(N\) 自身の基礎評価 `N.base.V0` について、定理 4 の一般の補題 `effectivePotential_lower_bound`（原文の下限 \(\tilde V\ge-\kappa\)）を適用して、値域条件を一つの受入の型 `SharedTheorem4Ranges N` にまとめます。

### 0.2 このファイルが証明していないこと

* \(P=\exp(-\mathrm{potential})\)、\(Q=1\)、\(\kappa=1\) の**具体的な選択**についての値域です。\(P\) を別の関数に取り替えた場合の値域は主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §6 は定理4に V₀ ≥ 0、P ∈ [0,1]、Q ∈ [−1,1]、κ > 0 を課し、Ṽ = V₀ − κPQ ≥ −κ を述べる。以前は P = exp(−F) ∈ (0,1]、Q = 1 の値域補題を共有基礎評価の側に置いた（commonBasePresenceP_mem など）が、N の述語には入っていなかった。ここでは N 自身の基礎評価 N.base.V0 について、定理4の一般補題 effectivePotential_lower_bound（原文の下限 Ṽ ≥ −κ）を適用して、値域条件を一つの受入型 SharedTheorem4Ranges N にまとめる。範囲：P = exp(−DA.potential)、Q = 1、κ = 1 の具体的な選択についての値域である。P を別の関数に取り替えた場合の値域は主張しない。

---

<a id="Tomabechi.Consistency.R123.SharedTheorem4Ranges"></a>

## 構造体 `SharedTheorem4Ranges`

### 式

$$
V_0\ge0,\ P\in[0,1],\ Q\in[-1,1],\ \kappa>0,\ \tilde V\ge-\kappa
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理 4 の値域条件 (M6.1) をまとめた受入の型です。フィールドは、\(V_0\ge0\)、\(P\in[0,1]\)、\(Q\in[-1,1]\)、\(\kappa>0\)、実効ポテンシャル \(\tilde V\ge-\kappa\)、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedTheorem4Ranges"></a>

## 定理 `SharedModelSignature.sharedTheorem4Ranges`

### 式

$$
\mathrm{SharedTheorem4Ranges}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

任意の共有署名が、定理 4 の値域条件を満たします。

### 証明の概略

1. \(V_0\ge0\)：共有基礎評価の正値性。\(P,Q\) の値域：`commonBasePresenceP_mem`・`commonBasePresenceQ_mem`。
2. \(\tilde V\ge-\kappa\)：定理 4 の一般の補題 `effectivePotential_lower_bound`。

----

<a id="Tomabechi.Consistency.R123.sharedModel_theorem4Ranges"></a>

## 定理 `sharedModel_theorem4Ranges`

### 式

$$
\mathrm{SharedTheorem4Ranges}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、値域条件を満たします。

### 証明の概略

1. 前の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_theorem4_ranges"></a>

## 定理 `final_consistency_v2_with_theorem4_ranges`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{SharedTheorem4Ranges}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、定理 4 の値域条件を加えた版です。

### 証明の概略

1. 存在宣言です。前の版から \(N\) を取り、値域条件を加える。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
