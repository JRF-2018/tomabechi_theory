# Tomabechi/Consistency/ConsistencyR123_SharedKernelInputs.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedKernelInputs.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedKernelInputs.lean)（共有署名を読む、解析の入口の受け入れ条件）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の**解析の入口の受け入れ条件**（`SharedKernelInputs`）をまとめ、その上で、**定理24・24→26・25・15→23** の一般の入口を、**同じ \(N\) のデータ**に適用するファイルです。旧い局所入力の受け入れ、共通束の 24・26 のデータの保存、同じ観測からの 15→23 の入力、同じ SCM の 25 の入力、一点の初期集合の原文 §2.4 の入口を、一つの署名に接続します。

### 0.2 このファイルが証明していないこと

* 冒頭のコメントのとおり、この型は**既に構成した入口の束**で、定理4・20の共有評価の残る解析条件や、全原文条件の共有の最終監査を**完了した**という意味ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 旧局所入力の受入、共通束24/26データの保存、同じ観測からの15→23入力、同じ SCM の25入力、一点初期 O24 を一つの署名に接続する。この型は既に構成した入口の束であり、定理4/20共有評価の残る解析条件や全原文共有条件の最終監査を完了したという意味ではない。

---

<a id="Tomabechi.Consistency.R123.SharedKernelInputs"></a>

## 構造体 `SharedKernelInputs`

### 式

$$
\text{共有署名を読む解析入口の受け入れ条件}
$$

### Lean のコメント（日本語訳）

> 各条件はNの実データを読む。未監査の一般入口を完了条件から除く型ではない。

### 定義の説明

共有署名 \(N\) の**実データ**を読む、解析の入口の受け入れ条件の束です。フィールドは、(1) 以前の署名の原文前提・追加条件・非退化性、(2) 共有保存式、(3) 共有署名のエントロピー入力、(4) SCM の出力が候補に依らない（a.e.）、(5) 候補が正の質量、(6) 一点の TCZ は合意点だけ、(7) 一点の距離の評価。未監査の一般の入口を、完了の条件から**除く型ではありません**。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem24"></a>

## 定理 `SharedKernelInputs.theorem24`

### 式

$$
\forall a<\top,\ 0<V^*\ \wedge\ \neg\mathrm{PZS}
$$

### Lean のコメント（日本語訳）

> 新署名の24一般入口を全真部分点に適用する。別の固定24-dataの結論を使わず、N.dataの入力recordを渡す。

### 補題の説明

新しい署名の、定理24の一般の入口を、**頂より下のすべての点**に適用します。別の固定したデータの結論を使わず、\(N.\mathrm{data}\) の入力の構造体を渡します。結論は、最適値が正で、PZS（永久零価値）が起こらないことです。

### 証明の概略

1. 定理24の下位の結論の一般形（`theorem24_lower_conclusions_from_nonnegativeTimeData`）に `N.data` を渡す。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem25"></a>

## 定理 `SharedKernelInputs.theorem25`

### 式

$$
\forall d,a,\ \neg\,\mathrm{hasAtman}(d,a)
$$

### Lean のコメント（日本語訳）

> 同じNのSCMへ定理25の測度付き一般入口を適用する。

### 補題の説明

同じ \(N\) の SCM に、定理25の測度つきの一般の入口を適用して、**すべての主体・層で自己（アートマン）が存在しない**ことを得ます。

### 証明の概略

1. 出力が候補に依らない（a.e.、入力のフィールド）ことから、一般の入口を適用する。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem24_26"></a>

## 定理 `SharedKernelInputs.theorem24_26`

### 式

$$
\text{定理24→26 の全結論（全非負初期対）}
$$

### Lean のコメント（日本語訳）

> Nの同じ24-data/26-dynamicsを一般入口へ渡す。全真部分層の正価値、頂点PZS分類、速度付き距離/評価、最適値極限、零評価目標同値と不変性を、全非負初期対についてまとめて得る。

### 補題の説明

\(N\) の同じ定理24のデータと定理26の力学を、一般の入口へ渡します。**全非負の初期対**について、(1) 全ての真部分層の正の価値、(2) 頂点の PZS の分類（PZS \(\iff\) 零価値目標に入る）、(3) 速さつきの距離・評価（\(W\le W_0e^{-\text{rate}(s-T)}\)、目標までの距離 \(\le\sqrt{W_0/c_1}\,e^{-\text{rate}(s-T)/2}\)）、(4) 最適値の極限（0 に収束）、(5) 零評価の目標の同値と不変性、をまとめて得ます。

### 証明の概略

1. 定理24→26 の一般の入口（`theorem24_to26_from_nonnegativeTimeData`）に `N.data`・`N.dynamics` を渡す。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.theorem15_23"></a>

## 定理 `SharedKernelInputs.theorem15_23`

### 式

$$
t_1<t_2\Rightarrow N.\mathrm{path}(t_2)\ne N.\mathrm{path}(t_1)
$$

### Lean のコメント（日本語訳）

> 同じNの完全状態pathへ15→23の一般入口を適用する。

### 補題の説明

同じ \(N\) の完全状態の軌道に、定理15→23 の一般の入口を適用します（非再訪）。

### 証明の概略

1. 共有署名のエントロピーの入力の非再訪（`SharedEntropyInputs.nonrecurrence`）。

----

<a id="Tomabechi.Consistency.R123.runningCost_cast"></a>

## 補題 `runningCost_cast`

### 式

$$
\text{走行費に対して cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

添字の等式に沿った型の変換（cast）で、走行費の値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.finite_cost_eq_base"></a>

## 補題 `SharedKernelInputs.finite_cost_eq_base`

### 式

$$
\text{有限層の費用}=\text{基礎評価（箱の中）}
$$

### Lean のコメント（日本語訳）

> Nの有限層24費用とNに一度だけ格納した基礎評価の一致。箱内状態と同じ有限層で述べ、頂点への数値baselineの一致を要求しない。

### 補題の説明

\(N\) の有限層の定理24の費用と、\(N\) に**一度だけ**格納した基礎評価が、一致します。箱の中の状態について、同じ有限層で述べ、頂点への数値の基準値の一致は要求しません。

### 証明の概略

1. 共通束上のデータの走行費を、以前の署名のデータの走行費に書き換える（保存式と cast の補題）。
2. 有限層の走行費は \(V_0\)（`c6LayeredFiniteRunningCost_eq_C1V0`）。基礎評価の契約（`theorem1_matches`）で一致。

----

<a id="Tomabechi.Consistency.R123.sharedModel_kernelInputs"></a>

## 定理 `sharedModel_kernelInputs`

### 式

$$
\mathrm{SharedKernelInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 外部モデル前提なしで、現在接続した解析入口を同じ署名に供給する。

### 補題の説明

外部のモデルの前提なしで、現在接続した解析の入口を、同じ署名に供給します。

### 証明の概略

1. 各フィールドに、これまでの定理（`commonModel_originalPremises`・`commonModel_additionalConditions`・`commonModel_nondegenerate`・`sharedModel_preservation`・`sharedModel_entropyInputs`）と、SCM の出力が履歴であること、候補の正の質量、一点の TCZ・距離（R2 の補題）を入れる。

----

<a id="Tomabechi.Consistency.R123.shared_kernel_model_exists"></a>

## 定理 `shared_kernel_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedKernelInputs}(N)
$$

### Lean のコメント（日本語訳）

> 共有データと接続済み解析入力の同時存在。FullOriginalPremisesの最終認定は残る原文条件の照合後に行う。

### 補題の説明

共有データと、接続済みの解析入力の**同時の存在**です。`FullOriginalPremises` の最終的な認定は、残る原文の条件の照合のあとに行います。

### 証明の概略

1. `sharedModel` と前の定理。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
