# Theorem15_23.lean 解説

> 対象: [`Theorem15_23.lean`](../Theorem15_23.lean)（定理15(I) から定理23第1部（非再帰）への接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| Vitali の収束定理 | 一様可積分かつ a.e. 収束するなら \(L^1\) 収束する。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理15(I)（エントロピー収支の積分形、`Theorem15.lean`）を、定理23の第 1 部（**完全状態は繰り返さない**）に**接続**する小さなファイルです。

各生存区間 \([a,b]\) で定理15の仮定（A2/A5/A6′/A7）が成り立てば、積分収支 \(S_{\text{gen}}(b)-S_{\text{gen}}(a)=\int_a^b\Pi\) が得られます。ここに**条件 23-A**（生存区間で総生成率の積分が厳密に正）を加えると、エントロピーが厳密に増えるので、完全状態は再び同じにならない（非再帰）、という結論になります。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `theorem15_first_part_implies_theorem23_nonrecurrence` | 可算層（列挙を呼び出し側が与える）の場合 |
| `theorem15_finite_layer_implies_theorem23_nonrecurrence` | 有限層の場合（列挙も Vitali も不要） |
| `countableLayerEnumeration` | 可算無限の層の型に、内部で列挙 \(\mathbb N\simeq\text{Layer}\) を選ぶ |
| `theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence` | 可算無限の層：列挙を呼び出し側が与えなくてよい版 |

### 0.3 このファイルが証明していないこと

- **条件 23-A（各区間の総生成量が厳密に正）は、定理15の非負性からは導かれません**。独立した条件として仮定します（ファイル冒頭のコメントのとおり）。「定理15の非負の生成から厳密散逸を導いた」とは主張しません。
- A7 と A6′ は、論文の独立した仮定のまま、入力として与えます。
- エントロピーが一価に定まる「完全状態」という解釈上の前提は `EntropyBalance.lean` と同じです。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理15(I) から定理23の第 1 部への接続**
>
> 定理15(I) の一般化エントロピーの収支を、各生存区間に適用し、定理23の条件 23-A（各区間の総生成量が厳密に正）と合わせて、完全状態の非再帰性を得る。23-A の厳密な正値性は、定理15の非負性からは導かれないため、独立の条件として残す。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem15_23`。`open Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem15_23.theorem15_first_part_implies_theorem23_nonrecurrence"></a>

## 定理 `theorem15_first_part_implies_theorem23_nonrecurrence`

### 式

$$\text{各生存区間で A2/A5/A6′/A7}\ +\ \text{23-A}\ \Longrightarrow\ \forall t_1<t_2\ (\text{alive}),\ \text{state}(t_2)\neq\text{state}(t_1)$$

### Lean のコメント（日本語訳）

> 各生存区間で定理15(I) の A2/A5/A6′/A7 の条件が成り立てば、積分収支が得られる。さらに、定理23-A の厳密散逸の条件から、完全状態は生存区間の中で再帰しない。A7 と A6′ は、論文の独立した仮定のまま入力する。定理15の非負の生成から、厳密散逸を導いたとは主張しない。

### 補題の説明

**定理15 → 定理23第 1 部**：各区間で定理15の積分収支を得て、23-A（積分が正）と合わせると、状態は繰り返しません。

### 証明の概略

1. 各区間 \([a,b]\) で `theorem15_trajectory_integral_balance`（Theorem15）を各区間 \([a,b]\) に適用して、積分収支を得る。
2. `complete_state_never_repeats_of_strict_entropy_balance`（EntropyBalance）に、収支と 23-A を渡す（21 行）。

----

<a id="Tomabechi.Theorem15_23.theorem15_finite_layer_implies_theorem23_nonrecurrence"></a>

## 定理 `theorem15_finite_layer_implies_theorem23_nonrecurrence`

### 式

$$\text{有限層}:\ \text{同様の結論}$$

### Lean のコメント（日本語訳）

> 有限個の認知層では、列挙 `ℕ ≃ Layer` や可算の Vitali の極限を使わず、定理15(I) の有限層の収支を各生存区間に適用して、定理23の第 1 部に接続する。厳密な正値性は、23-A として独立に仮定する。

### 補題の説明

上の定理の有限層版です（列挙・A6′ が不要）。

### 証明の概略

1. `theorem15_finite_layer_integral_balance`（Theorem15）で収支。
2. `complete_state_never_repeats_of_strict_entropy_balance` を適用（15 行）。

----

<a id="Tomabechi.Theorem15_23.countableLayerEnumeration"></a>

## 定義 `countableLayerEnumeration`

### 式

$$e:\mathbb N\simeq\text{Layer}\quad(\text{Layer は可算無限})$$

### Lean のコメント（日本語訳）

> 可算無限の層の型は、`ℕ` による内部の列挙をもつ。この古典的な選択は実装上の道具であり、以下の定理のインターフェースは、利用者に同値を構成させたり渡させたりしない。

### 定義の説明

可算無限な集合は自然数と一対一に対応します。その対応を（選択公理で）1 つ選んだものです。

### 証明の概略

1. 定義：`Classical.choice (nonempty_equiv_of_countable ...)`。

----

<a id="Tomabechi.Theorem15_23.theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence"></a>

## 定理 `theorem15_countably_infinite_layers_imply_theorem23_nonrecurrence`

### 式

$$\text{可算無限の層}\ (\text{列挙は内部で選ぶ})\ \Longrightarrow\ \text{非再帰}$$

### Lean のコメント（日本語訳）

> 可算無限個の層では、呼び出し側が与える列挙は要らない。A6′ の prefix の極限の前提は、内部の列挙について述べられ、一方、点ごとのエントロピーの総和可能性と、有限部分集合についての一様可積分性は、区間に局所的なままである。

### 補題の説明

列挙を引数にしない版です。内部の列挙 `countableLayerEnumeration` を使って、第 1 の定理を適用します。

### 証明の概略

1. `countableLayerEnumeration` で列挙を作り、`theorem15_first_part_implies_theorem23_nonrecurrence` を適用（13 行）。

----


## コメント修正記録

（なし）
