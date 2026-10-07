# Tomabechi/Consistency/ConsistencyR123_ModelExamples.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_ModelExamples.lean`](../Tomabechi/Consistency/ConsistencyR123_ModelExamples.lean)（25-C4（父母子の逆役割）の非空実例）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

原文 §14 の (25.C4)（父・母・子の**逆役割**）が、**空でない集合 \(\mathfrak D_{\mathrm{born}}\)** で成り立つ具体例を示すファイルです。(25.C4) は、「簡約した生物学的系譜モデルでは…と表せる」というモデルの例で、定理 25 の結論の前提ではありません。共有モデル \(N\) の主体は `Bool` の二つで、父・母・子の役割や出生をもつ存在 \(\mathfrak D_{\mathrm{born}}\) を持たないため、\(N\) では (25.C4) は \(\mathfrak D_{\mathrm{born}}=\emptyset\) により**空虚に**成り立ちます。

ここでは、(25.C4) の式を述語 `GenealogyC4` として書き下し、既存の六人の系譜の例（子 3 に父 1・母 2）が、\(\mathfrak D_{\mathrm{born}}\) が**空でない**まま満たすことを示します。

### 0.2 このファイルが証明していないこと

* これは \(N\) とは**別の小さな有限モデル**です。\(N\) の SCM・自己過程などの受入の型を拡張して、父・母・子を載せたものではありません。
* (25.C5)（死後の上位履歴層の表象）は、死亡時刻・`AliveRealization0`・境界値 \(\partial\alpha\) が Lean のモデルに存在せず、定義を新しく選ぶ必要があるので、ここでは扱いません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §14 の (25.C4) は「簡約した生物学的系譜モデルでは…と表せる」というモデル例で、定理25の結論の前提ではない。共有モデル N の主体は Bool の二つで、父・母・子の役割や出生をもつ存在 𝔇born を持たないため、N では (25.C4) は 𝔇born=∅ により空虚に成立する。ここでは (25.C4) の式を述語 GenealogyC4 として書き下し、既存の六人の系譜例（Tomabechi.Examples.Theorem25、子 3 に父 1・母 2）が 𝔇born が非空のまま満たすことを示す。範囲：これは N とは別の小さな有限モデルである。…(25.C5) は…ここでは扱わない（対応表に「対象外」と記録）。

---

<a id="Tomabechi.Consistency.R123.GenealogyC4"></a>

## 構造体 `GenealogyC4`

### 式

$$
\text{父・母の関係は逆向きの記述で、}\mathfrak D_{\mathrm{born}}\text{ の各存在に父と母がいる}
$$

### Lean のコメント（日本語訳）

> (25.C4)：履歴h∈ℋgeneで、FatherOf/HasFather・MotherOf/HasMotherは同一関係の逆向き記述で、𝔇bornの各存在に父と母がいる。

### 定義の説明

(25.C4) です。履歴 \(h\in\mathcal H_{\mathrm{gene}}\) で、`FatherOf`/`HasFather`・`MotherOf`/`HasMother` は**同一の関係の逆向きの記述**で、\(\mathfrak D_{\mathrm{born}}\) の各存在に父と母がいる、という条件です。フィールドは、父の逆向きの対応、母の逆向きの対応、生まれた各存在に父母がいること、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.HasMotherExample"></a>

## 定義 `HasMotherExample`

### 式

$$
\mathrm{HasMother}(c,m)\iff\mathrm{MotherOf}(m,c)
$$

### Lean のコメント（日本語訳）

> 六人の系譜例のHasMother c m⇔MotherOf m c（既存例はHasFatherだけを定義している）。

### 定義の説明

六人の系譜例の `HasMother c m ⇔ MotherOf m c` です（既存の例は `HasFather` だけを定義しています）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.genealogyC4_example"></a>

## 補題 `genealogyC4_example`

### 式

$$
\mathrm{GenealogyC4}(\{3\},\ \ldots)
$$

### Lean のコメント（日本語訳）

> 六人の系譜例（履歴は一つ）：𝔇born={子}（非空）で(25.C4)を満たす。

### 補題の説明

六人の系譜の例（履歴は一つ）で、\(\mathfrak D_{\mathrm{born}}=\{\text{子}\}\)（**空でない**）のまま、(25.C4) を満たします。

### 証明の概略

1. 逆向きの対応は、定義から `Iff.rfl`。
2. 生まれた存在（子 3）に、父 1・母 2 がいる（具体例）。

----

<a id="Tomabechi.Consistency.R123.genealogyC4_example_born_nonempty"></a>

## 補題 `genealogyC4_example_born_nonempty`

### 式

$$
\{3\}\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

生まれた存在の集合 \(\{3\}\) は空でないです。

### 証明の概略

1. 要素 3。

----


## コメント修正記録

末尾の「対応表に『対象外』と記録」は、この解説書では前提の対応表（[Consistency_Premises_Table.md](Consistency_Premises_Table.md)）への言及と読んでください。
