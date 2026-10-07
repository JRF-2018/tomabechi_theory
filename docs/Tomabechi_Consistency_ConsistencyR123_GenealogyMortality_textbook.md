# Tomabechi/Consistency/ConsistencyR123_GenealogyMortality.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_GenealogyMortality.lean`](../Tomabechi/Consistency/ConsistencyR123_GenealogyMortality.lean)（25-C4（父母子）と 25-C5（死後の上位履歴層の表象）を N に接続した拡張）。
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

原文 §14 の (25.C4)（父母子）と (25.C5)（死後の上位履歴層の表象）を、\(N\) に接続した**拡張**です。(25.C4)・(25.C5) は、「簡約した生物学的系譜モデルでは」「完全履歴が過去の身体的存在の因果履歴を保持する本モデルでは」と書くモデルの例で、定理 25 の結論の前提ではありません。\(N\) の主体は `Bool` の二つで、出生・死亡を持たないので、\(N\) だけでは \(\mathfrak D_{\mathrm{born}}=\emptyset\) で空虚に成立していました。

ここでは、\(N\) を**変えずに**、系譜と死亡の補助データを加えた拡張 `GenealogyMortalityExtension N` を作ります。\(N\) 自身の述語（第 2 版の全受入の型）は、\(N\) のフィールドだけを読むので、拡張を加えても、そのまま保たれます。

* **人物：** 六人の系譜の例 `Person`（祖父 0・父 1・母 2・子 3・叔母 4・祖母 5）。\(N\) の二つの主体は、`embed : Bool → Person`（false ↦ 父、true ↦ 子）で人物に埋め込みます。
* **(25.C4)：** `GenealogyC4`（逆役割、\(\mathfrak D_{\mathrm{born}}=\{\text{子}\}\) 非空で父母がいる）。さらに、\(N\) の関係辺が、埋め込んだ父・子の間に実在します。
* **(25.C5)：** 祖父は時刻 1、祖母は時刻 2 に死亡し、他は死にません。`AliveRealization0 d t := t < τ_d`。死亡時刻以降は `AliveRealization0` が偽で、かつ \(0\prec\alpha_{\rm hist}\prec\top\) の層 `diagonalLayer 1` で、表象（現前の profile）は境界 \(\partial=\) `none` でありません。

### 0.2 このファイルが証明していないこと

* 死亡時刻・人物の profile は、補助データとして**構成したモデルの選択**であり、\(N\) の力学から導かれたものではありません（\(N\) の軌道は \(\mathcal B_{\rm alive}\) の中に留まり、\(N\) 自身には死亡がない）。
* (25.C4)/(25.C5) を、\(N\) の SCM・自己過程の保存式へ組み込んだのではなく、\(N\) を変えない拡張です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §14 の (25.C4)・(25.C5) は「簡約した生物学的系譜モデルでは」「完全履歴が過去の身体的存在の因果履歴を保持する本モデルでは」と書くモデル例で、定理25の結論の前提ではない。N の主体は Bool の二つで、出生・死亡を持たないので、N だけでは 𝔇born=∅ で空虚に成立していた。ここでは N を変えずに、系譜と死亡の補助データを加えた拡張 GenealogyMortalityExtension N を作る。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.embedPerson"></a>

## 定義 `embedPerson`

### 式

$$
\mathrm{false}\mapsto\text{父}(1),\ \mathrm{true}\mapsto\text{子}(3)
$$

### Lean のコメント（日本語訳）

> Nの二主体の人物への埋め込み：false ↦ 父(1)、true ↦ 子(3)。

### 定義の説明

\(N\) の二つの主体の、人物への埋め込みです。`false` は父（1）、`true` は子（3）に送ります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.deathTime"></a>

## 定義 `deathTime`

### 式

$$
\tau_0=1,\ \tau_5=2,\ \text{他は}\ \infty
$$

### Lean のコメント（日本語訳）

> 死亡時刻：祖父(0)は1、祖母(5)は2、他は死なない。

### 定義の説明

死亡の時刻です。祖父（0）は 1、祖母（5）は 2、他は死にません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.AliveRealization0"></a>

## 定義 `AliveRealization0`

### 式

$$
\mathrm{Alive}(d,t)\iff t<\tau_d
$$

### Lean のコメント（日本語訳）

> 物理層における生きた自己制御過程の直接実装の有無。

### 定義の説明

物理層における、**生きた自己制御の過程の直接の実装**の有無です。時刻が死亡時刻より前であること。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.personProfile"></a>

## 定義 `personProfile`

### 式

$$
\text{profile}\equiv\mathrm{some}()
$$

### Lean のコメント（日本語訳）

> 人物・履歴・層の表象（presenceのprofileと同じ形。noneが境界∂に当たる）。

### 定義の説明

人物・履歴・層の表象です（現前の profile と同じ形。`none` が境界 \(\partial\) に当たります）。ここでは常に `some ()` です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.GenealogyMortalityExtension"></a>

## 構造体 `GenealogyMortalityExtension`

### 式

$$
\text{(25.C4)}\wedge\text{(25.C5)}\wedge\text{N の関係辺が系譜に実在}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

系譜と死亡の補助データを加えた、\(N\) の拡張です。フィールドは、(25.C4)（逆役割、\(\mathfrak D_{\mathrm{born}}=\{\text{子}\}\) 非空で父母がいる）、生まれた存在が空でない、(25.C5)（死亡時刻以降は `AliveRealization0` が偽で、\(0\prec\alpha_{\rm hist}\prec\top\) の層で、表象が境界 \(\partial\) でない）、死亡が実際に起きる、人物の profile が \(N\) の profile と同じ形で、\(N\) の二主体では一致する（`profile_agree`）、\(N\) の関係辺が、埋め込んだ父・子の間に実在する（`edge_realizes_genealogy`）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_genealogyMortality"></a>

## 定理 `sharedModel_genealogyMortality`

### 式

$$
\mathrm{GenealogyMortalityExtension}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルに、系譜と死亡の拡張が成り立ちます。

### 証明の概略

1. (25.C4)：逆向きの対応は `Iff.rfl`、生まれた存在（子）に父母がいること（`child_has_father_and_mother`）。
2. (25.C5)：死亡時刻以降は `AliveRealization0` が偽。層 `diagonalLayer 1` が \(\bot\) と \(\top\) の間にあること（`diagonalLayer_strictMono`・`diagonalLayer_lt_top`）と、profile が `some ()` であること。
3. 他のフィールドは具体的な計算。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v2_with_genealogy_mortality"></a>

## 定理 `final_consistency_v2_with_genealogy_mortality`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{GenealogyMortalityExtension}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

存在宣言に、系譜と死亡の拡張を加えた版です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
