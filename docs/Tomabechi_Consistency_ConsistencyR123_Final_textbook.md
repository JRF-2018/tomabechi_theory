# Tomabechi/Consistency/ConsistencyR123_Final.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_Final.lean`](../Tomabechi/Consistency/ConsistencyR123_Final.lean)（共有モデル `N` についての、最初の最終存在宣言）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

「原文の前提」「追加の明示条件」「非退化性」の三つを、**一つの共有モデル `N` が同時に満たす**ことを、一つの定理として述べるファイルです。無矛盾性の主張の骨格は、ここにあります。後の版（v13・v14）は、このファイルの宣言に、さらに補完を重ねたものです（[見取り図](Consistency_Overview.md)）。

三つの部品は次のとおりです。

| 部品 | 意味 |
| --- | --- |
| `FullOriginalPremises N` | 原文の前提。以前の署名の原文入力と、同じ `N` の実データを各定理の一般入口に渡すための全入力。 |
| `ExplicitAdditionalConditions N` | 追加の明示条件。以前の署名の追加条件、共有の保存式、層の添字が順序と頂を保つこと。 |
| `SharedNondegenerate N` | 非退化性（[解説](Tomabechi_Consistency_ConsistencyR123_Nondegenerate_textbook.md)）。 |

### 0.2 このファイルが証明していないこと

* 原文の前提**だけ**から定理が従うこと、すべてのモデルで成り立つことは主張しません。追加条件を許した**一つの**非退化な共有モデルの存在です。
* 頂点では二値の作用の符号が、時刻0・参照状態での観測であること。
* 定理3は零平均の箱の点に限ること。
* 定理20の二次式への拡張は箱の内側に限ること。
* 一点 K は、各箱の初期点からの閉到達集合であること。

これらの範囲は、各入力型の定義に従います。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 共通完備束 `CommonConcept` を添字とする `SharedModelSignature N` について、
> * `FullOriginalPremises N`：原文の全層解析入力（旧署名の `OriginalPremises`）と、同じ N の実データを一般入口へ渡す全入力（15→23、21/22/23-B、24→26、25、27、一点初期状態 K からの 1/2/3/4/20・全域誤差・再始動、全 CommonConcept 点の情報実験）
> * `ExplicitAdditionalConditions N`：旧署名の `AdditionalConditions`、共有保存式 `SharedDataPreservation N`、および層添字埋込みが順序・頂を保つこと
> * `SharedNondegenerate N`：N の実 field を読む N1–N7
>
> を同時に満たす N が外部モデル前提なしに存在することを述べる。これは追加条件を許容した一つの非退化共有モデルの存在であり、原文の前提だけから定理が従うこと、全モデルで成立することは主張しない。（以下、頂点・定理3・定理20・一点 K の量化範囲は各入力型に従う、という注意が続く。）

---

<a id="Tomabechi.Consistency.R123.FullOriginalPremises"></a>

## 構造体 `FullOriginalPremises`

### 式

$$
\mathrm{FullOriginalPremises}(N) \;=\; \mathrm{OriginalPremises}(N^{\text{旧}}) \ \wedge\ \mathrm{SharedPointDomainInputs}(N)
$$

### Lean のコメント（日本語訳）

> 原文の全入口前提。旧署名の原文入力と、同じ N の全一般入口入力。

### 定義の説明

原文の前提を二つの面から述べます。

* `legacy`：以前の署名の原文入力（各層の解析的な前提）。
* `inputs`：同じ `N` の実データから、各定理（15→23、21・22・23-B、24→26、25、27、1–4・20、情報実験）の一般入口に渡す入力をすべてそろえたもの。

つまり「前提を満たす」とは、前提を述べる**型**を満たすだけでなく、**同じ `N`** から一般定理の入口に実際に渡せることです。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.ExplicitAdditionalConditions"></a>

## 構造体 `ExplicitAdditionalConditions`

### 式

$$
\mathrm{AdditionalConditions}(N^{\text{旧}}) \ \wedge\ \mathrm{SharedDataPreservation}(N) \ \wedge\ \bigl(a\le b \iff \iota(a)\le\iota(b)\bigr)\ \wedge\ \iota(\top)=\top
$$

（\(\iota\) は層の添字 \(\mathbb N\cup\{\top\}\) から共通束への埋め込み）

### Lean のコメント（日本語訳）

> 明示的な追加条件。旧署名の追加条件、共有保存式、共通束への層添字の順序・頂保存。

### 定義の説明

追加の明示条件（H-info・H-flow・H-sum・H-stage、[Additional_Assumptions.md](Additional_Assumptions.md)）に加えて、次の二つを要求します。

* **共有保存式**：共有モデルのデータが、以前の署名のデータと座標の読み替えで一致すること。
* **層の添字の埋め込み**：自然数に頂（`⊤`）を加えた層の番号を共通束に埋め込む写像が、順序を保ち（`layer_order`）、頂を頂に送る（`layer_top`）こと。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.FinalConsistency"></a>

## 構造体 `FinalConsistency`

### 式

$$
\mathrm{FinalConsistency}(N)\ =\ \text{原文の前提}\ \wedge\ \text{追加条件}\ \wedge\ \text{非退化性}
$$

### Lean のコメント（日本語訳）

> 原文前提・明示追加条件・非退化性の同時充足。

### 定義の説明

三つの部品を一つにまとめた述語です。以下の存在定理を述べるときの「述語を一つの名前で呼ぶ」ための定義です。

### 証明の概略

構造体の定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_fullOriginalPremises"></a>

## 定理 `sharedModel_fullOriginalPremises`

### 式

$$
\mathrm{FullOriginalPremises}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的に構成した共有モデル `sharedModel` が、原文の前提を満たすことです。

### 証明の概略

1. 以前の署名の原文入力は `commonModel_originalPremises`。
2. 同じ `N` の一般入口の入力は `sharedModel_pointDomainInputs`。
3. この二つを組にする。

----

<a id="Tomabechi.Consistency.R123.sharedModel_explicitAdditionalConditions"></a>

## 定理 `sharedModel_explicitAdditionalConditions`

### 式

$$
\mathrm{ExplicitAdditionalConditions}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`sharedModel` が追加の明示条件を満たすことです。

### 証明の概略

1. 以前の署名の追加条件は `commonModel_additionalConditions`、共有保存式は `sharedModel_preservation`。
2. 層の添字の順序の保存は、埋め込み `layerAddressEmbedding` の順序同型の性質（`le_iff_le`）から。
3. 頂の保存は `layerAddress_top`。

----

<a id="Tomabechi.Consistency.R123.final_consistency_model_exists"></a>

## 定理 `final_consistency_model_exists`

### 式

$$
\exists N,\ \ \mathrm{FullOriginalPremises}(N)\ \wedge\ \mathrm{ExplicitAdditionalConditions}(N)\ \wedge\ \mathrm{SharedNondegenerate}(N)
$$

### Lean のコメント（日本語訳）

> 最終存在宣言。外部のモデル前提を含まない。

### 補題の説明

**無矛盾性の主張の最初の完成形**です。原文の前提・追加の明示条件・非退化性を同時に満たす共有モデルが存在します。「外部のモデル前提を含まない」とは、`N` の存在を仮定せず、`sharedModel` という具体的なモデルを Lean の中で構成していることです。

### 証明の概略

1. `sharedModel` を `N` として取る。
2. 三つの部品は、それぞれ `sharedModel_fullOriginalPremises`・`sharedModel_explicitAdditionalConditions`・`sharedModel_nondegenerate`。

----

<a id="Tomabechi.Consistency.R123.final_consistency_record"></a>

## 定理 `final_consistency_record`

### 式

$$
\exists N,\ \mathrm{FinalConsistency}(N)
$$

### Lean のコメント（日本語訳）

> 同じ内容を一つの record として述べた版。

### 補題の説明

前の定理と同じ内容を、構造体 `FinalConsistency` で述べ直したものです。

### 証明の概略

1. `sharedModel` を取り、前の定理の三つの部品を `FinalConsistency` の三つのフィールドに入れる。

----

## コメント修正記録

`final_consistency_model_exists` の docstring から、作業の段階を示す番号（「§14の」）を削除しました（コメントのみ）。
