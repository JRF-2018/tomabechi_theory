# Tomabechi/Consistency/ConsistencyR123_SelfProcessOnePoint.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SelfProcessOnePoint.lean`](../Tomabechi/Consistency/ConsistencyR123_SelfProcessOnePoint.lean)（定理25の型付き自己過程を、一点初期状態の定理16担体で読む）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 25 の型つき自己過程を、一点の初期状態の定理 16 の担体で読む**ファイルです。`Shared16OnePointInputs`（一点 \(x_0\) からの閉到達スライスを担体とする、定理 16 の層系）は、旧来の自己表象 `N.legacy.selfRepresentation`（TCZ は初期集合 \([0,1]\) からの到達集合）とは別に置かれていました。定理 25 の自己過程 \(R_i[h]=(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ})\) は、定理 16 の主体の TCZ をその成分にもちます（原文 §14 の 25.1、§2.4）。そこで、**TCZ の成分だけを一点版の層別 TCZ に取り替えた**型つき自己過程を、同じ `N.scm` から作り、条件 25-A(2) が同じ証明で成り立つことを示します。Self・Ego は旧い表象のものを使い、Ego は、一点版のフィードバック（時刻 1 の勾配流）の拡張になっていることも述べます。

あわせて、定理 21 の \(V_0\) の実例を、段と同じ**共通束の枝**で適用します。

### 0.2 このファイルが証明していないこと

* 自己過程の TCZ 成分は、一点版の担体（全層で同じ線分）です。層ごとに別々の担体を再構成したのではありません。
* 定理 21 の実例は、前のファイルと同じ具体的な値の一つです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> Shared16OnePointInputs（一点 x₀ からの閉到達スライスを担体とする定理16の層系）は、旧来の自己表象 N.legacy.selfRepresentation（TCZ は初期集合 [0,1] からの到達集合）とは別に置かれていた。定理25の自己過程 R_i[h]=(Self,Ego,TCZ) は、定理16の主体の TCZ をその成分にもつ（原文 §14 25.1、§2.4）。そこで、TCZ 成分だけを一点版の層別 TCZ N.layerTCZ1 h i に取り替えた型付き自己過程を同じ N.scm から作り、条件25-A(2) が同じ証明で成り立つことを示す。Self・Ego は旧表象のものを使い、Ego は一点版のフィードバック（時刻1の勾配流）の拡張になっていることも述べる。

---

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfRepOnePoint"></a>

## 定義 `SharedModelSignature.selfRepOnePoint`

### 式

$$
(\mathrm{Self},\mathrm{Ego},\mathrm{TCZ}_1)
$$

### Lean のコメント（日本語訳）

> TCZ成分を一点版の層別TCZに取り替えた三表現。

### 定義の説明

TCZ の成分を、一点版の層別 TCZ に取り替えた、**三つの表現**です。Self・Ego は旧い表象のものを使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationOnePoint"></a>

## 定義 `SharedModelSignature.typedObservationOnePoint`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ の }\Gamma\text{ と出力に、一点版の三表現を付加する観測}
$$

### Lean のコメント（日本語訳）

> 同じN.scmのΓと出力に、一点版の三表現を付加する観測。

### 定義の説明

同じ `N.scm` の \(\Gamma\) と出力に、一点版の三表現を付加する観測です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.typedObservationOnePoint_measurable"></a>

## 補題 `SharedModelSignature.typedObservationOnePoint_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この観測は可測です。

### 証明の概略

1. 三表現は有限個の値しか取らない（`measurable_of_finite`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.selfProcessOnePoint"></a>

## 定義 `SharedModelSignature.selfProcessOnePoint`

### 式

$$
\text{同じ }N.\mathrm{scm}\text{ から生成する、一点版の型付き自己過程}
$$

### Lean のコメント（日本語訳）

> 同じN.scmから生成する、一点版の型付き自己過程。

### 定義の説明

同じ `N.scm` から生成する、**一点版の型つき自己過程**です。外生の法則・履歴・候補の変数は同じ `N.scm` のもので、観測だけを一点版にします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedKernelInputs.selfProcessOnePoint25A2"></a>

## 補題 `SharedKernelInputs.selfProcessOnePoint25A2`

### 式

$$
\text{条件 25-A(2) は全主体・全共通束点で成り立つ}
$$

### Lean のコメント（日本語訳）

> 一点版の自己過程でも、条件25-A(2)は全主体・全共通束点で成り立つ。

### 補題の説明

一点版の自己過程でも、条件 25-A(2) は、**全主体・全共通束点**で成り立ちます。

### 証明の概略

1. 25-A(2) の一般の補題 `condition25A2` を適用する。候補が大域の文脈と独立であること（`candidateIndependentOfGlobalContext`）と、介入の等式を、同じ証明で示す。

----

<a id="Tomabechi.Consistency.R123.v0Stage_theorem21_common"></a>

## 定義 `v0Stage_theorem21_common`

### 式

$$
\text{定理21の }V_0\text{ 実例を、共通束の枝で適用}
$$

### Lean のコメント（日本語訳）

> 定理21のV₀実例を、段と同じ共通束CommonConceptの枝（sharedStageBranch 0）で適用する。旧v0Stage_theorem21はWithTop ℕの原子束の枝を使っていた。ここでは表象を順序埋込みlayerAddressEmbeddingで共通束へ送り、𝕃_i⊊𝕃・⊤∉𝕃_i・b=∨supp μを共通束で満たす。

### 定義の説明

定理 21 の \(V_0\) の実例を、段と同じ共通束 `CommonConcept` の枝（`sharedStageBranch 0`）で適用します。旧い `v0Stage_theorem21` は、`WithTop ℕ` の原子束の枝を使っていました。ここでは、表象を順序埋め込み `layerAddressEmbedding` で共通束へ送り、\(\mathbb L_i\subsetneq\mathbb L\)・\(\top\notin\mathbb L_i\)・\(b=\bigvee\mathrm{supp}\,\mu\) を、共通束で満たします。

### 証明の概略

1. 一般の入口を、共通束の枝・段 0 のアドレス・情報の部分で適用する。

----

<a id="Tomabechi.Consistency.R123.V0StageConclusionCommon"></a>

## 定義 `V0StageConclusionCommon`

### 式

$$
\text{共通束版の実例の結論（四結論）の命題}
$$

### Lean のコメント（日本語訳）

> 共通束版の実例の結論（定理21の四結論）の命題。

### 定義の説明

共通束版の実例の結論（定理 21 の四結論）の命題です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.v0Stage_theorem21_common_holds"></a>

## 定理 `v0Stage_theorem21_common_holds`

### 式

$$
\mathrm{V0StageConclusionCommon}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束版の実例の結論が成り立ちます。

### 証明の概略

1. `v0Stage_theorem21_common`。

----

<a id="Tomabechi.Consistency.R123.SharedTheorem21V0Common"></a>

## 構造体 `SharedTheorem21V0Common`

### 式

$$
\text{枝は段 0 と同じ共通束の住所}\wedge\text{四結論}
$$

### Lean のコメント（日本語訳）

> 定理21のV₀実例を共通束の枝で述べた受入型。枝は段0と同じ共通束の住所。

### 定義の説明

定理 21 の \(V_0\) の実例を、共通束の枝で述べた受入の型です。フィールドは、先の `SharedTheorem21V0`、枝が段 0 と同じ共通束の住所、結論、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.sharedTheorem21V0Common"></a>

## 定理 `SharedModelSignature.sharedTheorem21V0Common`

### 式

$$
\mathrm{SharedTheorem21V0Common}(N)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

単独の実例と、段の切り替えの入力から、共通束版の実例が従います。

### 証明の概略

1. 枝のアドレスは、段の切り替えの入力（`hsw.address`）から。結論は `v0Stage_theorem21_common_holds`。

----

<a id="Tomabechi.Consistency.R123.Shared25OnePointSelf"></a>

## 構造体 `Shared25OnePointSelf`

### 式

$$
\text{25 の自己過程の TCZ 成分}=\text{一点版の 16 の担体}
$$

### Lean のコメント（日本語訳）

> 定理25の自己過程のTCZ成分が、一点版の定理16担体と同じ対象であることの受入型。

### 定義の説明

定理 25 の自己過程の TCZ の成分が、**一点版の定理 16 の担体と同じ対象**であることの受入の型です。フィールドは、(1) 条件 25-A(2)：一点版の型つき自己過程で、候補・追加の自我への介入が法則を変えない、(2) 自己過程の TCZ 成分は、一点版の定理 16 の層系の担体そのもの、(3) TCZ 成分は線分で、二履歴で異なる、(4) Ego は、一点版のフィードバック（時刻 1 の勾配流）を担体の上で拡張する、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.shared25OnePointSelf"></a>

## 定理 `SharedModelSignature.shared25OnePointSelf`

### 式

$$
\mathrm{Shared25OnePointSelf}(N)
$$

### Lean のコメント（日本語訳）

> 最終受入型の部品から、一点版の自己過程の受入型を任意のNで得る。

### 補題の説明

最終の受入の型の部品から、一点版の自己過程の受入の型を、**任意の \(N\)** で得ます。

### 証明の概略

1. 25-A(2) は `selfProcessOnePoint25A2`。TCZ 成分の等式は、一点版の入力（`carrier_eq`・`tcz_eq`）から。二履歴で異なることは、一点版の層別 TCZ の補題から。

----

<a id="Tomabechi.Consistency.R123.sharedModel_shared25OnePointSelf"></a>

## 定理 `sharedModel_shared25OnePointSelf`

### 式

$$
\mathrm{Shared25OnePointSelf}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、一点版の自己過程の受入の型を満たします。

### 証明の概略

1. 前の定理を、`sharedModel_kernelInputs` と `sharedModel_shared16OnePointInputs` に適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_v5"></a>

## 定理 `final_consistency_v5`

### 式

$$
\exists N,\ \cdots\wedge\mathrm{Shared25OnePointSelf}(N)\wedge\mathrm{SharedTheorem21V0Common}(N)
$$

### Lean のコメント（日本語訳）

> v4の全受入型に、一点版の定理16担体をTCZ成分にもつ定理25の自己過程を加えた存在宣言。

### 補題の説明

第 5 版です。第 4 版の全受入の型に、一点版の定理 16 の担体を TCZ 成分にもつ定理 25 の自己過程を加えた存在宣言です。

### 証明の概略

1. 存在宣言です。部品は `sharedModel` と、これまでの各部品の定理です。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
