# Tomabechi/Consistency/ConsistencyR123_PolicyCapacity.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_PolicyCapacity.lean`](../Tomabechi/Consistency/ConsistencyR123_PolicyCapacity.lean)（定理19の容量を「問題 × 方策」の上限として）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理 19 の容量を、「問題 × 方策」の上限として**述べ直すファイルです。原文の §8 は \(\mathcal F_i(\alpha)=\sup_{(d,\pi)\in\mathfrak c_{i,\alpha}}I(G_d;Y_d^\pi\mid X_d)\) と、**問題 \(d\) と方策 \(\pi\) の組**の上限を取ります。`fixedCapacity` の問題は、方策の添字を持たず、固定した一つの `fullInformationDecoder` に委譲していました。`decode c false`／`decode c true` は、その一つの復号が出す**二つの実制御の方策**であって、二つのゴール条件つき写像ではありません。

ここでは、方策の族を型に入れます。

* **方策の族 `Pol`：** 一つのゴール条件つき復号 `fullInformationDecoder`（物理層以外では、ゴール `Bool` から実制御の方策への写像）の**一元集合**。
* **問題と方策の組：** `CapProblemPolicy a := CapProblemFixed a × CapPolicy`。評価値 `policyScore` は、**その方策 \(\delta\) から**実験の結合法則（`fullExperimentLaw δ`）を作り、情報の三成分へ押し出した結合法則の直接 CMI です（固定した復号への委譲ではなく、方策から結合法則を生成する）。
* **容量：** `fixedPolicyCapacity := dependentLayerCapacity CapProblemPolicy …`。`fixedCapacity`・`sharedCapacity` と一致します。方策の許容性（`N.data.admissible`）は、許容集合の条件に入れます。包含の埋め込みは、問題・方策を保ち、評価値を保ちます。

### 0.2 このファイルが証明していないこと

* 原文は、方策の族 `Pol` の大きさを要求しません。ここでは、**一元の方策の族**という読みで、現行の容量が、原文の「問題 × 方策の上限」の一例になることを証明しました。
* native の**全方策**に対する上限が、現行の容量に一致するとは**主張しません**（全方策版は未実施）。この限定は、[見取り図](Consistency_Overview.md)の「容量の方策族は一元です」に対応します。
* 非退化性は、上層で、復号がゴールの差を実制御の差へ写して \(\log2\) を達成することです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 原文 §8 は ℱ_i(α) = sup_{(d,π) ∈ 𝔠_{i,α}} I(G_d; Y_d^π | X_d) と、問題 d と方策 π の組の上限を取る。fixedCapacity の問題は方策の添字を持たず、固定した一つの fullInformationDecoder に委譲していた。decode c false／decode c true は、その一つの decoder が出す二つの実制御方策であって、二つのゴール条件付き写像ではない。ここでは方策族を型に入れる。…（以下、上の三点と範囲）。

---

<a id="Tomabechi.Consistency.R123.instance@L32"></a>

## インスタンス `instance@L32`

### 式

$$
\text{共通束の各点の状態型は可測空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

共通束の各点の状態の型に、可測空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capPolicySet"></a>

## 定義 `capPolicySet`

### 式

$$
\mathrm{Pol}=\{\mathrm{fullInformationDecoder}\}
$$

### Lean のコメント（日本語訳）

> 方策族Pol：一つのゴール条件付きdecoderの一元集合。

### 定義の説明

**方策の族** \(\mathrm{Pol}\) です。一つのゴール条件つき復号の**一元集合**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.CapPolicy"></a>

## 定義 `CapPolicy`

### 式

$$
\{\delta\mid\delta\in\mathrm{Pol}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

方策の族の元の型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capPolicyTheOne"></a>

## 定義 `capPolicyTheOne`

### 式

$$
\delta_0=\mathrm{fullInformationDecoder}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

唯一の方策（復号）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capPolicy_eq_the_one"></a>

## 補題 `capPolicy_eq_the_one`

### 式

$$
\pi=\delta_0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方策の族の任意の元は、唯一の方策に等しいです。

### 証明の概略

1. 族が一元集合であること。

----

<a id="Tomabechi.Consistency.R123.CapProblemPolicy"></a>

## 定義 `CapProblemPolicy`

### 式

$$
\mathrm{CapProblemFixed}(a)\times\mathrm{CapPolicy}
$$

### Lean のコメント（日本語訳）

> 問題×方策。

### 定義の説明

**問題と方策の組**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.PolicyAdmissible"></a>

## 定義 `PolicyAdmissible`

### 式

$$
\forall c,g,x,T\ge0,\ \delta(c,g)\ \text{は許容}
$$

### Lean のコメント（日本語訳）

> decoder δの実方策が全層・全ゴールで許容的（開始時刻T≥0）。

### 定義の説明

復号 \(\delta\) の実際の方策が、全層・全ゴールで**許容的**であること（開始時刻 \(T\ge0\)）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissiblePolicy"></a>

## 定義 `capacityAdmissiblePolicy`

### 式

$$
\{q\mid\text{開始時刻}\ge0,\ \text{方策が許容}\}
$$

### Lean のコメント（日本語訳）

> 許容な問題×方策：開始時刻が非負、方策が許容的。

### 定義の説明

**許容される問題と方策の組**です。開始時刻が非負で、方策が許容的であること。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.policyJoint"></a>

## 定義 `SharedModelSignature.policyJoint`

### 式

$$
\text{方策 }\delta\text{ から生成した情報 joint}
$$

### Lean のコメント（日本語訳）

> 方策δから生成した情報joint（入力・ゴール・行為）。

### 定義の説明

方策 \(\delta\) から生成した、情報の結合法則（入力・ゴール・行為）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.policyScore"></a>

## 定義 `SharedModelSignature.policyScore`

### 式

$$
\mathrm{score}(\text{その方策から生成した joint の直接 CMI})
$$

### Lean のコメント（日本語訳）

> 問題×方策の評価値：その方策から生成したjointの直接CMI。

### 定義の説明

問題と方策の組の評価値です。その方策から生成した結合法則の**直接 CMI** です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.fixedPolicyCapacity"></a>

## 定義 `SharedModelSignature.fixedPolicyCapacity`

### 式

$$
\mathcal F_{d,H}(a)=\sup_{(p,\pi)}\mathrm{score}
$$

### Lean のコメント（日本語訳）

> 固定した(d,H)の、問題×方策の上限としての容量。

### 定義の説明

固定した \((d,H)\) の、**問題と方策の組の上限**としての容量です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityEmbeddingPolicy"></a>

## 定義 `capacityEmbeddingPolicy`

### 式

$$
(p,\pi)\mapsto(\iota(p),\pi)
$$

### Lean のコメント（日本語訳）

> 包含による問題×方策の埋込み（問題は層の埋込み、方策は保つ）。

### 定義の説明

包含による、問題と方策の組の埋め込みです（問題は層の埋め込み、方策は保ちます）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.capacityEmbeddingPolicy_injective"></a>

## 補題 `capacityEmbeddingPolicy_injective`

### 式

$$
\text{単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この埋め込みは単射です。

### 証明の概略

1. 問題の埋め込みの単射性（`capacityEmbeddingFixed_injective`）と、方策が同じこと。

----

<a id="Tomabechi.Consistency.R123.policyJoint_the_one"></a>

## 補題 `policyJoint_the_one`

### 式

$$
\text{方策が一元なので、方策から生成した joint}=\mathrm{capacityJoint}
$$

### Lean のコメント（日本語訳）

> 方策が一元なので、方策から生成したjointは固定decoderのcapacityJoint。

### 補題の説明

方策が一元なので、方策から生成した結合法則は、固定した復号の `capacityJoint` に等しいです。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Consistency.R123.policyScore_eq_fixed"></a>

## 補題 `policyScore_eq_fixed`

### 式

$$
\mathrm{policyScore}=\mathrm{capacityScoreFixed}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

問題と方策の組の評価値は、固定した主体・履歴の評価値に等しいです。

### 証明の概略

1. 方策が唯一の復号に等しいので、代入して `rfl`。

----

<a id="Tomabechi.Consistency.R123.capacityAdmissiblePolicy_nonempty"></a>

## 補題 `capacityAdmissiblePolicy_nonempty`

### 式

$$
\text{許容な組は空でない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容される組は存在します。

### 証明の概略

1. 許容な問題の存在（`capacityAdmissibleFixed_nonempty`）と、唯一の方策が許容的であること。

----

<a id="Tomabechi.Consistency.R123.fixedPolicyCapacity_eq_fixed"></a>

## 補題 `fixedPolicyCapacity_eq_fixed`

### 式

$$
\mathcal F^{\rm policy}_{d,H}=\mathcal F_{d,H}
$$

### Lean のコメント（日本語訳）

> 一元の方策族の上で、問題×方策の上限はfixedCapacityに一致する。

### 補題の説明

一元の方策族の上で、**問題と方策の組の上限は、`fixedCapacity` に一致**します。

### 証明の概略

1. 両方の上限が、同じ評価値の像の集合の上限であること（評価値の一致と、許容な組と許容な問題の対応）。

----

<a id="Tomabechi.Consistency.R123.SharedPolicyCapacityInputs"></a>

## 構造体 `SharedPolicyCapacityInputs`

### 式

$$
\text{問題×方策の容量の受入型}
$$

### Lean のコメント（日本語訳）

> 問題×方策の容量の受入型。

### 定義の説明

**問題と方策の組の容量の受入の型**です。フィールドは、方策の族は一元、方策が許容的、二つの値は二つの実制御方策で区別され再符号化で戻る（ゴール条件つき写像は一つ）、許容な組が空でない、各組の結合法則は、その方策の実験の結合法則の押し出しで情報の法則そのもの、評価値・容量が固定した容量・主体履歴を動かす容量と一致、容量が \(\log2\) 以下・非負・単調・底で 0・頂で \(\log2\)、包含の埋め込みは組を保ち、単射・許容性・評価値を保存、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_policyCapacityInputs"></a>

## 定理 `sharedModel_policyCapacityInputs`

### 式

$$
\mathrm{SharedPolicyCapacityInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、問題と方策の組の容量の入力を満たします。

### 証明の概略

1. 復号の許容性（全実験の入力の `decoder_admissible`）と、固定した容量の入力（`sharedModel_fixedCapacityInputs`）から、各フィールドを導く。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_policy_capacity"></a>

## 定理 `final_consistency_with_policy_capacity`

### 式

$$
\exists N,\mathrm{sig},\ \cdots\wedge\mathrm{SharedPolicyCapacityInputs}(N)
$$

### Lean のコメント（日本語訳）

> 現行評価の前件・全正典担体の自己過程・問題×方策の容量を同じNで。

### 補題の説明

現行評価の前件・全正典担体の自己過程・問題と方策の組の容量を、**同じ \(N\) で**述べる存在宣言です。

### 証明の概略

1. `sharedModel` と、各部品の定理を組み合わせる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
