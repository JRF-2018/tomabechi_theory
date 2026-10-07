# Tomabechi/Consistency/ConsistencyC6_ActuatorInputs.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_ActuatorInputs.lean`](../Tomabechi/Consistency/ConsistencyC6_ActuatorInputs.lean)（共有署名の実 D・E を読む、定理27-A の入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

[TopActuator](Tomabechi_Consistency_ConsistencyC6_TopActuator_textbook.md) で構成した定理27-A の全運用入力を、**共有署名 `ModelSignature` のフィールド**（実軌道・残差 \(W\)・方策の同値・フィードバック）の言葉で述べ直すファイルです。全状態の上の自然ドリフト・基準入力の相殺を保持し、軌道上の a.e. な相殺だけに弱めません。

### 0.2 このファイルが証明していないこと

* 解析的な証明は、前のファイルのものをそのまま使います（複製しません）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 実軌道、残差 W、方策同値と feedback は同じ M のフィールドから取る。全状態上の自然ドリフト・基準入力の相殺を保持し、軌道上の a.e. 相殺だけへ弱めない。

---

<a id="Tomabechi.Consistency.C6.ModelSignature.topPath"></a>

## 定義 `ModelSignature.topPath`

### 式

$$
\text{頂点の軌道（実 D・E のフィードバック）}
$$

### Lean のコメント（日本語訳）

> MのDとEの実feedbackで得る頂点軌道。

### 定義の説明

共有署名 \(M\) の、データ D と力学 E の**実際のフィードバック**で得る頂点の軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.TopActuatorInputs"></a>

## 構造体 `TopActuatorInputs`

### 式

$$
\text{定理27-A の全運用入力の証拠}
$$

### Lean のコメント（日本語訳）

> O18/O19の27-A入力。場の具体化は固定し、全初期対に同じ場を使う。これは全O条件の受入recordの頂点解析部分である。

### 定義の説明

定理27の 27-A の**全運用入力**です。場（自然なドリフト・基準入力・勾配）の具体化は固定し、全初期対に同じ場を使います。これは、全原文条件の受け入れの構造体の、頂点の解析の部分です。フィールドは、[C6TopActuatorInputs](Tomabechi_Consistency_ConsistencyC6_TopActuator_textbook.md) と同じ形ですが、軌道を共有署名 \(M\) の `topPath` で述べます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.commonModel_topActuatorInputs"></a>

## 定理 `commonModel_topActuatorInputs`

### 式

$$
\forall x,T\ge0,\ \mathrm{TopActuatorInputs}(\text{commonModel},x,T)
$$

### Lean のコメント（日本語訳）

> commonModelの実D/Eフィールドが全初期対の27-A入力を満たす。既存入力の実軌道との定義的一致を使い、解析証明を複製しない。

### 補題の説明

共有モデルの実際の D・E のフィールドが、全初期対で 27-A の入力を満たします。既存の入力が、実軌道と定義的に一致することを使い、解析的な証明は複製しません。

### 証明の概略

1. 先のファイルの `c6TopActuatorInputs` を取り、各フィールドをそのまま入れる。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
