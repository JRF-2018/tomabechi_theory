# Tomabechi/Consistency/ConsistencyR123_FullExperimentRecovery.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_FullExperimentRecovery.lean`](../Tomabechi/Consistency/ConsistencyR123_FullExperimentRecovery.lean)（全域実験と、有限の旧い住所の実験の、厳密な回収）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**全域の実験**（共通束の全点）と、**有限の旧い住所の実験**との、**厳密な回収**を示すファイルです。全域の実験は、元の（native の）状態の型を保存します。有限の旧い住所では、**同じ住所の型の変換（cast）だけ**で、以前の状態・費用・自己過程・標本を含む**結合法則の全体**へ戻ります。非埋め込みの点や頂点の実験を、有限の旧い住所の実験に**読み替えることはしません**。

### 0.2 このファイルが証明していないこと

* 有限の旧い住所でだけ、従来の実験への回収が成り立ちます。それ以外の点の実験は、元の型のままです。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 全域実験は native 状態型を保存する。有限旧住所では、同じ住所の型 cast だけで以前の状態・費用・自己過程・標本を含む joint 全体へ戻る。非埋込み点と頂点の実験を有限旧住所の実験に読み替えない。

---

<a id="Tomabechi.Consistency.R123.instance@L17"></a>

## インスタンス `instance@L17`

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

<a id="Tomabechi.Consistency.R123.stateCast_measurable"></a>

## 補題 `stateCast_measurable`

### 式

$$
\text{状態の型の変換（cast）は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

層の等式 \(i=j\) に沿った、状態の型の変換（cast）は、可測です（`private`）。

### 証明の概略

1. 等式で場合分けして、cast が恒等写像になることから。

----

<a id="Tomabechi.Consistency.R123.fullExperimentFiniteRecovery"></a>

## 定義 `fullExperimentFiniteRecovery`

### 式

$$
\text{有限住所の状態型の cast（他の観測はそのまま）}
$$

### Lean のコメント（日本語訳）

> 有限住所の状態型cast。その他の観測はすべてそのまま保持する。

### 定義の説明

有限の住所での、**状態の型の変換だけ**を行う写像です。その他の観測（標本・自己過程・費用）は、すべてそのまま保持します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.fullExperimentFiniteRecovery_measurable"></a>

## 補題 `fullExperimentFiniteRecovery_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この回収の写像は可測です。

### 証明の概略

1. 各成分の可測性（状態の cast は前の補題）を合わせる。

----

<a id="Tomabechi.Consistency.R123.SharedFullExperimentInputs.finiteObservation"></a>

## 補題 `SharedFullExperimentInputs.finiteObservation`

### 式

$$
\text{同じ標本ごとに、全域実験が従来の有限実験の観測に戻る}
$$

### Lean のコメント（日本語訳）

> 同じ入力標本ごとに、全域実験が従来の有限実験の全観測へ戻る。

### 補題の説明

同じ入力の標本ごとに、全域の実験が、従来の**有限実験の全観測**へ戻ります。

### 証明の概略

1. 全域実験の観測の定義を展開し、有限層での軌道・走行費が、従来の有限実験のもの（状態の cast を除いて）に等しいことを示す。

----

<a id="Tomabechi.Consistency.R123.SharedFullExperimentInputs.finiteLaw"></a>

## 補題 `SharedFullExperimentInputs.finiteLaw`

### 式

$$
\text{標本・自己過程・情報・状態・費用の結合法則全体を回収}
$$

### Lean のコメント（日本語訳）

> 標本・自己過程・情報・状態・費用のjoint全体の回収。周辺lawだけの一致で代替しない。

### 補題の説明

標本・自己過程・情報・状態・費用の**結合法則の全体**の回収です。周辺の法則だけの一致で代替しません。

### 証明の概略

1. 像の合成（`map_map`）。標本ごとの回収（前の補題）。

----

<a id="Tomabechi.Consistency.R123.SharedFullExperimentInputs.legacyFiniteLaw"></a>

## 補題 `SharedFullExperimentInputs.legacyFiniteLaw`

### 式

$$
\text{さらに }\Gamma\text{ を制限すれば、旧署名の全実験 joint を回収}
$$

### Lean のコメント（日本語訳）

> さらにΓ制限観測を行えば、旧署名の全実験jointを回収する。

### 補題の説明

さらに \(\Gamma\) を制限する観測を行えば、**旧い署名の全実験の結合法則**を回収します。

### 証明の概略

1. 有限の回収（前の補題）と、\(\Gamma\) の制限による旧署名への回収（`SharedSCMCouplings.experimentLaw`）を合成する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
