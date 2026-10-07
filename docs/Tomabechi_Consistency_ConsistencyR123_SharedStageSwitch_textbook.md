# Tomabechi/Consistency/ConsistencyR123_SharedStageSwitch.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedStageSwitch.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedStageSwitch.lean)（共有署名の H-stage の全切り替えの入力）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の、**H-stage の全切り替えの入力**を作るファイルです。段階の解析入力は `N.stages` を読み、段の中心は共通概念束の**忠実な二座標の表現**で指定します。**元の 23-B の間隔・線分・時間・遷移・対数的な待ち時間の条件をすべて要求**します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「段階の谷と情報」（C3）の、共有署名への接続です。

* 共通束の二座標を二次元の認知状態に表す表現（単射。旧アドレスで元の共通表象の等長の持ち上げを回収）。
* \(N\) の段に対応する共通束の更新の列 \(U_n\)（頂より下、順に更新される、新しい層）。
* 全切り替えの前件 `SharedStageSwitchInputs` と、23-B の一般入口の適用。
* 持ち上げても減衰率・振幅が変わらない。

### 0.2 このファイルが証明していないこと

* 具体的な共有署名（`sharedModel`）についての構成です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 段階の解析入力は N.stages を読み、中心は共通概念束の忠実な二座標表現で指定する。原 23-B の gap・線分・時間・遷移・対数待ち条件を全て要求する。

---

<a id="Tomabechi.Consistency.R123.sharedStageRepresentation"></a>

## 定義 `sharedStageRepresentation`

### 式

$$
a\mapsto\bigl(a_0/\sqrt2,\ a_1/\sqrt2\bigr)
$$

### Lean のコメント（日本語訳）

> 共通概念束の二座標を同じ二次元認知状態へ表す。

### 定義の説明

共通概念束の二つの座標を、同じ二次元の認知状態（\(\sqrt2\) で割ったもの）として表す写像です。H-stage の中心を、共通束の**忠実な二座標の表現**で指定するために使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedStageRepresentation_injective"></a>

## 補題 `sharedStageRepresentation_injective`

### 式

$$
\text{表現は単射}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この表現は単射です（共通束の異なる点は、異なる認知状態になる）。

### 証明の概略

1. 二つの座標が等しい（\(\sqrt2\ne0\) で割ったものが等しい）ので、座標が等しい。

----

<a id="Tomabechi.Consistency.R123.sharedStageRepresentation_oldAddress"></a>

## 補題 `sharedStageRepresentation_oldAddress`

### 式

$$
\text{旧アドレスで、元の共通表象の等長 lift を回収}
$$

### Lean のコメント（日本語訳）

> 旧アドレスで元の共通表象の等長liftを回収する。

### 補題の説明

旧いアドレスでは、元の共通表象（\(\tfrac{n}{n+1}\)）の**等長の持ち上げ**を回収します。

### 証明の概略

1. 頂と自然数の場合分け。座標ごとに、対角の層の座標が \(\mathrm{rep}(n)/\sqrt2\) になること（持ち上げの定義）を確認する。

----

<a id="Tomabechi.Consistency.R123.sharedStageU"></a>

## 定義 `sharedStageU`

### 式

$$
U_n=\mathrm{layerAddressEmbedding}(\mathrm{layerU}\,n)
$$

### Lean のコメント（日本語訳）

> Nの段列に対応する共通束の更新列。

### 定義の説明

\(N\) の段の列に対応する、共通束の**更新の列** \(U_n\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedStageV"></a>

## 定義 `sharedStageV`

### 式

$$
V_n=\mathrm{layerAddressEmbedding}(\mathrm{layerV}\,n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

新しい層の列 \(V_n\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedStageU_update"></a>

## 補題 `sharedStageU_update`

### 式

$$
U_{n+1}=U_n\sqcup V_{n+1}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

更新の列は、前の層と新しい層の結びです。

### 証明の概略

1. \(U_n\le U_{n+1}\)（埋め込みの単調性）なので、結びは \(U_{n+1}\)。

----

<a id="Tomabechi.Consistency.R123.sharedStageU_below_top"></a>

## 補題 `sharedStageU_below_top`

### 式

$$
U_n<\top
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

更新の列は、頂より真に下です。

### 証明の概略

1. 埋め込みは狭義単調で、頂を頂に送る。

----

<a id="Tomabechi.Consistency.R123.sharedStageV_new"></a>

## 補題 `sharedStageV_new`

### 式

$$
\neg\,(V_{n+1}\le U_n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

新しい層は、前の更新には含まれません（本当に新しい）。

### 証明の概略

1. 埋め込みは順序を反映する（`le_iff_le`）。元の層で成り立たない（`layerV_new`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.stageValleys"></a>

## 定義 `SharedModelSignature.stageValleys`

### 式

$$
\text{N 自身の選択谷点・選択軌道}
$$

### Lean のコメント（日本語訳）

> N自身の選択谷点・選択軌道。

### 定義の説明

\(N\) の段の列から選ぶ、谷の**最小点と軌道**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageSwitchInputs"></a>

## 構造体 `SharedStageSwitchInputs`

### 式

$$
\text{元の H-stage の全切り替え前件（N の段の列・時刻で）}
$$

### Lean のコメント（日本語訳）

> 元H-stageの全切替前件をNの同じ段列・時刻で要求する。

### 定義の説明

元の H-stage の**全切り替えの前件**を、\(N\) の同じ段の列・時刻で要求する構造体です。フィールドは、保存式、中心が共通束の表現で指定されること、住所、間隔の条件（\(\theta\) が谷の距離に対して十分小さい）、線分が次の球に入ること、開始時刻、段の移行（次の初期値は前の段の軌道の終端）、開始時刻の漸化式、発散、待ち時間（対数）の条件、です。原 23-B の間隔・線分・時間・遷移・対数的な待ち時間の条件を**すべて要求**します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedStageSwitchInputs.theorem23B"></a>

## 定義 `SharedStageSwitchInputs.theorem23B`

### 式

$$
\text{23-B の一般入口の適用}
$$

### Lean のコメント（日本語訳）

> 全前件を同じNで読む23-B一般入口の適用。

### 定義の説明

全前件を同じ \(N\) で読む、定理23-B の一般の入口の適用です。

### 証明の概略

1. 切り替えの核（`meanField_stage_specs_and_switches_give_condition23B_core`）に、更新の列・表現・段の列・閾値・間隔・時刻・待ち時間と、入力のフィールドを渡す。

----

<a id="Tomabechi.Consistency.R123.sharedLifted_decayRate"></a>

## 補題 `sharedLifted_decayRate`

### 式

$$
\text{持ち上げても、選択谷の減衰率は変わらない}
$$

### Lean のコメント（日本語訳）

> liftしても選択谷の減衰率を落とさない。

### 補題の説明

持ち上げても、選んだ谷の**減衰率**は落ちません（元の谷の減衰率に等しい）。

### 証明の概略

1. 定義を展開（二次谷の減衰率は 1）。

----

<a id="Tomabechi.Consistency.R123.sharedLifted_decayAmplitude"></a>

## 補題 `sharedLifted_decayAmplitude`

### 式

$$
\text{持ち上げても、減衰の振幅は厳密に一致}
$$

### Lean のコメント（日本語訳）

> 初期評価差と曲率余裕を保ち、距離評価係数も厳密一致する。

### 補題の説明

持ち上げても、**減衰の振幅**（初期の評価差と曲率の余裕から決まる距離評価の係数）は、厳密に一致します。

### 証明の概略

1. 両方の振幅の定義を展開し、最小点が持ち上げたスカラーの最小点であること、持ち上げの距離の補題（`liftedStageCenter_difference_norm`）で、平方根の中身を比べる。

----

<a id="Tomabechi.Consistency.R123.sharedModel_stageSwitchInputs"></a>

## 定理 `sharedModel_stageSwitchInputs`

### 式

$$
\mathrm{SharedStageSwitchInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 具体共有署名は原H-stageの全切替前件を満たす。

### 補題の説明

具体的な共有署名は、元の H-stage の**全切り替えの前件**を満たします。

### 証明の概略

1. 中心・住所は、更新の列と表現の旧アドレスの補題から。間隔・線分は、H-stage の列の補題（`hStageSequence_gap_threshold`・`hStageSequence_segment_in_next_ball`）を持ち上げる。
2. 開始時刻・移行・漸化式・発散・待ち時間は、C3 のファイルの補題（`stageTime_recurrence`・`stageTime_unbounded` など）。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
