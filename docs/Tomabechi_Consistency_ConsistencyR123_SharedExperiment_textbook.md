# Tomabechi/Consistency/ConsistencyR123_SharedExperiment.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_SharedExperiment.lean`](../Tomabechi/Consistency/ConsistencyR123_SharedExperiment.lean)（共有署名の、情報・自己過程・制御状態・費用の実験）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

共有署名 \(N\) の、**情報・自己過程・制御の状態・費用**を、**同じ実験の法則**として観測するファイルです。情報のラベルを \(N\) に格納された許容方策に復号し、同じ有限層 `N.data` の軌道と走行費を観測します。二値のラベルは、許容制御の族の**部分族**を指定します。旧い署名の実験の結合法則の**全体**との一致は、\(\Gamma\) を制限する観測を通して証明します。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の、共有署名への接続です。

### 0.2 このファイルが証明していないこと

* 二値の行為は、許容ゲインの部分族（ゼロと最大ゲイン）への復号です。
* 有限の旧い住所での実験です（頂点・非埋め込み点の実験は、次のファイルで扱います）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 情報ラベルを N に格納された許容方策へ復号し、同じ有限層 N.data の軌道と走行費を観測する。二値ラベルは許容制御族の部分族を指定する。旧署名の実験 joint 全体との一致は Γ 制限観測を通して証明する。

---

<a id="Tomabechi.Consistency.R123.finiteIndex"></a>

## 補題 `finiteIndex`

### 式

$$
\mathrm{fullCommonLayerIndex}(\mathrm{layerAddressEmbedding}(k))=k
$$

### Lean のコメント（日本語訳）

> 有限層の型同定。状態・方策のcastを同じ住所で行う。

### 補題の説明

有限層の**型の同一視**です。状態・方策の cast を、同じ住所で行うための補助です（`private`）。

### 証明の概略

1. 共通束の層番号の補題（`fullCommonLayerIndex_layerAddress`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.finiteExperimentState"></a>

## 定義 `SharedModelSignature.finiteExperimentState`

### 式

$$
N.\mathrm{data}\text{ の実有限層軌道を AgentState 座標で観測}
$$

### Lean のコメント（日本語訳）

> N.dataの実有限層軌道をAgentState座標で観測する。

### 定義の説明

\(N\) のデータの**実際の有限層の軌道**を、`AgentState` の座標で観測します（状態・方策の cast を同じ住所で行う）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.finiteExperimentCost"></a>

## 定義 `SharedModelSignature.finiteExperimentCost`

### 式

$$
\text{同じ実軌道の同じ走行費}
$$

### Lean のコメント（日本語訳）

> 同じ実有限層軌道の同じ走行費。定数費用へ置き換えない。

### 定義の説明

同じ実際の有限層の軌道の、**同じ走行費**です。定数の費用に置き換えません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.trajectory_cast"></a>

## 補題 `trajectory_cast`

### 式

$$
\text{軌道に対して cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道について、添字の等式に沿った型の変換（cast）で値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして、cast が何もしないことから。

----

<a id="Tomabechi.Consistency.R123.cost_cast"></a>

## 補題 `cost_cast`

### 式

$$
\text{走行費に対して cast は値を変えない}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

走行費について、添字の等式に沿った型の変換（cast）で値が変わらないことを示す補助補題です（`private`）。

### 証明の概略

1. 添字の等式で場合分けして。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.finiteExperimentState"></a>

## 補題 `SharedDataPreservation.finiteExperimentState`

### 式

$$
N.\mathrm{finiteExperimentState}=\text{旧署名の有限層の軌道}
$$

### Lean のコメント（日本語訳）

> Nの保存式により有限層の実状態を旧署名の同じ制御へ回収する。

### 補題の説明

\(N\) の保存式により、有限層の実際の状態を、旧い署名の同じ制御の軌道に回収します。

### 証明の概略

1. 軌道の保存式（`trajectory`）と cast の補題。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.finiteExperimentCost"></a>

## 補題 `SharedDataPreservation.finiteExperimentCost`

### 式

$$
N.\mathrm{finiteExperimentCost}=\text{旧署名の走行費}
$$

### Lean のコメント（日本語訳）

> 実費用も同じ署名の同じ実状態で一致する。

### 補題の説明

実際の費用も、同じ署名の同じ実際の状態で一致します。

### 証明の概略

1. 走行費の保存式と、前の補題。

----

<a id="Tomabechi.Consistency.R123.sharedInformationIndex_finite"></a>

## 補題 `sharedInformationIndex_finite`

### 式

$$
\mathrm{index}(\mathrm{layerAddressEmbedding}(k))=k
$$

### Lean のコメント（日本語訳）

> 全有限旧アドレスで情報lawの番号も保存される。

### 補題の説明

すべての有限の旧いアドレスで、情報の法則の番号も保存されます。

### 証明の概略

1. \(k=0\) は旧アドレス 0（底）、\(k=n+1\) は旧い正の層（`commonConceptInformationIndex_old_*`）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.experimentInputLaw"></a>

## 定義 `SharedModelSignature.experimentInputLaw`

### 式

$$
\text{外生の法則}\otimes N.\mathrm{informationLaw}
$$

### Lean のコメント（日本語訳）

> 同じN.scmの外生標本と同じN情報lawを使う実験入力。

### 定義の説明

同じ `N.scm` の外生標本と、同じ \(N\) の情報の法則を使う、実験の入力の標本の法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedExperimentObservation"></a>

## 定義 `SharedExperimentObservation`

### 式

$$
\text{標本}\times((\Gamma,R),h)\times(\text{状態},\text{費用})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の観測の型です（標本・型つき自己過程・状態・費用）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.experimentObservation"></a>

## 定義 `SharedModelSignature.experimentObservation`

### 式

$$
w\mapsto(w,\ \text{自己過程},\ \text{状態},\ \text{費用})
$$

### Lean のコメント（日本語訳）

> N.scmの自己過程とN.dataの実制御状態/費用を同時に観測する。

### 定義の説明

`N.scm` の自己過程と、`N.data` の実際の制御の状態・費用を、同時に観測します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.experimentLaw"></a>

## 定義 `SharedModelSignature.experimentLaw`

### 式

$$
\text{標本の法則を観測で押し出したもの}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実験の法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedExperimentRecovery"></a>

## 定義 `sharedExperimentRecovery`

### 式

$$
\text{実験の観測を、旧署名の観測へ戻す}
$$

### Lean のコメント（日本語訳）

> 全実験jointを旧署名へ戻す。標本・情報・自己表現・状態・費用を残す。

### 定義の説明

全実験の結合を、旧い署名の観測へ戻す写像です。標本・情報・自己の表現・状態・費用を残し、\(\Gamma\) だけを制限します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedExperimentRecovery_measurable"></a>

## 補題 `sharedExperimentRecovery_measurable`

### 式

$$
\text{可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この写像は可測です。

### 証明の概略

1. 各成分の可測性を合わせる。

----

<a id="Tomabechi.Consistency.R123.SharedDataPreservation.experimentInputLaw"></a>

## 補題 `SharedDataPreservation.experimentInputLaw`

### 式

$$
N.\mathrm{experimentInputLaw}=\text{旧署名のもの}
$$

### Lean のコメント（日本語訳）

> 共有保存条件から元の入力jointを厳密に回収する。

### 補題の説明

共有の保存条件から、元の入力の結合法則を**厳密に回収**します。

### 証明の概略

1. 外生法則（`scm_law`）と情報の法則（`information`・番号の保存）が一致。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experimentObservation"></a>

## 補題 `SharedSCMCouplings.experimentObservation`

### 式

$$
\text{実験の観測は、標本ごとに旧署名の観測に一致}
$$

### Lean のコメント（日本語訳）

> 旧住所の全SCM構造式と実制御状態/費用が同じ標本ごとに一致する。

### 補題の説明

旧いアドレスの全 SCM の構造式と、実際の制御の状態・費用が、**同じ標本ごとに一致**します。

### 証明の概略

1. 定義を展開し、構造式の一致（状態・出力・候補）と、状態・費用の補題（`finiteExperimentState`・`finiteExperimentCost`）で書き換える。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experimentLaw"></a>

## 補題 `SharedSCMCouplings.experimentLaw`

### 式

$$
\text{実験の結合法則全体が、旧署名のものに一致}
$$

### Lean のコメント（日本語訳）

> 実験joint全体が同じ旧署名のjointへ一致する。

### 補題の説明

実験の**結合法則の全体**が、同じ旧い署名の結合法則に一致します。

### 証明の概略

1. 入力の法則が一致（前の補題）、観測が標本ごとに一致（前の補題）。像の合成。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.experiment_stateCost"></a>

## 補題 `SharedModelSignature.experiment_stateCost`

### 式

$$
\text{状態・費用の周辺を、入力の法則から回収}
$$

### Lean のコメント（日本語訳）

> 同じNの実状態・実費用の周辺を、Nの入力lawから回収する。

### 補題の説明

同じ \(N\) の実際の状態・費用の周辺を、\(N\) の入力の法則から回収します。

### 証明の概略

1. 像の合成（`map_map`）。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experiment_information"></a>

## 補題 `SharedSCMCouplings.experiment_information`

### 式

$$
\text{情報の周辺}=N.\mathrm{informationLaw}
$$

### Lean のコメント（日本語訳）

> 同じNの情報周辺は旧署名を経由しても変わらない。

### 補題の説明

同じ \(N\) の情報の周辺は、旧い署名を経由しても変わりません。

### 証明の概略

1. 実験の法則が旧署名のものに一致（前の補題）。旧署名の情報の周辺と、情報の保存。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experiment_actualPolicyInformation"></a>

## 補題 `SharedSCMCouplings.experiment_actualPolicyInformation`

### 式

$$
\text{復号・再符号化した joint}=N.\mathrm{informationLaw}
$$

### Lean のコメント（日本語訳）

> 情報行為を実許容入力へ復号・再符号化したjointを保つ。

### 補題の説明

情報の行為を、実際の許容入力へ復号し、再び符号化した結合法則も保ちます。

### 証明の概略

1. 旧署名の復号・再符号化の補題（`c6ExperimentLaw_actualPolicyInformation`）と実験の法則の一致。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.information_optimal"></a>

## 補題 `SharedSCMCouplings.information_optimal`

### 式

$$
\text{情報行為 true}=\text{有限層の実最適方策}
$$

### Lean のコメント（日本語訳）

> 有限層の実最適方策も同じ情報行為trueで指定される。

### 補題の説明

有限層の**実際の最適方策**も、同じ情報の行為 `true` で指定されます。

### 証明の概略

1. 最適方策の保存式と、旧署名の情報行為の最適性（`information_optimal`）。cast の整理。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.intervenedExperimentObservation"></a>

## 定義 `SharedModelSignature.intervenedExperimentObservation`

### 式

$$
\text{介入時の観測}
$$

### Lean のコメント（日本語訳）

> 介入時も同じ標本・情報方策・状態・費用を観測する。

### 定義の説明

介入のときも、同じ標本・情報の方策・状態・費用を観測します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experiment_intervention"></a>

## 補題 `SharedSCMCouplings.experiment_intervention`

### 式

$$
\text{候補への介入は、実験の結合法則全体を変えない}
$$

### Lean のコメント（日本語訳）

> 全有限旧層で候補介入は実験joint全体を変えない。

### 補題の説明

すべての有限の旧い層で、**候補への介入は、実験の結合法則の全体を変えません**。

### 証明の概略

1. 観測を各点で比べる。出力が候補に依らない（a.e.）ことと、状態・費用が候補に依らないことから。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.information_probability"></a>

## 補題 `SharedSCMCouplings.information_probability`

### 式

$$
\text{情報の法則は確率測度}
$$

### Lean のコメント（日本語訳）

> 同じ署名の物理層・正層の情報lawは全て確率法則である。

### 補題の説明

同じ署名の物理層・正の層の情報の法則は、すべて確率測度です。

### 証明の概略

1. 番号で場合分け：0 は物理層の確率測度性、正は上位層の確率測度性。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experiment_probability"></a>

## 補題 `SharedSCMCouplings.experiment_probability`

### 式

$$
\text{標本の法則と観測の結合法則は確率測度}
$$

### Lean のコメント（日本語訳）

> 実標本lawと全観測jointの確率性。

### 補題の説明

実際の標本の法則と、観測の結合法則は、確率測度です。

### 証明の概略

1. 情報の法則が確率測度（前の補題）で、積測度・押し出しも確率測度。

----

<a id="Tomabechi.Consistency.R123.SharedSCMCouplings.experiment_selfProcess"></a>

## 補題 `SharedSCMCouplings.experiment_selfProcess`

### 式

$$
\text{自己過程の周辺}=\text{ベースライン joint}
$$

### Lean のコメント（日本語訳）

> 三表現・Γを付加した共通束の自己過程の周辺を、そのまま回収する。

### 補題の説明

三つの表現・\(\Gamma\) を付加した共通束の自己過程の周辺を、そのまま回収します。

### 証明の概略

1. 像の合成で、自己過程の成分は外生標本の関数。積測度の第 1 周辺は外生法則。

----

<a id="Tomabechi.Consistency.R123.SharedSCMAndExperimentInputs"></a>

## 構造体 `SharedSCMAndExperimentInputs`

### 式

$$
\text{R3・27 に、同じ SCM の全構造式と実験回収を接続する受入型}
$$

### Lean のコメント（日本語訳）

> R3・27に、同じSCMの全構造式と実験回収を接続する受入型。

### 定義の説明

R3・27 の入力に、**同じ SCM の全構造式と実験の回収**を接続する受入の構造体です（`SharedR3And27Inputs` を拡張）。フィールドは、SCM の構造式の保存、型つき自己過程の 25-A(2)、実験の結合法則の回収、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_scmAndExperimentInputs"></a>

## 定理 `sharedModel_scmAndExperimentInputs`

### 式

$$
\mathrm{SharedSCMAndExperimentInputs}(\text{sharedModel})
$$

### Lean のコメント（日本語訳）

> 同じ署名の全受入入力を外部モデル前提なしに同時構成する。

### 補題の説明

同じ署名の全受入の入力を、外部のモデルの前提なしに、**同時に構成**します。

### 証明の概略

1. R3・27 の入力（`sharedModel_r3Inputs`・`sharedModel_theorem27Inputs`）、SCM の保存式、自己過程の 25-A(2)、実験の回収。

----

<a id="Tomabechi.Consistency.R123.shared_scm_and_experiment_model_exists"></a>

## 定理 `shared_scm_and_experiment_model_exists`

### 式

$$
\exists N,\ \mathrm{SharedSCMAndExperimentInputs}(N)
$$

### Lean のコメント（日本語訳）

> stage/R2/最終監査を残した、SCM・実験付き共有署名の同時存在。

### 補題の説明

段・R2・最終監査を残した、SCM・実験つきの共有署名の同時の存在です。

### 証明の概略

1. `sharedModel` と前の定理。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
