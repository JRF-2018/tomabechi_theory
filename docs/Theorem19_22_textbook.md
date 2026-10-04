# Theorem19_22.lean 解説

> 対象: [`Theorem19_22.lean`](../Theorem19_22.lean)（定理19/22の一般測度 CMI 接続の互換入口）。宣言はなく、`import` と `#print axioms`（公理の監査）だけです。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| `#print axioms` | その定理が依存する公理を表示する検査命令。標準の 3 公理だけならよい。 |
| 標準公理 | `propext`, `Classical.choice`, `Quot.sound`。Mathlib の数学が使う標準的な公理。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

かつて 1 つの大きなファイルだった定理19/22の一般測度 CMI の形式化を、分割したあとの**互換入口**です。旧モジュール名と、既存の公理の監査コマンドを維持するために残されています。

### 0.2 読み込むファイルと解説書

| ファイル | 内容 | 解説書 |
| --- | --- | --- |
| `Tomabechi/Information/MeasureCMI.lean` | 一般測度の CMI の核 | [解説](Tomabechi_Information_MeasureCMI_textbook.md) |
| `Tomabechi/Information/MeasureCMICapacity.lean` | 依存型の容量との橋 | [解説](Tomabechi_Information_MeasureCMICapacity_textbook.md) |
| `Tomabechi/Counterexamples/DecoderRegularity.lean` | 出力 σ 代数の正則性が必要な反例 | [解説](Tomabechi_Counterexamples_DecoderRegularity_textbook.md) |

### 0.3 ファイル冒頭のコメント（日本語訳）

> **互換入口**
>
> 定理19/22の一般測度 CMI の接続は `Tomabechi.Information.MeasureCMI`、出力の可測性の反例の証人は `Tomabechi.Counterexamples.DecoderRegularity` に配置した。この旧モジュール名と、既存の公理の監査コマンドを維持する。

### 0.4 公理の監査

`#print axioms` で、`posteriorGoalKernel_disintegrates`、`finite_measure_cmi_eq_entropy_sub_posterior`、`finite_measure_cmi_le_inputGoalEntropy`、`cmiLawOfJoint_reference_eq`、`dependent_measure_cmi_capacity_eq_zero_of_inputGoalEntropy_zero` など、主要な定理が**標準公理のみ**に依存することを確認します。

### 0.5 このファイルが証明していないこと

何も証明していません。内容は上の表のファイルにあります。

## コメント修正記録

（なし）
