# Theorem22_InvariantRegion_P13.lean 解説

> 対象: [`Theorem22_InvariantRegion_P13.lean`](../Theorem22_InvariantRegion_P13.lean)（H-stage緩和入力の定理21第4結論（直接KL型CMI）接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem22_InvariantRegion`（緩和した不変領域の段階入力）を、定理21の**第 4 結論（直接 KL 型 CMI の情報容量）**につなぐ入口です。`MeanFieldDirectCMI.lean` の結果の、不変領域版です。谷・軌道の結論は、**初期全劣水準集合の等式なし**の不変領域の証人から、第 4 結論は同じ生成した同時法則の直接 KL 型 CMI で返します。

### 0.2 このファイルが証明していないこと

- 情報容量は谷の力学とは独立の入力（`MeanFieldDirectCMI.lean` と同じ）から得ます。枝・台・LUB の対応も仮定のままです。

### 0.3 ファイル冒頭のコメント（日本語訳）と名前空間

> **H-stage の緩和した入力の、定理21の第 4 結論（直接 KL 型の CMI）の接続**
>
> 既存の P13 の情報論的な条件をそのまま用いながら、谷・軌道の結論を、初期の全 sublevel の等式のない、不変領域の証人へ接続する。

名前空間は `Tomabechi.Theorem22InvariantRegionP13`。`open MeasureTheory`、`open Tomabechi.Theorem21`、`open Tomabechi.Theorem19_22`、`open Tomabechi.Theorem22InvariantRegion`。

---

<a id="Tomabechi.Theorem22InvariantRegionP13.invariantRegion_meanField_stage_theorem21_four_conclusions_directKL"></a>

## 定理 `invariantRegion_meanField_stage_theorem21_four_conclusions_directKL`

### 式

$$\text{不変領域の段階}:\ \text{谷・変位・軌道・指数減衰}\ +\ I_{\text{direct KL}}=H(G\mid X)>0$$

### Lean のコメント（日本語訳）

> 緩和した平均場の段階は、最初の 3 つの定量的な結論と、P13 と同じ、生成された joint の直接の KL 型の CMI の結論を保つ。枝・台・LUB の対応は、明示的なままである。

### 補題の説明

`meanField_invariant_region_stage_conclusions`（InvariantRegion）で第 1〜3 結論、`finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy`（MeasureCMI）で第 4 結論です。

### 証明の概略

1. `chooseInvariantRegionStageWitness`（InvariantRegion）で証人を選び、第 4 結論は `finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy` を適用。

----


## コメント修正記録

（なし）
