# Tomabechi/Information/MeanFieldDirectCMI.lean 解説

> 対象: [`Tomabechi/Information/MeanFieldDirectCMI.lean`](../Tomabechi/Information/MeanFieldDirectCMI.lean)（定理21の第4結論：生成jointの直接KL型CMIへの接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| KL ダイバージェンス | 2 つの確率分布の「差」を測る量（相対エントロピー）。 |
| 標準 Borel 空間 | 測度論でよい性質（可測な逆写像など）をもつ空間。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理21の**四つの結論**（谷・変位/停留・指数軌道・情報容量）のうち、**第 4 結論（情報容量）**を、**同じ入力法則・質量・行動から生成した同時法則の直接の KL 型 CMI** で述べる版です。`StageData.lean` の `meanField_stage_theorem21_four_conclusions`（第 4 結論は `Theorem21` 系のエントロピー差による CMI）に対し、`MeasureCMI.lean` の測度論的な CMI（KL ダイバージェンス）で言い直します。第 1〜3 結論は変えません。

### 0.2 このファイルが証明していないこと

- 情報容量は谷の力学とは**独立の入力**（入力分布 \(\mu\)、行動・目標の質量、行動の a.e. 単射性、入力エントロピーが正）から得ます。谷の力学から推論しません。
- ゴールは**有限離散**、出力空間は標準 Borel（`StandardBorelSpace Y`）を仮定します。
- 枝（branch）・台・LUB の対応は、結果の一部として引き続き**仮定**です。

### 0.3 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理21の第 4 結論：生成した joint の、直接の KL 型 CMI への接続**
>
> 定理22の平均場の段階の入力から得られる、谷・変位・指数軌道の 3 つの結論を保ち、第 4 の結論だけを、同じ `μ/mass/action` が生成する joint の、直接の KL 型 CMI で返す。joint、事前の核、条件付きのエントロピーは、別の法則に置き換えず、`Theorem19_22` の生成・disintegration の同定を通じて一致させる。

名前空間は `Tomabechi.Theorem22`。`open MeasureTheory`、`open Tomabechi.Theorem21`、`open Tomabechi.Theorem19_22`。

---

<a id="Tomabechi.Theorem22.meanField_stage_theorem21_four_conclusions_directKL"></a>

## 定理 `meanField_stage_theorem21_four_conclusions_directKL`

### 式

$$\text{谷・変位/停留・指数軌道}\ +\ I_{\text{direct KL}}(G;Y\mid X)=H(G\mid X)>0$$

### Lean のコメント（日本語訳）

> 1 つの平均場の段階についての、定理21の 4 つの結論のグループ。第 4 のグループは、同じ入力の法則・ゴールの質量・行動から生成された joint の、直接の KL 型の条件付き相互情報量を使って表す。段階の枝・台・LUB の対応は、結果の一部として残る。

### 補題の説明

第 1〜3 結論は `meanField_stage_theorem21_four_conclusions`（StageData）から、第 4 結論は `finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy`（MeasureCMI）から得ます。

### 証明の概略

1. `meanField_stage_theorem21_four_conclusions`（StageData）で第 1〜3 結論（第 4 は使わない）。
2. `finiteGoalActionGeneratedJoint_directCMI_eq_conditionalEntropy` で、生成した同時法則の直接 CMI が \(H(G|X)\) に等しく正であること。枝への所属は仮定をそのまま添える。

----


## コメント修正記録

（なし）
