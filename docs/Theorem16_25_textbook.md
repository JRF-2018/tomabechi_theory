# Theorem16_25.lean 解説

> 対象: [`Theorem16_25.lean`](../Theorem16_25.lean)（定理16・25の入口）。このファイルには宣言がなく、`import` と `#print axioms`（公理の監査）だけです。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 無我（定理25） | 関係記述を超えて独立・固定・個体化する「自性」が存在しないこと。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 縮小写像 | \(d(Fx,Fy)\le L\,d(x,y)\)（\(L<1\)）をみたす写像。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| `sorry` | 証明が未完であることを示す Lean の記号。本プロジェクトでは残さない方針。 |
| `#print axioms` | その定理が依存する公理を表示する検査命令。標準の 3 公理だけならよい。 |
| 標準公理 | `propext`, `Classical.choice`, `Quot.sound`。Mathlib の数学が使う標準的な公理。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem16_25_Core.lean`（定理16・25の依存コア）と `Theorem16_25_Model.lean`（具体モデル）を読み込み、主要な定理について `#print axioms` で、**標準公理だけを使っている**ことを確認する入口ファイルです。

### 0.2 読み込むファイルと解説書

| ファイル | 内容 | 解説書 |
| --- | --- | --- |
| `Theorem16_25_Core.lean` | 逆極限・固定点・縮小写像・無我の論理核 | [解説](Theorem16_25_Core_textbook.md) |
| `Theorem16_25_Model.lean` | 具体モデル（1 次元の例など） | 後続の解説書で扱う |

### 0.3 公理の監査

`#print axioms` は、定理が依存する公理を表示します。このプロジェクトでは `propext`、`Classical.choice`、`Quot.sound` の**標準公理のみ**で、`sorry` に由来する `sorryAx` が現れないことを確認します。対象は、`theorem16_represented_fixedPoint_of_continuous_inverseLimitMap`、`history_represented_fixedPoints_of_equivariance`、`contraction_iterates_dist_le_initial_fixedPoint`、`represented_unique_fixedPoint_and_geometricIterates_of_contraction`、`history_fixedPoints_geometric_and_represented`、`theorem16_25_geometricRepresentation_conditionalProofCore`、`historyContinuousInverseLimit_fixedPoints_data`、`historyFixedPointsOfCarrierContractions`、`theorem16HistoryLayerSystem_to_theorem25_fullConnection` です。

### 0.4 このファイルが証明していないこと

何も証明していません。上の定理の内容と条件は `Theorem16_25_Core` の解説書を参照してください。

## コメント修正記録

（なし）
