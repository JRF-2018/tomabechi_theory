# Theorem21.lean 解説

> 対象: [`Theorem21.lean`](../Theorem21.lean)（定理21の互換入口）。このファイルには宣言がなく、他のファイルを再輸出するだけです。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 自由意思容量 | ゴール条件付きの制御が運べる情報量の上限（定理19）。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 条件付きエントロピー | \(H(G\mid X)\)。\(X\) を知った後に残る \(G\) の不確かさ。 |
| 相互情報量・CMI | \(I(G;Y\mid X)\)。\(Y\) から \(G\) について分かる量（\(X\) を知ったうえで）。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

`Theorem21.lean` は、かつて 1 つの大きなファイルだった定理21の形式化を、複数のファイルに分けたあとに残した**互換入口**です。
`import Theorem21` と書けば、分割された次のファイルがすべて読み込まれ、従来と同じ宣言名（`Tomabechi.Theorem21.…`）が使えます。

### 0.2 読み込むファイルと、その解説書

| ファイル | 内容 | 解説書 |
| --- | --- | --- |
| `Theorem1.lean` | 定理1（指数収束の基礎） | [Theorem1_textbook.md](Theorem1_textbook.md) |
| `Tomabechi/Information/FiniteCMI.lean` | 有限の条件付き相互情報量 | [解説](Tomabechi_Information_FiniteCMI_textbook.md) |
| `Tomabechi/Information/FiniteMeasureEntropy.lean` | 有限目標の条件付きエントロピーの測度論的基礎 | [解説](Tomabechi_Information_FiniteMeasureEntropy_textbook.md) |
| `Tomabechi/Information/DeterministicOutput.lean` | 決定論的出力の情報容量 | [解説](Tomabechi_Information_DeterministicOutput_textbook.md) |
| `Tomabechi/Dynamics/MeanFieldReconstruction.lean` | 分岐の支持と有限・積分の平均場カーネル | [解説](Tomabechi_Dynamics_MeanFieldReconstruction_textbook.md) |
| `Tomabechi/Analysis/StrongConvexity.lean` | 強凸性と最小点 | [解説](Tomabechi_Analysis_StrongConvexity_textbook.md) |
| `Tomabechi/Dynamics/GradientFlow.lean` | 勾配流の散逸・局所存在・延長 | [解説](Tomabechi_Dynamics_GradientFlow_textbook.md) |
| `Tomabechi/Dynamics/GlobalFlow.lean` | 閾値条件のもとでの大域存在・指数減衰 | [解説](Tomabechi_Dynamics_GlobalFlow_textbook.md) |
| `Tomabechi/Dynamics/Theorem21GlobalResults.lean` | 定理21の四つの結論のまとめ | [解説](Tomabechi_Dynamics_Theorem21GlobalResults_textbook.md) |

### 0.3 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理21の互換入口。有限情報核・強凸最適化・ODE・大域結論を再輸出する。

（もとのコメントが日本語なのでそのまま写しています。）名前空間 `Tomabechi.Theorem21` を開いて閉じるだけで、**宣言は 1 つもありません**。

### 0.4 このファイルが証明していないこと

何も証明していません。定理21の内容は、上の表のファイルにあります。

## コメント修正記録

（なし）
