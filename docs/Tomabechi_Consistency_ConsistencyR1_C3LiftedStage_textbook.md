# Tomabechi/Consistency/ConsistencyR1_C3LiftedStage.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C3LiftedStage.lean`](../Tomabechi/Consistency/ConsistencyR1_C3LiftedStage.lean)（R1: 横方向にも曲率を持つ二次H-stage）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| Grönwall の不等式 | 微分不等式 \(\phi'\le K\phi\) から \(\phi(t)\le\phi(t_0)e^{K(t-t_0)}\) を導く標準的な道具。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 完備束 | 任意の部分集合に上限・下限がある束。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**横方向にも曲率を持つ、二次の H-stage** を作るファイルです。既存の H-stage のスカラーの平均場を、対角の上で保ちながら、二次元 Euclid 空間の**両方向**に負の曲率を持つ平均場の入力を作ります。段の原子の法則は、対応する共通束の層の Dirac 測度で、しきい値・初期の部分準位・障壁・移動度も、入力のレコードに含めます。

* スカラーの値 \(c\) は、対角の点 \((c/\sqrt2,\,c/\sqrt2)\) に持ち上げます（`liftedStageCenter`）。この持ち上げは**等長**で、**閉埋め込み**です。
* 持ち上げた平均場は \(S_c(x)=-\tfrac12\|x-\mathrm{center}(c)\|^2\)（二次元の両方向に負の曲率）、移動度は恒等です。
* 元のスカラーの段の、軌道・谷の最小点・TCZ・接合軌道・端点の誤差が、すべて持ち上げで**ちょうど保たれる**ことを示します。
* 共通束の各点に、射影した層の段の入力と TCZ を割り当てます（`commonConceptHStageInput`・`commonConceptHStageTCZ`）。

### 0.2 このファイルが証明していないこと

* 横方向の曲率は、**二次式の平均場**（\(-\tfrac12\|x-c\|^2\)）の場合の構成です。一般の平均場の場合は扱いません。
* 旧い頂の住所には有限の H-stage がないので、そこに段 0 を割り当てる**全域への拡張**を使っています。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 既存H-stageのスカラー平均場を対角上で保ちながら、二次元Euclidean空間の両方向に負の曲率を持つ平均場入力を作る。段の原子法則は対応する共通束層のDirac lawであり、しきい値・初期sublevel・障壁・移動度も入力recordに含める。

---

<a id="Tomabechi.Consistency.R1.LiftedStageState"></a>

## 定義 `LiftedStageState`

### 式

$$
\mathbb R^2\ \text{（Euclid 空間）}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

持ち上げた段の状態空間です。二次元の Euclid 空間 \(\mathbb R^2\)（定理 20 と同じ空間）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.LiftedStageAtom"></a>

## 定義 `LiftedStageAtom`

### 式

$$
\text{共通束の原子の型}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段の原子の型です（C3 の原子と同じ）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter"></a>

## 定義 `liftedStageCenter`

### 式

$$
\mathrm{center}(c)=\bigl(\tfrac c{\sqrt2},\tfrac c{\sqrt2}\bigr)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

スカラーの中心 \(c\) を、対角の点 \((c/\sqrt2,\,c/\sqrt2)\) に持ち上げる写像です。スカラーの差 \(|x-y|\) が、持ち上げた点の距離になります（等長）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageMeanField"></a>

## 定義 `liftedStageMeanField`

### 式

$$
S_c(x)=-\tfrac12\|x-\mathrm{center}(c)\|^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

持ち上げた平均場 \(S_c(x)=-\tfrac12\|x-\mathrm{center}(c)\|^2\) です。二次元の**両方向**に負の曲率を持ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_difference_norm_sq"></a>

## 補題 `liftedStageCenter_difference_norm_sq`

### 式

$$
\|\mathrm{center}(x)-\mathrm{center}(y)\|^2=(x-y)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた中心の差の二乗ノルムは、スカラーの差の二乗です。

### 証明の概略

1. Euclid ノルムの二乗を展開し、\((\sqrt2)^2=2\) で整理する。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_difference_norm"></a>

## 補題 `liftedStageCenter_difference_norm`

### 式

$$
\|\mathrm{center}(x)-\mathrm{center}(y)\|=|x-y|
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた中心の差のノルムは、スカラーの差の絶対値です。

### 証明の概略

1. 二乗の等式と、非負性から平方根を取る（`nlinarith`）。

----

<a id="Tomabechi.Consistency.R1.liftedStage_closedBall_mem_iff"></a>

## 補題 `liftedStage_closedBall_mem_iff`

### 式

$$
\mathrm{center}(x)\in\bar B(\mathrm{center}(c),\|\mathrm{center}(x_0)-\mathrm{center}(c)\|)\iff x\in\bar B(c,|x_0-c|)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉球の所属は、対角の持ち上げで保たれます。

### 証明の概略

1. 距離を `liftedStageCenter_difference_norm` で書き換える。

----

<a id="Tomabechi.Consistency.R1.liftedStageMeanFieldGradient"></a>

## 定義 `liftedStageMeanFieldGradient`

### 式

$$
\nabla S_c(x)=-(x-\mathrm{center}(c))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

持ち上げた平均場の勾配です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageMeanFieldHessian"></a>

## 定義 `liftedStageMeanFieldHessian`

### 式

$$
\nabla^2S_c=-\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

持ち上げた平均場のヘシアンです（\(-\mathrm{id}\)）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageMobility"></a>

## 定義 `liftedStageMobility`

### 式

$$
M=\mathrm{id}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

移動度は恒等写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit"></a>

## 定義 `liftedStageOrbit`

### 式

$$
x(t)=\mathrm{center}(c)+e^{-(t-s)}(x_0-\mathrm{center}(c))
$$

### Lean のコメント（日本語訳）

> 持ち上げた二次場の、明示的な勾配流の軌道。

### 定義の説明

持ち上げた二次の場の、**明示的な勾配流の軌道**です。中心に指数的に近づきます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit_hasDerivAt"></a>

## 補題 `liftedStageOrbit_hasDerivAt`

### 式

$$
\dot x(t)=-(x(t)-\mathrm{center}(c))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は、\(\dot x=-(x-\mathrm{center}(c))\) を満たします。

### 証明の概略

1. 指数関数の合成関数の微分。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit_distance"></a>

## 補題 `liftedStageOrbit_distance`

### 式

$$
\mathrm{dist}(x(t),\mathrm{center}(c))=e^{-(t-s)}\,\mathrm{dist}(x_0,\mathrm{center}(c))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道の中心への距離は、指数的に減衰します。

### 証明の概略

1. 定義を展開して、ノルムのスカラー倍。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit_mem_closedBall"></a>

## 補題 `liftedStageOrbit_mem_closedBall`

### 式

$$
x_0\in\bar B(\mathrm{center}(c),r),\ s\le t\Rightarrow x(t)\in\bar B(\mathrm{center}(c),r)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は、中心の閉球の中に留まります（前向きに不変）。

### 証明の概略

1. 距離の減衰の式と、\(e^{-(t-s)}\le1\)。

----

<a id="Tomabechi.Consistency.R1.liftedStageAveragePresentation"></a>

## 定義 `liftedStageAveragePresentation`

### 式

$$
\text{二次元の平均化表現（段の LUB 原子での Dirac 測度）}
$$

### Lean のコメント（日本語訳）

> 二次元の平均化表現は、元のH-stageと同じ原子の添字・表現を使い、段のLUB原子でのDirac測度を持つ。

### 定義の説明

二次元の**平均化表現**です。元の H-stage と同じ原子の添字・表現を使い、段の LUB 原子での Dirac 測度を持ちます。

### 証明の概略

1. 定義です。原子の位相を離散、可測構造を最大にして、Dirac 測度が確率測度であること、再構成の核が可積分であることを示して組み立てる。

----

<a id="Tomabechi.Consistency.R1.liftedStageAveragePresentation_integral"></a>

## 補題 `liftedStageAveragePresentation_integral`

### 式

$$
\int(\ldots)\,d\delta=S_{\text{表象}(n+1)}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

平均化表現の積分値は、持ち上げた平均場に一致します。

### 証明の概略

1. Dirac 測度の積分（`integral_dirac`）に帰着する。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput"></a>

## 定義 `liftedHStageInput`

### 式

$$
\text{完全な二次元 H-stage の入力}
$$

### Lean のコメント（日本語訳）

> 完全な二次元H-stageの入力。選ばれた中心と初期状態は、元の段のデータの対角持ち上げ。

### 定義の説明

**完全な二次元の H-stage の入力**です。選ばれた中心と初期状態は、元の段のデータの対角持ち上げです。中心 \(c=\)層 \(n+1\) の表象、初期点 \(x_0\)、半径 \(R=d+1\)（\(d=\|x_0-c\|\)）、利得 1、曲率 1、背景は 0、平均場は `liftedStageMeanField c`、移動度は恒等、部分準位は中心の周りの閉球、開始時刻は `stageTime n` です。各条件（\(C^2\)・勾配の表現・ヘシアンの上界・中心の停留・初期点が部分準位に入る・部分準位の障壁・移動度の強制性・部分準位の等式）を、本文の補題で埋めます。

### 証明の概略

1. 定義です。各条件の証明は、二次式の微分・ノルムの二乗の評価・閉球の性質による。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_orbit_derivative"></a>

## 補題 `liftedHStageInput_orbit_derivative`

### 式

$$
\dot x=-M\,\nabla\!\bigl(\tilde V\bigr)\ \text{（軌道は勾配流の解）}
$$

### Lean のコメント（日本語訳）

> 持ち上げた平均場は、対角部分空間上で、元のH-stageの平均場の厳密な保存をする。

### 補題の説明

持ち上げた平均場は、対角部分空間の上で、元の H-stage の平均場の流れを**そのまま保ちます**。軌道は、入力の移動度と勾配で定まる勾配流の解です。

### 証明の概略

1. 軌道の微分の補題（`liftedStageOrbit_hasDerivAt`）と、移動度・勾配の定義を比べる。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_orbit_forwardInvariant"></a>

## 補題 `liftedHStageInput_orbit_forwardInvariant`

### 式

$$
x_0\in\text{部分準位},\ t\ge\text{開始時刻}\Rightarrow x(t)\in\text{部分準位}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道は、部分準位に留まります（開始時刻以降）。

### 証明の概略

1. 部分準位は中心の閉球。軌道の閉球への前向き不変性（`liftedStageOrbit_mem_closedBall`）。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit_eq_liftedScalarOrbit"></a>

## 補題 `liftedStageOrbit_eq_liftedScalarOrbit`

### 式

$$
\text{持ち上げた軌道}=\text{スカラーの軌道の持ち上げ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角上の点から出発する、持ち上げた軌道は、スカラーの軌道の持ち上げに一致します。

### 証明の概略

1. 座標ごとに計算する（`ext i`）。スカラーの凍結軌道の式と比べる。

----

<a id="Tomabechi.Consistency.R1.liftedHStageValleyWitness"></a>

## 定義 `liftedHStageValleyWitness`

### 式

$$
\text{既存の定理 21/22 の API が選ぶ段の谷の証拠}
$$

### Lean のコメント（日本語訳）

> 既存の定理21/22のAPIで選ばれた段の谷の証拠。

### 定義の説明

既存の定理 21/22 の API で選ばれた、**段の谷の証拠**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageValleyWitness_minimizer_eq_center"></a>

## 補題 `liftedHStageValleyWitness_minimizer_eq_center`

### 式

$$
\text{谷の最小点}=\mathrm{center}(\text{表象}(n+1))
$$

### Lean のコメント（日本語訳）

> 定理21/22で選ばれた最小点は、持ち上げた共有の段の中心にちょうど等しい。これにより、切り替えの核の谷の点を、共通束の住所の表象に同定する。

### 補題の説明

定理 21/22 で選ばれた**最小点**は、持ち上げた共有の段の中心に、ちょうど等しいです。これにより、切り替えの核の谷の点が、共通束の住所の表象に同定されます。

### 証明の概略

1. 最小点の一意性（強凸な有効ポテンシャル）と、中心が停留点であること。

----

<a id="Tomabechi.Consistency.R1.liftedStageOrbit_eq_selectedOrbit"></a>

## 補題 `liftedStageOrbit_eq_selectedOrbit`

### 式

$$
\text{持ち上げた軌道}=\text{選ばれた谷の証拠の軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた軌道は、選ばれた谷の証拠の軌道に一致します（開始時刻以降）。

### 証明の概略

1. 両方が同じ初期値から出発する勾配流の解で、解の一意性（Grönwall の不等式）から一致する。

----

<a id="Tomabechi.Consistency.R1.liftedHStageValleyWitness_orbit_eq_liftedOriginal"></a>

## 補題 `liftedHStageValleyWitness_orbit_eq_liftedOriginal`

### 式

$$
\text{選ばれた軌道}=\mathrm{center}(\text{元のスカラー軌道})
$$

### Lean のコメント（日本語訳）

> 元の各段の前向き時間の範囲で、選ばれた持ち上げた証拠の軌道は、元のスカラーH-stageの証拠の等長な持ち上げ。

### 補題の説明

元の各段の前向きの時間の範囲で、選ばれた持ち上げた証拠の軌道は、元のスカラー H-stage の証拠の**等長な持ち上げ**です。

### 証明の概略

1. 持ち上げた軌道が、スカラーの軌道の持ち上げであること（`liftedStageOrbit_eq_liftedScalarOrbit`）と、各々の選ばれた軌道との一致。

----

<a id="Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory"></a>

## 定義 `liftedHStageStitchedTrajectory`

### 式

$$
\mathrm{center}(\text{元の正典 23-B のスカラーの接合軌道})
$$

### Lean のコメント（日本語訳）

> 正典のスカラー23-Bの軌道を、共通束のH-stage入力と同じ二座標の状態空間へ持ち上げる。

### 定義の説明

正典のスカラー 23-B の軌道を、共通束の H-stage の入力と同じ二座標の状態空間へ**持ち上げた**ものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_eq_stageOrbit"></a>

## 補題 `liftedHStageStitchedTrajectory_eq_stageOrbit`

### 式

$$
t\in[\text{段の滞在区間}]\Rightarrow\ \text{持ち上げた接合軌道}=\text{選ばれた谷の軌道}
$$

### Lean のコメント（日本語訳）

> 切り替えの各滞在区間で、持ち上げた正典の軌道は、その段について選ばれた、持ち上げた定理21/22の谷の軌道である。

### 補題の説明

切り替えの各滞在区間で、持ち上げた正典の軌道は、その段について選ばれた、**持ち上げた定理 21/22 の谷の軌道**です。

### 証明の概略

1. 接合軌道の定義と、元のスカラーの接合軌道が滞在区間で谷の軌道に一致すること（C3 の補題）を、持ち上げて比べる。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_dist"></a>

## 補題 `liftedStageCenter_dist`

### 式

$$
\mathrm{dist}(\mathrm{center}(x),\mathrm{center}(y))=\mathrm{dist}(x,y)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げは、距離を保ちます。

### 証明の概略

1. ノルムの補題から。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_isometry"></a>

## 補題 `liftedStageCenter_isometry`

### 式

$$
\mathrm{center}\text{ は等長写像}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心の持ち上げは、等長写像です。

### 証明の概略

1. 距離の等式を、拡張距離（`edist`）の等式に書き換える。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_isClosedEmbedding"></a>

## 補題 `liftedStageCenter_isClosedEmbedding`

### 式

$$
\mathrm{center}\text{ は閉埋め込み}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心の持ち上げは、閉埋め込みです。

### 証明の概略

1. 等長写像は閉埋め込み（`Isometry.isClosedEmbedding`、完備な定義域）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageReachable_eq_liftedScalarImage"></a>

## 補題 `liftedHStageReachable_eq_liftedScalarImage`

### 式

$$
\overline{\text{持ち上げた軌道の像}}=\mathrm{center}(\overline{\text{元のスカラー到達集合}})
$$

### Lean のコメント（日本語訳）

> 持ち上げた凍結軌道の像の閉包は、元のスカラーの到達集合の閉包の持ち上げにちょうど等しい。閉埋め込みを使うので、閉包によって持ち上げた対角の横断方向の点が加わることはない。

### 補題の説明

持ち上げた凍結軌道の像の閉包は、元のスカラーの到達集合の閉包の持ち上げに、ちょうど等しいです。閉埋め込みを使うので、閉包によって、持ち上げた対角と**横断する方向の点が加わることはありません**。

### 証明の概略

1. 軌道が元のスカラー軌道の持ち上げであること（前の補題）。閉埋め込みは、像の閉包と閉包の像を交換する。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_meanField_on_diagonal"></a>

## 補題 `liftedHStageInput_meanField_on_diagonal`

### 式

$$
\text{持ち上げた平均場}(\mathrm{center}(x))=\text{元のスカラー平均場}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角の上で、持ち上げた平均場は、元のスカラーの平均場に一致します。

### 証明の概略

1. 平均場の定義を展開し、中心の差のノルムの補題。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_effectivePotential_on_diagonal"></a>

## 補題 `liftedHStageInput_effectivePotential_on_diagonal`

### 式

$$
\text{持ち上げた有効ポテンシャル}(\mathrm{center}(x))=\text{元の有効ポテンシャル}(x)
$$

### Lean のコメント（日本語訳）

> 持ち上げた段の有効ポテンシャルとスカラーの段の有効ポテンシャルは、埋め込んだ対角上で、正規化も含めて一致する。

### 補題の説明

持ち上げた段の有効ポテンシャルと、スカラーの段の有効ポテンシャルは、埋め込んだ対角の上で、**正規化も含めて一致**します。

### 証明の概略

1. 有効ポテンシャルの定義を展開し、背景（0）と平均場の一致を使う。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_radius_eq_scalar"></a>

## 補題 `liftedHStageInput_radius_eq_scalar`

### 式

$$
\text{持ち上げた半径}=\text{元のスカラーの半径}
$$

### Lean のコメント（日本語訳）

> 持ち上げたH-stageの半径は、元のスカラーの段の半径と同じ。どちらでも、等長な初期変位に1を加えて作られている。

### 補題の説明

持ち上げた H-stage の半径は、元のスカラーの段の半径と同じです。どちらでも、等長な初期変位に 1 を加えて作られています。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_center_eq_lifted_scalar"></a>

## 補題 `liftedHStageInput_center_eq_lifted_scalar`

### 式

$$
\text{持ち上げた中心}=\mathrm{center}(\text{元のスカラーの中心})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた段の中心は、元のスカラーの段の中心の持ち上げです。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Consistency.R1.liftedStageCenter_closedBall_mem_iff"></a>

## 補題 `liftedStageCenter_closedBall_mem_iff`

### 式

$$
\mathrm{center}(x)\in\bar B(\mathrm{center}(c),r)\iff x\in\bar B(c,r)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉球の所属は、持ち上げで保たれます（半径 \(r\) が任意の場合）。

### 証明の概略

1. 距離の保存（`liftedStageCenter_dist`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageValleyWitness_minimizer_eq_lifted_scalar"></a>

## 補題 `liftedHStageValleyWitness_minimizer_eq_lifted_scalar`

### 式

$$
\text{持ち上げた谷の最小点}=\mathrm{center}(\text{元の谷の最小点})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた段の谷の最小点は、元のスカラーの谷の最小点の持ち上げです。

### 証明の概略

1. 両方が中心に等しいこと（最小点の補題）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageTCZ"></a>

## 定義 `liftedHStageTCZ`

### 式

$$
\mathrm{TCZ}^{\rm lift}_n\ \text{（持ち上げた段入力から作る 23-B の TCZ）}
$$

### Lean のコメント（日本語訳）

> 持ち上げたH-stageの入力から作った23-BのTCZ。同じ段の閾値と、選ばれた持ち上げた軌道の像の閉包を使う。

### 定義の説明

持ち上げた H-stage の入力から作った、23-B の **TCZ** です。同じ段の閾値と、選ばれた持ち上げた軌道の像の閉包を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageTCZ_eq_lifted_scalar_image"></a>

## 補題 `liftedHStageTCZ_eq_lifted_scalar_image`

### 式

$$
\mathrm{TCZ}^{\rm lift}_n=\mathrm{center}(\mathrm{TCZ}_n)
$$

### Lean のコメント（日本語訳）

> 完全な23-Bの段のTCZは、到達閉包の成分だけでなく、持ち上げた対角の等長写像で保たれる。

### 補題の説明

完全な 23-B の段の TCZ は、到達閉包の成分だけでなく、**持ち上げた対角の等長写像で保たれます**。

### 証明の概略

1. 両方向の包含を、要素ごとに示す。有効ポテンシャルの閾値条件（対角で一致）と、到達閉包（`liftedHStageReachable_eq_liftedScalarImage`）の成分を比べる。

----

<a id="Tomabechi.Consistency.R1.liftedHStageTCZ_closed"></a>

## 補題 `liftedHStageTCZ_closed`

### 式

$$
\mathrm{TCZ}^{\rm lift}_n\ \text{は閉}
$$

### Lean のコメント（日本語訳）

> スカラーの段のTCZの閉性は、対角の段中心写像が閉埋め込みなので、持ち上げた像へ移る。

### 補題の説明

スカラーの段の TCZ の閉性は、対角の段の中心の写像が閉埋め込みなので、持ち上げた像へ移ります。

### 証明の概略

1. 前の補題で像の形にし、閉埋め込みによる像の閉性の同値を使う。

----

<a id="Tomabechi.Consistency.R1.liftedHStageTCZ_nonempty"></a>

## 補題 `liftedHStageTCZ_nonempty`

### 式

$$
\mathrm{TCZ}^{\rm lift}_n\ne\emptyset
$$

### Lean のコメント（日本語訳）

> 元の各段のTCZの非空性は、持ち上げたTCZへ移る。

### 補題の説明

元の各段の TCZ が空でないことは、持ち上げた TCZ へ移ります。

### 証明の概略

1. 像の形にして、元の非空性の像。

----

<a id="Tomabechi.Consistency.R1.liftedHStageTCZ_adjacent_distinct"></a>

## 補題 `liftedHStageTCZ_adjacent_distinct`

### 式

$$
\mathrm{TCZ}^{\rm lift}_{n+1}\ne\mathrm{TCZ}^{\rm lift}_n
$$

### Lean のコメント（日本語訳）

> 隣り合う持ち上げた段のTCZは、持ち上げが単射なので、異なるままである。

### 補題の説明

隣り合う持ち上げた段の TCZ は、持ち上げが単射なので、**異なるまま**です。

### 証明の概略

1. 等しいと仮定して、像の等式に直し、持ち上げの単射性で元のスカラーの TCZ が等しいことになり、矛盾。

----

<a id="Tomabechi.Consistency.R1.liftedHStageValleyWitness_adjacent_minimizers_separated"></a>

## 補題 `liftedHStageValleyWitness_adjacent_minimizers_separated`

### 式

$$
0<\mathrm{dist}(\text{最小点}_{n+1},\text{最小点}_n)
$$

### Lean のコメント（日本語訳）

> 隣り合うスカラーの谷の最小点の正の分離は、等長な段の中心の持ち上げにより、ちょうど保たれる。

### 補題の説明

隣り合う谷の最小点が、正の距離だけ離れていることは、等長な段の中心の持ち上げにより、ちょうど保たれます。

### 証明の概略

1. 最小点を持ち上げた中心に書き換え、距離の保存と、元のスカラーの正の分離。

----

<a id="Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_covers_every_finite_time"></a>

## 補題 `liftedHStageStitchedTrajectory_covers_every_finite_time`

### 式

$$
\forall t\ge t_0,\ \exists n,\ t\in[\text{段 }n\text{ の滞在区間}]
$$

### Lean のコメント（日本語訳）

> 持ち上げた経路は、あらゆる有限の開始時刻の後で、選ばれた持ち上げた谷の軌道を、滞在区間の全体にわたって通る。

### 補題の説明

持ち上げた経路は、あらゆる有限の時刻の後で、選ばれた持ち上げた谷の軌道を、**滞在区間の全体にわたって**通ります。

### 証明の概略

1. 元の接合軌道が、任意の有限時刻をいずれかの滞在区間に含むこと（C3 の補題）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_eq_lifted_scalar"></a>

## 補題 `liftedHStageStitchedTrajectory_eq_lifted_scalar`

### 式

$$
\text{持ち上げた接合軌道}=\mathrm{center}(\text{元のスカラーの接合軌道})\ (t\ge t_0)
$$

### Lean のコメント（日本語訳）

> あらゆる有限の前向き時刻で、選ばれた持ち上げた切り替えの経路は、元の正典のスカラーの接合経路の等長像である。

### 補題の説明

あらゆる有限の前向きの時刻で、選ばれた持ち上げた切り替えの経路は、元の正典のスカラーの接合経路の**等長な像**です。

### 証明の概略

1. 有限時刻を含む滞在区間の段 \(n\) を取る（前の補題）。その区間で、持ち上げた接合軌道は選ばれた谷の軌道に等しく（`liftedHStageStitchedTrajectory_eq_stageOrbit`）、それは元のスカラーの谷の軌道の持ち上げ（`liftedHStageValleyWitness_orbit_eq_liftedOriginal`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageStitchedTrajectory_endpoint_error"></a>

## 補題 `liftedHStageStitchedTrajectory_endpoint_error`

### 式

$$
\mathrm{dist}(\text{段の終点},\text{最小点})\le\varepsilon_n
$$

### Lean のコメント（日本語訳）

> 元の端点の許容誤差は、持ち上げた段で選ばれた最小点に対して測っても、等長な持ち上げでちょうど保たれる。

### 補題の説明

元の端点の許容誤差は、持ち上げた段で選ばれた最小点に対して測っても、等長な持ち上げで**ちょうど保たれます**。

### 証明の概略

1. C3 の証明書（`stitched_dwell_and_endpoint_error`）の元のスカラーの誤差の評価を、持ち上げて、距離の保存で比べる。

----

<a id="Tomabechi.Consistency.R1.liftedStageSelectedOrbit_distance"></a>

## 補題 `liftedStageSelectedOrbit_distance`

### 式

$$
\mathrm{dist}(\text{選ばれた軌道},\text{中心})=e^{-(t-s)}\,\mathrm{dist}(x_0,\text{中心})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選ばれた谷の証拠の軌道の、中心への距離は、指数的に減衰します。

### 証明の概略

1. 選ばれた軌道が持ち上げた軌道に等しいこと（`liftedStageOrbit_eq_selectedOrbit`）と、軌道の距離の式。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_selected_transition"></a>

## 補題 `liftedHStageInput_selected_transition`

### 式

$$
\text{段 }n+1\text{ の初期点}=\text{段 }n\text{ の選ばれた軌道の滞在区間の終点}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期点は、前の段の選ばれた軌道の、滞在区間の終点に等しいです。

### 証明の概略

1. 元のスカラーの段の接続の補題（C3）を持ち上げて、指数の計算（`stageDuration` の式）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageDataOnOldAddress"></a>

## 定義 `liftedHStageDataOnOldAddress`

### 式

$$
\text{旧住所}\ a\ \mapsto\ \text{段 }a\text{ の持ち上げた入力（}\top\mapsto\text{段 0）}
$$

### Lean のコメント（日本語訳）

> 住所添字のH-stageデータ。元の列では、旧い頂のアドレスに有限のH-stageはないので、この全域への拡張は、そこに段0を割り当てる。以下の共通束の族は、格子射影を使う。

### 定義の説明

**住所で添字づけた H-stage のデータ**です。元の段の列では、旧い頂の住所には有限の H-stage がないので、この全域への拡張は、そこに段 0 を割り当てます。以下の共通束の族は、格子の射影を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput"></a>

## 定義 `commonConceptHStageInput`

### 式

$$
\text{共通束の各点 }x\mapsto\text{H-stage の入力}
$$

### Lean のコメント（日本語訳）

> 完全なH-stageの入力は、共有の完備束の各点に、住所で添字づけた段のデータを引き戻すことで割り当てられる。

### 定義の説明

完全な H-stage の入力は、共有の完備束の各点に、住所で添字づけた段のデータを**引き戻す**ことで割り当てられます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_eq_projected"></a>

## 補題 `commonConceptHStageInput_eq_projected`

### 式

$$
\text{入力}(x)=\text{入力データ}(\mathrm{layerProjection}(x))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の点での入力は、格子射影した住所での入力データに等しいです。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_at_properPoint"></a>

## 補題 `commonConceptHStageInput_at_properPoint`

### 式

$$
x<\top\Rightarrow\text{入力}(x)=\text{段 }(\mathrm{layerProjection}\,x)\text{ の入力}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

頂より真に下の点では、入力は、射影した層の段の入力です。

### 証明の概略

1. 射影が頂でないこと（`layerProjection_lt_top_of_lt_top`）で場合分け。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_center"></a>

## 補題 `commonConceptHStageInput_center`

### 式

$$
\text{中心}(x)=\mathrm{center}(\text{表象}(\mathrm{layerProjection}\,x+1))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の点での段の中心は、射影した層の次の層の表象の持ち上げです。

### 証明の概略

1. 入力が射影した住所のデータであること（前の補題）。中心の定義。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_at_oldAddress"></a>

## 補題 `commonConceptHStageInput_at_oldAddress`

### 式

$$
\text{入力}(\iota(a))=\text{入力データ}(a)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

旧い住所の埋め込みでは、入力は、住所の入力データに一致します。

### 証明の概略

1. 拡張の補題（`extendLayerData_on_oldAddress`）。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_at_finiteAddress"></a>

## 補題 `commonConceptHStageInput_at_finiteAddress`

### 式

$$
\text{入力}(\iota(n))=\text{段 }n\text{ の入力}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有限の旧い住所では、入力は、元の段の入力です。

### 証明の概略

1. 前の補題。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageInput_at_top"></a>

## 補題 `commonConceptHStageInput_at_top`

### 式

$$
\text{入力}(\top)=\text{段 0 の入力}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の頂では、入力は段 0 の入力です。

### 証明の概略

1. 頂の射影が旧い頂になること（`layerAddressEmbedding` の補題）。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageTCZ"></a>

## 定義 `commonConceptHStageTCZ`

### 式

$$
\mathrm{TCZ}^{\rm lift}_{\mathrm{layerProjection}(x)}
$$

### Lean のコメント（日本語訳）

> 共通束の点に割り当てられる、持ち上げた切り替え領域は、同じ格子射影で選ばれた添字での段のTCZである。

### 定義の説明

共通束の点に割り当てられる、持ち上げた**切り替え領域**です。同じ格子射影で選ばれた添字での段の TCZ です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageTCZ_eq_projected"></a>

## 補題 `commonConceptHStageTCZ_eq_projected`

### 式

$$
\mathrm{TCZ}(x)=\mathrm{TCZ}^{\rm lift}_{\mathrm{layerProjection}\,x}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通束の点での TCZ は、射影した添字の持ち上げた TCZ に等しいです。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageTCZ_at_oldAddress"></a>

## 補題 `commonConceptHStageTCZ_at_oldAddress`

### 式

$$
\mathrm{TCZ}(\iota(a))=\mathrm{TCZ}^{\rm lift}_a
$$

### Lean のコメント（日本語訳）

> 埋め込んだすべての旧住所で、H-stageのTCZは、対応する共通束のH-stage入力と同じ旧層の添字を使う。

### 補題の説明

埋め込んだすべての旧い住所で、H-stage の TCZ は、対応する共通束の H-stage の入力と、同じ旧層の添字を使います。

### 証明の概略

1. 射影が旧い住所を戻すこと。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageTCZ_at_top"></a>

## 補題 `commonConceptHStageTCZ_at_top`

### 式

$$
\mathrm{TCZ}(\top)=\mathrm{TCZ}^{\rm lift}_0
$$

### Lean のコメント（日本語訳）

> 格子の頂には、初期の持ち上げたH-stageのTCZが割り当てられる。

### 補題の説明

格子の頂には、**初期の**（段 0 の）持ち上げた TCZ が割り当てられます。

### 証明の概略

1. 頂の射影の補題。

----

<a id="Tomabechi.Consistency.R1.commonConceptHStageTCZ_closed_nonempty"></a>

## 補題 `commonConceptHStageTCZ_closed_nonempty`

### 式

$$
\mathrm{TCZ}(x)\ \text{は閉かつ非空}
$$

### Lean のコメント（日本語訳）

> 共通束のすべての点は、閉かつ非空の持ち上げた段のTCZを受け取る。射影した添字のH-stageがそれらの性質を持つため。

### 補題の説明

共通束の**すべての点**は、閉かつ空でない、持ち上げた段の TCZ を受け取ります。射影した添字の H-stage がそれらの性質を持つためです。

### 証明の概略

1. 射影した添字の持ち上げた TCZ の閉性と非空性（`liftedHStageTCZ_closed`・`liftedHStageTCZ_nonempty`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageInput_diagonal_sublevel"></a>

## 補題 `liftedHStageInput_diagonal_sublevel`

### 式

$$
\mathrm{center}(x)\in\text{部分準位}\iff x\in\text{元のスカラー部分準位}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角の点 \(\mathrm{center}(x)\) が部分準位に入ることは、\(x\) が元のスカラーの部分準位に入ることと同値です。

### 証明の概略

1. 閉球の所属の補題（`liftedStage_closedBall_mem_iff`）。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
