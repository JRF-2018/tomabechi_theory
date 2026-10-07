# Tomabechi/Consistency/ConsistencyR1_C3LayerConnection.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR1_C3LayerConnection.lean`](../Tomabechi/Consistency/ConsistencyR1_C3LayerConnection.lean)（元の H-stage の中心・原子の層と、共通束）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

元の H-stage（段階の谷）の**中心と原子の層**を、新しい**共通束**につなぐファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「共通の概念束」（R1）の部品です。

* 元の平均場 H-stage の中心を作る**実数の表象** \(\tfrac{n}{n+1}\) は、共通束の**対角の自然数層**の座標そのものです。
* 各段の平均場の原子が指す自然数の層は、順序を保つ埋め込み `layerAddressEmbedding` で、同じ共通束に送られます。
* スカラーの H-stage を、C1 の二主体モデルと同じ二座標の空間の**対角**に持ち上げます。持ち上げた二次のポテンシャルは、横方向にも曲がっていて（退化していない）、対角の上では元のスカラーの場に一致し、凍結した軌道はそのままベクトル場の解になります。

### 0.2 このファイルが証明していないこと

* 持ち上げは具体的な二次のポテンシャル（係数 \(-\tfrac14\)）による構成です。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 元の平均場 H-stage の中心を作る実数表象は、新しい共通束の対角 Nat 層の座標そのものである。また各段の平均場原子が指す Nat 層は、順序埋込み `layerAddressEmbedding` で同じ共通束へ送られる。

---

<a id="Tomabechi.Consistency.R1.CommonLayerState"></a>

## 定義 `CommonLayerState`

### 式

$$
\mathbb R^2
$$

### Lean のコメント（日本語訳）

> H-stage のスカラーの状態は、C1 の合意モデルが使うのと同じ二座標の空間に、対角に埋め込まれる。

### 定義の説明

H-stage のスカラーの状態を、**対角に**埋め込む先の空間です。C1 の合意モデルが使うのと同じ、二座標の空間 \(\mathbb R^2\)（`Fin 2 → ℝ`）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonDiagonalAgentState"></a>

## 定義 `commonDiagonalAgentState`

### 式

$$
x\mapsto(x,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

スカラー \(x\) を、二つの座標が等しい対角の点 \((x,x)\) に置きます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStagePotential"></a>

## 定義 `liftedHStagePotential`

### 式

$$
-\tfrac14\bigl((x_0-c)^2+(x_1-c)^2\bigr)
$$

### Lean のコメント（日本語訳）

> C3 の層を中心とする、退化していない二座標の二次ポテンシャル。

### 定義の説明

C3 の層を中心とする、**退化していない二座標の二次ポテンシャル**（臨場感の場）です。横方向（対角に垂直な方向）にも曲がっています。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.commonDiagonal_difference_energy"></a>

## 補題 `commonDiagonal_difference_energy`

### 式

$$
\lVert(x,x)-(y,y)\rVert^2=2(x-y)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

対角の二点の差の二乗（二座標の和）は、スカラーの差の二乗の 2 倍です。

### 証明の概略

1. 各座標の差が \(x-y\)。二つ足す。

----

<a id="Tomabechi.Consistency.R1.liftedHStagePotential_on_diagonal"></a>

## 補題 `liftedHStagePotential_on_diagonal`

### 式

$$
\text{対角の上では}\ -\tfrac12(x-c)^2
$$

### Lean のコメント（日本語訳）

> 対角に沿っては、持ち上げた二座標のポテンシャルは、元のスカラーの二次の臨場感の場に、規格化も含めてちょうど等しい。

### 補題の説明

対角の上では、持ち上げた二座標のポテンシャルは、元のスカラーの二次の臨場感の場に、**係数も含めてちょうど**一致します。

### 証明の概略

1. 定義を展開して整理する（`simp`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStagePotential_zero_iff"></a>

## 補題 `liftedHStagePotential_zero_iff`

### 式

$$
\text{ポテンシャル}=0\iff x=(c,c)
$$

### Lean のコメント（日本語訳）

> 持ち上げた臨場感の場は、持ち上げた中心でだけ最大になり、他のどこでもならない。これは、横方向の座標が平らでないことを確かめる。

### 補題の説明

持ち上げた臨場感の場は、持ち上げた中心 \((c,c)\) **だけ**で最大（\(0\)）になります。横方向の座標が平らでないことの確認です。

### 証明の概略

1. （→）二つの二乗の和が 0（非負なので両方 0）。（←）代入して 0。

----

<a id="Tomabechi.Consistency.R1.liftedHStagePotential_second_difference"></a>

## 補題 `liftedHStagePotential_second_difference`

### 式

$$
P(x+v)+P(x-v)-2P(x)=-\tfrac12(v_0^2+v_1^2)
$$

### Lean のコメント（日本語訳）

> 二階差分は、0 でないどの方向でも厳密に負である。したがって、持ち上げた二次式は、両方の座標で一様な曲率を持つ。

### 補題の説明

二階差分は、0 でないどの方向でも**厳密に負**です。したがって、持ち上げた二次式は、**両方の座標で一様な曲率**を持ちます。

### 証明の概略

1. 定義を展開して整理する（`ring`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStagePresenceGradient"></a>

## 定義 `liftedHStagePresenceGradient`

### 式

$$
-\tfrac12(x_i-c)
$$

### Lean のコメント（日本語訳）

> 持ち上げた臨場感の場の、各座標での勾配。

### 定義の説明

持ち上げた臨場感の場の、各座標の勾配です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageEffectiveGradient"></a>

## 定義 `liftedHStageEffectiveGradient`

### 式

$$
\text{有効勾配}=-\text{臨場感の勾配}
$$

### Lean のコメント（日本語訳）

> 有効ポテンシャルは臨場感の場にマイナスをつけたものなので、その勾配は符号が逆である。

### 定義の説明

有効ポテンシャルは臨場感の場の符号を変えたものなので、その勾配は符号が逆です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageMobility"></a>

## 定義 `liftedHStageMobility`

### 式

$$
v\mapsto2v
$$

### Lean のコメント（日本語訳）

> 移動度 2 は、規格化した持ち上げたポテンシャルの係数 1/2 を補い、元の率 1 の対角の力学を保つ。

### 定義の説明

**移動度 2** です。正規化した持ち上げたポテンシャルの係数 \(1/2\) を補い、もとの率 1 の対角の力学を保ちます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageVectorField"></a>

## 定義 `liftedHStageVectorField`

### 式

$$
-\mathrm{mobility}(\text{有効勾配})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

持ち上げた H-stage のベクトル場です。移動度 × 有効勾配の符号を変えたものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageVectorField_formula"></a>

## 補題 `liftedHStageVectorField_formula`

### 式

$$
F(x)_i=-(x_i-c)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げたベクトル場は、各座標で \(-(x_i-c)\)（中心への率 1 の縮み）です。

### 証明の概略

1. 定義を展開して整理する（`simp`）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageOrbit"></a>

## 定義 `liftedHStageOrbit`

### 式

$$
t\mapsto(\text{frozen orbit}(t),\text{frozen orbit}(t))
$$

### Lean のコメント（日本語訳）

> 元の厳密なスカラーの凍結した軌道を、対角に持ち上げたものは、すべての実時刻で、二座標の完全なベクトル場を解く。

### 定義の説明

元の厳密なスカラーの**凍結した軌道**を、対角に持ち上げたものです。これは、すべての実時刻で、二座標の完全なベクトル場の解です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R1.liftedHStageOrbit_hasDerivAt"></a>

## 補題 `liftedHStageOrbit_hasDerivAt`

### 式

$$
\frac{d}{dt}\text{orbit}=F(\text{orbit})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

持ち上げた軌道は、すべての実時刻で、持ち上げたベクトル場の解です。

### 証明の概略

1. 各座標で、スカラーの凍結した軌道の微分の補題（`hasDerivAt_quadraticFrozenOrbit`）を使う。

----

<a id="Tomabechi.Consistency.R1.representation_eq_commonDiagonal_coordinate"></a>

## 補題 `representation_eq_commonDiagonal_coordinate`

### 式

$$
\mathrm{rep}(n)=\text{対角層 }n\text{ の第 1 座標}
$$

### Lean のコメント（日本語訳）

> C3のスカラー表象は、共通束の対角層の第一座標に一致する。

### 補題の説明

C3 のスカラーの表象 \(\tfrac{n}{n+1}\) は、共通束の対角の層 \(n\) の第 1 座標に一致します。

### 証明の概略

1. 両方の定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.R1.hStageSequence_center_eq_commonDiagonal_coordinate"></a>

## 補題 `hStageSequence_center_eq_commonDiagonal_coordinate`

### 式

$$
\text{center}_n=\text{対角層 }(n+1)\text{ の第 1 座標}
$$

### Lean のコメント（日本語訳）

> 元H-stageの中心値は、共通束の対応Nat層の第一座標である。

### 補題の説明

元の H-stage の中心の値は、共通束の対応する自然数の層の第 1 座標です。

### 証明の概略

1. 中心は \(\mathrm{rep}(n+1)\)（`hStageSequence_center`）。前の補題。

----

<a id="Tomabechi.Consistency.R1.hStageSequence_atomLayer_commonConcept"></a>

## 補題 `hStageSequence_atomLayer_commonConcept`

### 式

$$
\mathrm{layerAddressEmbedding}(n+1)=\mathrm{diagonalLayer}(n+1)
$$

### Lean のコメント（日本語訳）

> 元H-stageの平均場が読む原子層を、同じ共通束上の層点へ送る。

### 補題の説明

元の H-stage の平均場が読む**原子の層**を、同じ共通束の上の層の点へ送ります。

### 証明の概略

1. `layerAddress_nat`。

----

<a id="Tomabechi.Consistency.R1.hStageSequence_center_matches_embedded_atomLayer"></a>

## 補題 `hStageSequence_center_matches_embedded_atomLayer`

### 式

$$
\text{center}_n=\text{埋め込んだ原子層の第 1 座標}
$$

### Lean のコメント（日本語訳）

> H-stage中心のスカラーと、埋め込まれた原子層の座標は一致する。

### 補題の説明

H-stage の中心のスカラーと、埋め込まれた原子の層の座標は一致します。

### 証明の概略

1. 前の二つの補題を合わせる。

----

<a id="Tomabechi.Consistency.R1.hStageSequence_meanField_matches_liftedPotential"></a>

## 補題 `hStageSequence_meanField_matches_liftedPotential`

### 式

$$
\text{meanField}(x)=P_{\text{lifted}}((x,x))
$$

### Lean のコメント（日本語訳）

> 元の H-stage の平均場は、対角の状態に制限すると、持ち上げた二次のポテンシャルにちょうど一致する。

### 補題の説明

元の H-stage の平均場は、対角の状態に制限すると、持ち上げた二次のポテンシャルに**ちょうど一致**します。

### 証明の概略

1. 平均場は積分表示で \(-\tfrac12(x-c)^2\)（`averagePresentation_integral`）。前に示した、対角の上のポテンシャルの式と比べる。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
