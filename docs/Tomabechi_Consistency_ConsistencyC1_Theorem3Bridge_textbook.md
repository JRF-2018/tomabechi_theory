# Tomabechi/Consistency/ConsistencyC1_Theorem3Bridge.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_Theorem3Bridge.lean`](../Tomabechi/Consistency/ConsistencyC1_Theorem3Bridge.lean)（率 3 の合意の流れでの定理3（共有 TCZ・LUB への収束））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 下降条件 | 微分不等式 \(\frac{d}{dt}\Phi\le-2c\Phi\)（\(c>0\)）。\(\Phi\) が指数的に減ることを保証する。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| はさみうちの原理 | 0 以上で、0 に収束するものに抑えられた量は 0 に収束する。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 順序埋め込み | 順序を保ち、かつ反映する単射 \(\iota\)。束を実数ベクトル空間などへ埋め込む。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

二主体の合意の流れ（率 3）に、**定理3**（共有 TCZ と LUB への収束）を適用するファイルです。二つの物理座標が、そのまま抽象的な共有系の二人の主体になります。平均が 0 の「不変なスライス」の上で、二人は、(1) 物理的な合意の対角線と、(2) 抽象的な LUB（束の最小元）の両方に、同じ率 3 で近づきます。初期の食い違いは 0 ではないので、結論は自明ではありません。

| 内容 | 宣言 |
| --- | --- |
| 抽象的な共有系をモデルの上に作る | `c1Theorem3System` |
| 本来の目標集合（完全な \(\Phi_3\) の零点集合）は原点だけ | `c1Theorem3OriginalTCZ_eq_singleton` |
| 零平均の軌道で \(\Phi_3=\tfrac98\Phi_2\) | `c1Theorem3Potential_eq_of_zeroMean` |
| 非自明な初期点 | `c1Theorem3NontrivialInitial` |
| 定量的な結論と 0 への収束 | `c1Theorem3_rate3_quantitative`、`c1Theorem3_original_phi3_bound`、`c1Theorem3_original_phi3_tendsto` |

### 0.2 このファイルが証明していないこと

* 結論は、**平均が 0 の初期点（零平均のスライス）**に限ります。これは、定理3の目標が空でない初期点が、このモデルでは零平均の点に限られるためです（`Φ₃` の零点は原点だけ）。
* 状態は箱の中に限ります。

### 0.3 ファイル冒頭のコメント（日本語訳）

> **率 3 の合意の流れでの定理3。** 二つの物理座標は、抽象的な共有系の二人の主体でもある。不変な零平均のスライスの上で、二人の主体は、同じ率 3 の流れのもとで、束の最小元（LUB）と、物理的な合意の対角線の両方に近づく。初期の食い違いは 0 でなくてよいので、二つの結論はどちらも自明ではない。

---

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.C1Concept"></a>

## 定義 `C1Concept`

### 式

$$
[0,1]^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

このファイルで使う概念の型は、共通の概念束 `CommonConcept`（\([0,1]^2\)）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.clippedMagnitude"></a>

## 定義 `clippedMagnitude`

### 式

$$
x\mapsto\min(|x|,1)\in[0,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

実数の状態の大きさ \(\lvert x\rvert\) を、1 で打ち切って区間 \([0,1]\) に入れる関数です（束の座標に入れるため）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3System"></a>

## 定義 `c1Theorem3System`

### 式

$$
\text{物理座標を、抽象的な共有系の主体とみなす}
$$

### Lean のコメント（日本語訳）

> 各物理主体は、打ち切った大きさを、束の自分の座標に報告する。

### 定義の説明

定理3（共有 TCZ・LUB）の対象である**抽象的な共有系**（`AbstractSharedSystem`）を、この合意モデルの上に作ります。二つの物理座標が、そのまま二人の主体です。各主体は、自分の状態の大きさ（打ち切ったもの）を、束の**自分の座標**に報告します（他の座標は 0）。世界のラベルはすべて最小元 \(\bot\) です。埋め込み \(\iota\) は、束の点を実数の座標へ送る順序埋め込みです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.instance@L41"></a>

## インスタンス `instance@L41`

### 式

$$
\text{各主体の状態型 }\mathbb R\ \text{は擬距離空間}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各主体の状態型が \(\mathbb R\) であることから、擬距離空間の構造を与える局所インスタンスです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3System_lub"></a>

## 補題 `c1Theorem3System_lub`

### 式

$$
\mathrm{LUB}=\bot
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全世界ラベルの上限（LUB）は、最小元 \(\bot\) です（ラベルがすべて \(\bot\) だから）。

### 証明の概略

1. LUB の定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3System_abstraction_residual"></a>

## 補題 `c1Theorem3System_abstraction_residual`

### 式

$$
z\in\mathrm{box}\Rightarrow A_i(z_i)=z_i^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、主体 \(i\) の抽象残差（LUB への距離の二乗）は \(z_i^2\) です。

### 証明の概略

1. 箱の中では \(\lvert z_i\rvert\le1/4\le1\) なので、打ち切りは何もしない（`min_eq_left`）。
2. 報告した束の点は第 \(i\) 座標だけ \(\lvert z_i\rvert\)、他は 0。LUB は \(\bot\)（全座標 0）。
3. 座標ごとのノルムの二乗は \(z_i^2\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Trajectory"></a>

## 定義 `c1Theorem3Trajectory`

### 式

$$
x_i(s)=\bigl(\Phi^{(3)}_{t_0\to s}(x)\bigr)_i
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適な合意の流れの、主体 \(i\) の軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3SharedTCZ"></a>

## 定義 `c1Theorem3SharedTCZ`

### 式

$$
\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理2の共有 TCZ です（物理的な合意の対角線）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Weight"></a>

## 定義 `c1Theorem3Weight`

### 式

$$
\eta_i=\tfrac12
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二人の主体の重み \(\eta_i\) は、どちらも \(1/2\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Potential"></a>

## 定義 `c1Theorem3Potential`

### 式

$$
\Phi_3(s)=\Phi_2+\sum_i\eta_i A_i
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

流れに沿った、抽象共有系のポテンシャル \(\Phi_3=\Phi_2+\sum_i\eta_iA_i\) です（共有残差に、各主体の抽象残差の重みつき和を足す）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Zero"></a>

## 定義 `c1Theorem3Zero`

### 式

$$
(0,0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

原点です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3"></a>

## 定義 `c1Theorem3StatePhi3`

### 式

$$
\Phi_3(z,t)=\Phi_2(z,t)+\sum_i\eta_iA_i(z_i)
$$

### Lean のコメント（日本語訳）

> 状態ごとの `Φ₃=Φ₂+ΣηᵢAᵢ`。同じ物理状態・同じ時刻で評価する。

### 定義の説明

状態ごとに評価した \(\Phi_3=\Phi_2+\sum\eta_iA_i\) です（同じ物理状態・同じ時刻で評価）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3OriginalTCZ"></a>

## 定義 `c1Theorem3OriginalTCZ`

### 式

$$
\{z\in\overline{\mathrm{Reach}}\mid\Phi_3(z,t)=0\}
$$

### Lean のコメント（日本語訳）

> 定理3の本来の目標：閉到達領域の中で、完全な `Φ₃` の零点集合。`Φ₂` だけの零点集合とは別である。

### 定義の説明

定理3の**本来の目標集合**です。閉到達領域のうち、完全な \(\Phi_3\) が 0 になる点の集合で、\(\Phi_2\) だけが 0 になる集合（合意の対角線）とは別です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3StatePhi3_eq_on_box"></a>

## 補題 `c1Theorem3StatePhi3_eq_on_box`

### 式

$$
z\in\mathrm{box}\Rightarrow\Phi_3(z,t)=2(z_0-z_1)^2+\tfrac12(z_0^2+z_1^2)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、\(\Phi_3\) は具体的に \(2(z_0-z_1)^2+\tfrac12(z_0^2+z_1^2)\) です。

### 証明の概略

1. 定義を展開し、共有残差 \(2(z_0-z_1)^2\)（`sharedPotential_eq_coupling`）と抽象残差 \(z_i^2\)（前の補題）、重み \(1/2\) を代入する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3OriginalTCZ_eq_singleton"></a>

## 補題 `c1Theorem3OriginalTCZ_eq_singleton`

### 式

$$
\text{本来の TCZ}=\{(0,0)\}
$$

### Lean のコメント（日本語訳）

> この箱では、完全な `Φ₃` の零点集合はちょうど原点で、`Φ₂` の対角の零点集合より小さい。

### 補題の説明

この箱の中では、完全な \(\Phi_3\) の零点集合はちょうど原点 \(\{(0,0)\}\) で、\(\Phi_2\) の零点集合（対角線）より小さいです。

### 証明の概略

1. （⊆）零点 \(z\) は閉到達集合 \(=\) 箱に入る。\(\Phi_3=0\) は、非負の二項の和が 0 なので、\(z_0^2=z_1^2=0\)。
2. （⊇）原点は箱に入り、\(\Phi_3(0)=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3OriginalTCZ_nonempty"></a>

## 補題 `c1Theorem3OriginalTCZ_nonempty`

### 式

$$
\mathrm{TCZ}\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

本来の TCZ は空でありません（原点が入る）。

### 証明の概略

1. 前の補題で一点集合。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Trajectory_zeroMean"></a>

## 補題 `c1Theorem3Trajectory_zeroMean`

### 式

$$
x_0+x_1=0\Rightarrow x_0(t)+x_1(t)=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期点の平均が 0 なら、軌道の平均はずっと 0 です（合意の流れは平均を保つ）。

### 証明の概略

1. 流れの式を展開すると、平均の項が打ち消される（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3NontrivialInitial"></a>

## 定義 `c1Theorem3NontrivialInitial`

### 式

$$
(\tfrac18,-\tfrac18)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

非自明な初期点（食い違っているが、平均は 0）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3NontrivialInitial_mem_box"></a>

## 補題 `c1Theorem3NontrivialInitial_mem_box`

### 式

$$
\in\mathrm{box}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この初期点は箱に入ります。

### 証明の概略

1. 各座標の絶対値が \(1/8\le1/4\)（`norm_num`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3NontrivialInitial_zeroMean"></a>

## 補題 `c1Theorem3NontrivialInitial_zeroMean`

### 式

$$
x_0+x_1=0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この初期点の平均は 0 です。

### 証明の概略

1. \(1/8-1/8=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3NontrivialInitial_abstractResidual_positive"></a>

## 補題 `c1Theorem3NontrivialInitial_abstractResidual_positive`

### 式

$$
A_0(x_0)>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この初期点の抽象残差は正です（目標に着いていない、非自明）。

### 証明の概略

1. 抽象残差は \(x_0^2=1/64>0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Potential_eq_of_zeroMean"></a>

## 補題 `c1Theorem3Potential_eq_of_zeroMean`

### 式

$$
\Phi_3=\tfrac98\,\Phi_2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中で平均が 0 の初期点から出た軌道上では、\(\Phi_3\) は共有残差 \(\Phi_2\) の \(9/8\) 倍です。

### 証明の概略

1. 軌道は箱に留まり、平均 0 を保つ。
2. 軌道上の点 \(y\) で \(y_0=-y_1\)。共有残差は \(8y_0^2\)、抽象残差の重みつき和は \(y_0^2\)、合計は \(9y_0^2=\tfrac98\Phi_2\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Potential_ac"></a>

## 補題 `c1Theorem3Potential_ac`

### 式

$$
\Phi_3\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\Phi_3\) は有限区間で絶対連続です。

### 証明の概略

1. \(\Phi_3=\tfrac98\Phi_2\)（前の補題）と、\(\Phi_2\) の絶対連続性（`consensusOptimalPotentialAlong_ac`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3Potential_decay_ae"></a>

## 補題 `c1Theorem3Potential_decay_ae`

### 式

$$
\frac{d}{ds}\Phi_3\le-2\cdot3\,\Phi_3\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\Phi_3\) は、ほとんど至る所で率 3 の下降条件を満たします。

### 証明の概略

1. 両端は測度 0。内点で、近傍では \(\Phi_3=\tfrac98\Phi_2\) なので、導関数も \(\tfrac98\) 倍。
2. \(\Phi_2\) の下降（`consensusOptimalResidualPath_hasDerivAt`）から。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3_shared_nonempty"></a>

## 補題 `c1Theorem3_shared_nonempty`

### 式

$$
\mathrm{sharedTCZ}\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有 TCZ は空でありません。

### 証明の概略

1. `consensus_sharedTCZ_nonempty`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3_rate3_quantitative"></a>

## 定理 `c1Theorem3_rate3_quantitative`

### 式

$$
\operatorname{dist}(x(s),\mathrm{sharedTCZ})\le\sqrt{\Phi_3(x_0)}\,e^{-3(s-t_0)},\quad \lVert\text{LUB 表象}\rVert\le\sqrt{\Phi_3/\eta_0}\,e^{-3(s-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

零平均の初期点から出た最適な合意の流れで、(1) 共有 TCZ（合意の対角線）までの距離と、(2) 主体 0 の抽象表象の LUB までの距離が、ともに率 3 の指数で小さくなります。定理3の定量的な結論の一つです。

### 証明の概略

1. \(\Phi_3\) の各項が非負（\(\eta_iA_i\ge0\)）であること、絶対連続・下降（率 3）を確認する。
2. 定理3の一般入口に渡す。共有 TCZ の非空性・誤差境界は、前のファイルの結果を使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3_original_phi3_bound"></a>

## 定理 `c1Theorem3_original_phi3_bound`

### 式

$$
\operatorname{dist}\bigl(x(s),\mathrm{TCZ}_{\Phi_3}\bigr)\le\sqrt{\Phi_3(x_0)}\,e^{-3(s-t_0)},\quad \lVert\text{LUB 表象}_i\rVert\le\sqrt{\Phi_3/\eta_i}\,e^{-3(s-t_0)}
$$

### Lean のコメント（日本語訳）

> 実際の完全な `Φ₃` の零点集合についての、有限時間の定量的な結論。

### 補題の説明

本来の目標集合（完全な \(\Phi_3\) の零点集合）についての、有限時間の定量的な結論です。(1) 状態は本来の TCZ に率 3 で近づく。(2) 各主体 \(i\) の抽象表象は LUB に率 3 で近づく。

### 証明の概略

1. 前の定理と同様に、残差の絶対連続・下降を確認する。
2. 本来の TCZ（原点）への距離についての誤差境界を示す（箱の中で \(\operatorname{dist}^2\le\Phi_3\) 型の評価）。
3. 定理3の一般入口に渡す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Theorem3Bridge.c1Theorem3_original_phi3_tendsto"></a>

## 定理 `c1Theorem3_original_phi3_tendsto`

### 式

$$
\operatorname{dist}(x(s),\mathrm{TCZ}_{\Phi_3})\to0,\quad \lVert\text{LUB 表象}_i\rVert\to0
$$

### Lean のコメント（日本語訳）

> 完全な `Φ₃` の零点集合までの状態の距離と、各主体の LUB 表象は 0 に収束する。有限時間の速さは、直前の評価が与える。

### 補題の説明

状態の本来の TCZ への距離と、すべての主体の LUB 表象への距離が、0 に収束します。有限時間の速さは、前の定理の評価によります。

### 証明の概略

1. 前の定理の評価（右辺が指数で 0 に収束する）に、はさみうちの原理を適用する。距離は非負。

----


## コメント修正記録

（英語の docstring は、この解説書では日本語訳を載せました。）
