# Tomabechi/Consistency/ConsistencyC1_ConsensusControl.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC1_ConsensusControl.lean`](../Tomabechi/Consistency/ConsistencyC1_ConsensusControl.lean)（二主体の合意モデルでの有限地平の最適化と、定理1・2・4・20 の適用）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

前のファイル（二主体の合意の流れ）に、**制御の最適化**と、**定理1・2・4・20 の適用**を加えるファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「二主体合意系」の中核です。

* **有限地平の最適性（argmin）**：ゲイン信号 \(u\in[0,3]\) のうち、最大ゲイン 3 が、費用 \(\int(1+\cdot)\) を最小にします（一次元モデルの結果を二主体へ移す）。
* **最適流れ**：最大ゲインの閉ループの流れ（率 3 の合意）。前の率 2 の流れを、時間を 1.5 倍に速めたものです。
* **定理1・2・4 の適用**：最適流れに定理1・2・4 の一般入口を適用し、指数収束（率 3、個人・辺の誤差は率 6）を得ます。定理4では、臨場感 \(P=e^{-\Phi_2}\) が定数でなくても、実効ポテンシャルで打ち消されます。
* **定理20 の適用**：象徴（情報の束 \(\{\emptyset,\{0\}\}\)、アドレス \(\{0\}\)、目標 = 合意の対角線）のデータを作り、Euclid 座標へ移して定理20の入口を適用します。

### 0.2 このファイルが証明していないこと

* 制御の集合は、可測で \([0,3]\) に入る信号に**具体化**したものです（原文の関数空間とは同一視していません）。
* 二主体の状態は箱の中に限ります。
* 定理20の象徴データは、このモデルのために置いた**有限の具体例**です（情報束は二点の真部分束）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 既存の最大ゲイン最適化核を、定理1/2で使う二主体状態空間へ移す。制御信号 `u∈[0,3]` は平均を保ち、不一致成分を `exp(-∫u)` 倍する。したがって選択制御 `u=3` の閉ループ flow は指数率3の合意流となる。

節のコメント：

> **二主体 flow に結び付けた定理20の有限象徴データ。** 情報束は二主体の冪集合束で、利用可能情報は `{∅, {0}}` という真部分束（全体 `{0,1}` を含まない）にする。象徴の指示集合は `{0}`、そのLUBも `{0}` であり、状態空間側ではこのアドレスを合意集合へ対応させる。以下は C1 の同一二主体状態・flow に結び付いた具体データである。

> **定理20のための Euclid 座標での実現。** `AgentState` は sup ノルムを持つ関数型で、内積空間のインスタンスを持たない。同じ座標の力学を、標準的な連続線形同値で `EuclideanSpace ℝ (Fin 2)` へ移す。そこでは定理20の勾配流のインターフェースが適用できる。

---

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.controlledConsensusState"></a>

## 定義 `controlledConsensusState`

### 式

$$
\bigl(m+\text{orbit}(d),\ m-\text{orbit}(d)\bigr)
$$

### Lean のコメント（日本語訳）

> 可測ゲイン信号で動く二主体の明示軌道。平均は保ち、半差だけを減衰させる。

### 定義の説明

ゲイン信号 \(u\) で動かした二人の状態を、式で書いたものです。平均 \(m\) は動かさず、差の半分 \(d\) だけを、一次元モデルの積分軌道 \(d\,e^{-\int u}\) で縮めます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.controlledConsensusState_halfDifference"></a>

## 補題 `controlledConsensusState_halfDifference`

### 式

$$
d\bigl(\text{state}\bigr)=\text{orbit}(d_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この軌道の差の半分は、一次元モデルの積分軌道に一致します。

### 証明の概略

1. 定義を展開して、二つの座標の差を取る（`simp` と整理）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFiniteHorizonCost"></a>

## 定義 `consensusFiniteHorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}\bigl(1+d(s)^2\bigr)\,ds
$$

### Lean のコメント（日本語訳）

> 二主体モデルで最小化する有限地平費用。

### 定義の説明

二主体モデルの有限地平費用です。基準値 1 に、差の半分の二乗を足して時間で積分します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusFiniteHorizonCost_eq_scalar"></a>

## 補題 `consensusFiniteHorizonCost_eq_scalar`

### 式

$$
\text{二主体の費用}=\text{一次元の費用}(d_0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

二主体の費用は、差の半分に対する一次元モデルの費用に一致します。

### 証明の概略

1. 費用の被積分関数が、各時刻で一致することを示す（`lintegral_congr_ae`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_maxGain_attains_finite_horizon_argmin"></a>

## 補題 `consensus_maxGain_attains_finite_horizon_argmin`

### 式

$$
J(u_{\max})\le J(u)\quad(\forall u)
$$

### Lean のコメント（日本語訳）

> 最大ゲインは同じ二主体初期状態・費用の全可測ゲイン競合に対するargmin。

### 補題の説明

二主体モデルでも、最大ゲイン 3 が、すべての許容制御の中で費用を最小にします。

### 証明の概略

1. 二主体の費用を一次元の費用に書き換える（`consensusFiniteHorizonCost_eq_scalar`）。
2. 一次元の結果 `c1_maximum_gain_attains_finite_horizon_argmin` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_maxGain_finite_cost"></a>

## 補題 `consensus_maxGain_finite_cost`

### 式

$$
J(u_{\max})<\infty
$$

### Lean のコメント（日本語訳）

> 選択最大ゲインの二主体費用は有限。

### 補題の説明

最大ゲインの費用は有限です。

### 証明の概略

1. 一次元の費用に書き換え、`c1_maximum_gain_finite_cost` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusTheorem1HorizonCost"></a>

## 定義 `consensusTheorem1HorizonCost`

### 式

$$
\int_{t_0}^{t_0+T}\bigl(1+\Phi_2(\text{state}(s),s)\bigr)\,ds
$$

### Lean のコメント（日本語訳）

> 定理1で使う `V₀=1+Φ₂` の実際の有限地平費用。`Φ₂=8d²` なので、既存の `1+d²` 費用とは定数倍部分が異なる。

### 定義の説明

定理1の基礎評価 \(V_0=1+\Phi_2\) で測った有限地平の費用です。箱の中では \(\Phi_2=8d^2\) なので、先の \(1+d^2\) の費用とは、\(d^2\) の係数が違います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.controlledConsensusState_mem_box"></a>

## 補題 `controlledConsensusState_mem_box`

### 式

$$
x\in\mathrm{box},\ s\ge t_0\Rightarrow\text{state}(s)\in\mathrm{box}
$$

### Lean のコメント（日本語訳）

> 任意の許容ゲインが作る二主体状態は、初期箱の中にとどまる。

### 補題の説明

どの許容ゲインで動かしても、箱の中から出発した状態は、前向きの時刻で箱の中にとどまります。

### 証明の概略

1. 累積ゲインは 0 以上なので、\(e^{-\text{累積量}}\in[0,1]\)。
2. 各座標は、重み \(\tfrac{1\pm e}{2}\in[0,1]\) の凸結合として書ける。
3. 凸結合は箱に入る（`convexCombination_mem_box`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_maxGain_attains_theorem1_horizon_argmin"></a>

## 補題 `consensus_maxGain_attains_theorem1_horizon_argmin`

### 式

$$
J_1(u_{\max})\le J_1(u)\quad(\forall u)
$$

### Lean のコメント（日本語訳）

> 定理1の `V₀` 費用でも最大ゲインが全Borelゲイン信号上でargminを達成する。比較は各時刻での不一致二乗の大小を直接積分する。

### 補題の説明

定理1の基礎評価 \(V_0=1+\Phi_2\) の費用でも、最大ゲインが最小です。

### 証明の概略

1. 箱の中では \(\Phi_2=8d^2\) なので、各時刻の費用の大小は \(d^2\) の大小で決まる。
2. 最大ゲインの差の二乗は他の制御以下（`c1MaxGain_orbit_sq_le`）。
3. 被積分関数の点ごとの不等式を、積分に持ち上げる（`lintegral_mono_ae`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_maxGain_finite_theorem1_cost"></a>

## 補題 `consensus_maxGain_finite_theorem1_cost`

### 式

$$
J_1(u_{\max})<\infty
$$

### Lean のコメント（日本語訳）

> 選んだ制御は、定理1で使うのと同じ `V₀` について、正の有限地平のどれでも、箱の中のどの初期状態でも、有限の費用を持つ。

### 補題の説明

定理1と同じ \(V_0\) について、選んだ制御の費用は、箱の中のどの初期状態でも、正のどの有限地平でも有限です。

### 証明の概略

1. 最大ゲインの軌道の被積分関数は連続な関数 \(1+8(d\,e^{-3(s-t_0)})^2\)。コンパクト区間で可積分で非負。
2. 非負の可積分関数の下積分は有限（`ofReal_integral_eq_lintegral_ofReal`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow"></a>

## 定義 `consensusOptimalFlow`

### 式

$$
\dot x=\bigl(-\tfrac u2(x_0-x_1),\ \tfrac u2(x_0-x_1)\bigr),\quad \pi\equiv3
$$

### Lean のコメント（日本語訳）

> 全状態・全実数時刻に定義した最大ゲインの閉ループ合意flow。

### 定義の説明

最大ゲイン \(u=3\) の閉ループの合意の流れです。許容制御は \([0,3]\)、フィードバックは常に 3、ベクトル場は \(u/2\) 倍の差の項。流れの式は、平均を保ち、差の半分が \(e^{-3(t-t_0)}\) 倍になります。全状態・全時刻で定義してあります。

### 証明の概略

1. 許容性は \(0\le3\le3\)（`norm_num`）。
2. 初期条件・やり直し則は、`consensusFlow` と同様に、成分ごとの式の整理と指数の加法性で示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalTimeMap"></a>

## 定義 `consensusOptimalTimeMap`

### 式

$$
t_0+\tfrac32(t-t_0)
$$

### Lean のコメント（日本語訳）

> rate-3最適flowをrate-2合意flowで表す時間変換。

### 定義の説明

率 3 の流れは、率 2 の合意の流れを、時間を 1.5 倍に速めたものです。その時間の変換です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_eq_retimed"></a>

## 補題 `consensusOptimalFlow_eq_retimed`

### 式

$$
\Phi^{(3)}_{t_0\to t}(x)=\Phi^{(2)}_{t_0\to \tau(t)}(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

率 3 の最適流れは、率 2 の合意の流れを時間変換 \(\tau\) したものに一致します。

### 証明の概略

1. 両辺の成分を式で書く。指数の引数が \(-3(t-t_0)=-2(\tau(t)-t_0)\) で等しい（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_gap"></a>

## 補題 `consensusOptimalFlow_gap`

### 式

$$
x_0(t)-x_1(t)=(x_0-x_1)\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適流れでの二人の差は、初期差の \(e^{-3(t-t_0)}\) 倍です。

### 証明の概略

1. 流れの式から、差を計算する（平均が打ち消される）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_forward_invariant"></a>

## 補題 `consensusOptimalFlow_forward_invariant`

### 式

$$
x\in\mathrm{box}\Rightarrow\Phi^{(3)}_{t_0\to t}(x)\in\mathrm{box}
$$

### Lean のコメント（日本語訳）

> rate-3最適flowは、初期箱をすべての未来時刻で保つ。

### 補題の説明

率 3 の最適流れも、箱の中の点を、前の時刻で箱の中に保ちます。

### 証明の概略

1. 時間変換 \(\tau(t)\ge t_0\)。
2. 時間変換で率 2 の流れに書き換え（`consensusOptimalFlow_eq_retimed`）、`consensusFlow_forward_invariant` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_reachable_closure_eq_box"></a>

## 補題 `consensusOptimalFlow_reachable_closure_eq_box`

### 式

$$
\overline{\mathrm{Reach}}=\mathrm{box}
$$

### Lean のコメント（日本語訳）

> rate-3最適flowが初期箱から生成する閉到達集合は箱そのもの。

### 補題の説明

最適流れで到達する点の閉包は、箱そのものです。

### 証明の概略

1. （⊆）到達点は前向き不変で箱に入り、箱は閉。
2. （⊇）箱の点は、時刻 \(t_0\) でそのまま到達できる。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalResidualPath"></a>

## 定義 `consensusOptimalResidualPath`

### 式

$$
\gamma\bigl((x_0-x_1)\,e^{-3(s-t_0)}\bigr)^2
$$

### Lean のコメント（日本語訳）

> rate-3最適flow上の共有残差を表す滑らかな閉形式。

### 定義の説明

最適流れに沿った共有残差の、時間の滑らかな関数としての閉じた式です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalResidualPath_hasDerivAt"></a>

## 補題 `consensusOptimalResidualPath_hasDerivAt`

### 式

$$
\frac{d}{ds}\text{resid}=-2\cdot3\cdot\text{resid}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉形式の残差の微分は、残差の \(-6\) 倍です（率 3 の指数減衰）。

### 証明の概略

1. 指数の引数の微分は \(-3\)。\(\exp\)・定数倍・二乗・定数倍の合成の微分を整理する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalResidualPath_ac"></a>

## 補題 `consensusOptimalResidualPath_ac`

### 式

$$
\text{resid}\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C¹ 級なので絶対連続です。

### 証明の概略

1. C¹ 性（`fun_prop`）から絶対連続性を得る。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalPotentialAlong"></a>

## 定義 `consensusOptimalPotentialAlong`

### 式

$$
s\mapsto\Phi_2\bigl(\Phi^{(3)}_{t_0\to s}(x),s\bigr)
$$

### Lean のコメント（日本語訳）

> 最適flow上では実共有残差が閉形式の率3 pathに一致する。

### 定義の説明

最適流れに沿って、共有残差を実際に評価した関数です。次の補題で、箱の中では閉形式に一致することを示します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalPotentialAlong_eq"></a>

## 補題 `consensusOptimalPotentialAlong_eq`

### 式

$$
\text{実残差}=\text{閉形式}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱から出発すれば、実際の残差は閉形式と一致します。

### 証明の概略

1. 流れが箱に留まる（前向き不変）ので、`sharedPotential_eq_coupling` を使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalPotentialAlong_ac"></a>

## 補題 `consensusOptimalPotentialAlong_ac`

### 式

$$
\text{実残差は絶対連続}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実際の残差も絶対連続です。

### 証明の概略

1. 閉形式が絶対連続で、実残差と一致するので、実残差も絶対連続（`congr`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalPotentialAlong_decay_ae"></a>

## 補題 `consensusOptimalPotentialAlong_decay_ae`

### 式

$$
\frac{d}{ds}\Phi\le-2\cdot3\,\Phi\quad(\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 最適flow上の実共有残差は有限区間でa.e.に率6で減少する。

### 補題の説明

最適流れの上で、実共有残差の微分は、ほとんど至る所で \(-6\) 倍の残差以下です。

### 証明の概略

1. 両端は測度 0。内点では、近傍で実残差が閉形式に一致するので、導関数も一致する。
2. 閉形式の導関数は \(-6\) 倍の閉形式。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalTheorem1Target"></a>

## 定義 `consensusOptimalTheorem1Target`

### 式

$$
\{y\in\overline{\mathrm{Reach}}\mid V_0(y)\le1\}
$$

### Lean のコメント（日本語訳）

> rate-3最適flowの定理1 TCZ。元の基礎評価を `1+Φ₂` とする。

### 定義の説明

最適流れに対する、定理1の TCZ（閉到達集合のうち \(V_0\le1\) の点）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalTheorem1Target_eq_shared"></a>

## 補題 `consensusOptimalTheorem1Target_eq_shared`

### 式

$$
\mathrm{TCZ}_1=\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この TCZ は、定理2の共有 TCZ に一致します。

### 証明の概略

1. 閉到達集合が箱（`consensusOptimalFlow_reachable_closure_eq_box`）。
2. 箱の上では残差が時刻によらない（`sharedPotential_eq_coupling`）ので、\(1+\Phi_2\le1\iff\Phi_2=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_theorem1"></a>

## 定理 `consensusOptimalFlow_theorem1`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{TCZ}_1\bigr)\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> O02最適化flow上で定理1の全未来定量結論と距離収束を得る。

これは `consensusOptimalFlow` 自身を定理1のH-flowとして渡し、全有限区間条件を rate-3共有残差の閉形式から供給する適用である。

### 補題の説明

最適化された率 3 の流れに、定理1を適用した結論です。(1) 流れは閉到達集合に留まる。(2) TCZ までの距離は \(\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}\) 以下。(3) 距離は 0 に収束する。

### 証明の概略

1. 各有限区間で、TCZ が空でない（共有 TCZ の非空性）、残差が絶対連続・a.e. 下降（率 3）、誤差境界（\(C=1\)）であることを示す。
2. 定理1の一般形（`theorem1_policy_flow_reachable_tcz_distance_tendsto_zero`）に渡す。
3. 初期残差を書き換えて、結論の形に整える。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresenceP"></a>

## 定義 `consensusPresenceP`

### 式

$$
P(x)=\exp\bigl(-\Phi_2(x,0)\bigr)
$$

### Lean のコメント（日本語訳）

> 二主体共有ポテンシャルから作る非定数の臨場感。

### 定義の説明

定理4の臨場感 \(P\) を、共有ポテンシャルから \(e^{-\Phi_2}\) として作ったものです。定数でなく、状態によって変わります。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresenceQ"></a>

## 定義 `consensusPresenceQ`

### 式

$$
Q\equiv1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理4の第二の臨場感 \(Q\) は、定数 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresenceV0"></a>

## 定義 `consensusPresenceV0`

### 式

$$
V_0=1+\Phi_2+P
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理4用の基礎評価です。\(P\) をわざと足してあるので、実効ポテンシャル \(V_0-\kappa PQ\) では \(P\) が打ち消されます（`consensusPresence_effective_eq_shared`）。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresence_potential_nonneg"></a>

## 補題 `consensusPresence_potential_nonneg`

### 式

$$
\Phi_2(x,t)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共有残差は非負です。

### 証明の概略

1. 共有残差の具体形（`potential_eq`）から、各項が非負（`positivity`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresenceP_bounds"></a>

## 補題 `consensusPresenceP_bounds`

### 式

$$
0<P\le1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(P=e^{-\Phi_2}\) は 0 より大きく 1 以下です（定理4の値域条件）。

### 証明の概略

1. \(\exp>0\)。\(\Phi_2\ge0\) なので \(-\Phi_2\le0\)、よって \(\exp\le1\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresenceP_nonconstant"></a>

## 補題 `consensusPresenceP_nonconstant`

### 式

$$
P((0,0))\ne P((1,0))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(P\) は定数ではありません（原点と \((1,0)\) で値が違う）。非退化性の確認です。

### 証明の概略

1. 二点での共有残差を計算し、\(\exp\) の単射性から、値が異なることを示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresence_effective_eq_shared"></a>

## 補題 `consensusPresence_effective_eq_shared`

### 式

$$
V_0-\kappa PQ=1+\Phi_2(x,0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

実効ポテンシャル（\(\kappa=1\)）は、\(P\) が打ち消されて \(1+\Phi_2\) になります。

### 証明の概略

1. 定義を展開し、\(Q=1\) と \(P\) の項を打ち消す（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresence_residual_eq_potential"></a>

## 補題 `consensusPresence_residual_eq_potential`

### 式

$$
x\in\mathrm{box}\Rightarrow\text{residual}_4=\Phi_2(x,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、定理4の残差は共有残差に一致します。

### 証明の概略

1. 実効ポテンシャルが \(1+\Phi_2(x,0)\)（前の補題）。
2. 箱の上では残差が時刻によらない。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusPresence_weightedTCZ_eq_shared"></a>

## 補題 `consensusPresence_weightedTCZ_eq_shared`

### 式

$$
\mathrm{weightedTCZ}=\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

定理4の加重 TCZ は、共有 TCZ に一致します。

### 証明の概略

1. 実効ポテンシャルが \(1+\Phi_2(y,0)\) なので、\(\le1\) は \(\Phi_2(y,0)\le0\) と同値。箱の上で時刻によらず、非負なので \(=0\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.C1SymbolConcept"></a>

## 定義 `C1SymbolConcept`

### 式

$$
\mathcal P(\{0,1\})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の「概念」の型です。二主体の添字集合 \(\{0,1\}\) の部分集合（冪集合束）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolInfoLattice"></a>

## 定義 `c1SymbolInfoLattice`

### 式

$$
\{\emptyset,\ \{0\}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

利用可能な情報の集合（真部分束）です。空集合と \(\{0\}\) だけで、全体 \(\{0,1\}\) を含みません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1AvailableInformation"></a>

## 定義 `c1AvailableInformation`

### 式

$$
\text{どの主体・時刻でも}\ \{\emptyset,\{0\}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各主体・各時刻に利用できる情報は、上の真部分束です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolW"></a>

## 定義 `c1SymbolW`

### 式

$$
W=\{\{0\}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の指示集合 \(W\) です。\(\{0\}\) だけを含みます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolAddress"></a>

## 定義 `c1SymbolAddress`

### 式

$$
u=\{0\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴のアドレス（\(W\) の上限）です。\(\{0\}\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolInfo_bot"></a>

## 補題 `c1SymbolInfo_bot`

### 式

$$
\emptyset\in\{\emptyset,\{0\}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

空集合は利用可能情報に入ります。

### 証明の概略

1. 定義の左側の選択肢（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolInfo_join_closed"></a>

## 補題 `c1SymbolInfo_join_closed`

### 式

$$
a,b\in\mathcal L\Rightarrow a\cup b\in\mathcal L
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

利用可能情報は、和集合（結び）で閉じています。

### 証明の概略

1. 各々 \(\emptyset\) か \(\{0\}\) の場合分けで、和も \(\emptyset\) か \(\{0\}\) になることを確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolInfo_meet_closed"></a>

## 補題 `c1SymbolInfo_meet_closed`

### 式

$$
a,b\in\mathcal L\Rightarrow a\cap b\in\mathcal L
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

利用可能情報は、共通部分（交わり）でも閉じています。

### 証明の概略

1. 場合分けで、共通部分が \(\emptyset\) か \(\{0\}\) になることを確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolInfo_proper"></a>

## 補題 `c1SymbolInfo_proper`

### 式

$$
\{0,1\}\notin\mathcal L
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全体 \(\{0,1\}\) は利用可能情報に入りません（真部分束）。

### 証明の概略

1. 入っていたとすると、\(1\) が空集合または \(\{0\}\) に属することになり、矛盾（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1AvailableInformation_proper"></a>

## 補題 `c1AvailableInformation_proper`

### 式

$$
\text{利用可能情報}\subsetneq\text{全体}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

利用可能情報は全体の真部分集合です（すべてが分かる状態ではない）。

### 証明の概略

1. 部分集合は明らか。等しいと仮定すると、全体 \(\{0,1\}\) が入って矛盾（前の補題）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolW_subset_info"></a>

## 補題 `c1SymbolW_subset_info`

### 式

$$
W\subset\mathcal L
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

指示集合は利用可能情報に含まれます。

### 証明の概略

1. \(W\) の唯一の元 \(\{0\}\) が束の右側の選択肢。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolAddress_isLUB"></a>

## 補題 `c1SymbolAddress_isLUB`

### 式

$$
\{0\}=\sup W
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレス \(\{0\}\) は \(W\) の最小上界（LUB）です。

### 証明の概略

1. 上界であること：\(W\) の元は \(\{0\}\) だけで、\(\{0\}\subseteq\{0\}\)。
2. 最小であること：他の上界 \(b\) は \(\{0\}\subseteq b\) を満たす。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolTarget"></a>

## 定義 `c1SymbolTarget`

### 式

$$
\mathrm{Tgt}(u)=\begin{cases}\{x\mid x_0=x_1\}&u=\{0\}\\\emptyset&\text{otherwise}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の目標集合です。アドレスが \(\{0\}\) のとき、二人が一致する状態（合意の対角線）、それ以外では空集合です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance"></a>

## 定義 `c1SymbolDistance`

### 式

$$
D(x)=\tfrac14(x_0-x_1)^2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の距離（食い違いの二乗）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolTarget_nonempty"></a>

## 補題 `c1SymbolTarget_nonempty`

### 式

$$
\mathrm{Tgt}(\{0\})\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合は空でありません。原点が入ります。

### 証明の概略

1. 原点 \((0,0)\) は \(x_0=x_1\) を満たす（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolTarget_closed"></a>

## 補題 `c1SymbolTarget_closed`

### 式

$$
\mathrm{Tgt}(\{0\})\ \text{は閉集合}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合は閉集合です。

### 証明の概略

1. \(\{x\mid x_0=x_1\}\) は、二つの連続関数が等しい点の集合なので閉（`isClosed_eq`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance_nonneg"></a>

## 補題 `c1SymbolDistance_nonneg`

### 式

$$
D(x)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

距離は非負です。

### 証明の概略

1. 二乗の非負性（`nlinarith`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance_zero_iff"></a>

## 補題 `c1SymbolDistance_zero_iff`

### 式

$$
D(x)=0\iff x\in\mathrm{Tgt}(\{0\})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

距離が 0 であることと、目標集合に入ることは同値です。

### 証明の概略

1. （→）\(\tfrac14(x_0-x_1)^2=0\) から \(x_0=x_1\)。
2. （←）\(x_0=x_1\) なら距離は 0。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance_eq_sharedPotential_on_box"></a>

## 補題 `c1SymbolDistance_eq_sharedPotential_on_box`

### 式

$$
x\in\mathrm{box}\Rightarrow D(x)=\tfrac18\Phi_2(x,t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱の中では、象徴の距離は共有残差の \(1/8\) 倍です（係数の関係）。

### 証明の概略

1. 箱の上で \(\Phi_2=2(x_0-x_1)^2\)。\(D=\tfrac14(x_0-x_1)^2\) との比が \(1/8\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolTarget_box_eq_sharedTCZ"></a>

## 補題 `c1SymbolTarget_box_eq_sharedTCZ`

### 式

$$
\mathrm{box}\cap\mathrm{Tgt}(\{0\})=\mathrm{sharedTCZ}(\mathrm{box},t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱と象徴の目標集合の共通部分は、共有 TCZ に一致します。象徴のデータが、定理1・2の目標と同じものを指していることの確認です。

### 証明の概略

1. 共有 TCZ は「箱の点で共有残差が 0」。箱の上で共有残差 \(=2(x_0-x_1)^2\)。\(=0\) は \(x_0=x_1\) と同値。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance_optimalFlow_decay"></a>

## 補題 `c1SymbolDistance_optimalFlow_decay`

### 式

$$
D(\Phi^{(3)}(x))=D(x)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適流れの上で、象徴の距離は率 6 で指数減衰します（差が \(e^{-3(t-t_0)}\) 倍なので、二乗で \(e^{-6}\)）。

### 証明の概略

1. 定義を展開し、`consensusOptimalFlow_gap` と指数の性質で整理する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolBasePresence"></a>

## 定義 `c1SymbolBasePresence`

### 式

$$
P_{\text{base}}\equiv0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の基礎臨場感は、常に 0 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolAmplification"></a>

## 定義 `c1SymbolAmplification`

### 式

$$
A(u)=\begin{cases}1&u=\{0\}\\0&\text{otherwise}\end{cases}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の増幅は、アドレスが \(\{0\}\) のときだけ 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolLambda"></a>

## 定義 `c1SymbolLambda`

### 式

$$
\lambda=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

増幅の係数 \(\lambda\) は 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolPresence"></a>

## 定義 `c1SymbolPresence`

### 式

$$
P(u,x,t)=P_{\text{base}}+\lambda A(u)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の臨場感です。基礎臨場感に、増幅の \(\lambda\) 倍を足したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolQ"></a>

## 定義 `c1SymbolQ`

### 式

$$
Q\equiv1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴の第二の臨場感 \(Q\) は、定数 1 です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolV0"></a>

## 定義 `c1SymbolV0`

### 式

$$
V_0(x)=2D(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴のモデルの基礎評価は、距離の 2 倍です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolSlope"></a>

## 定義 `c1SymbolSlope`

### 式

$$
s(d)=-d
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

定理20の傾き関数 \(s\) は \(s(d)=-d\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolEffectivePotential"></a>

## 定義 `c1SymbolEffectivePotential`

### 式

$$
V_0-\kappa\,\lambda\,P\,s(D)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

象徴のモデルの有効ポテンシャルです。基礎評価から、臨場感と傾きの積を引きます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolDistance_contDiff"></a>

## 補題 `c1SymbolDistance_contDiff`

### 式

$$
D\ \text{は C}^1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

距離は C¹ 級（滑らか）です。

### 証明の概略

1. 多項式の滑らかさ（`fun_prop`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolV0_contDiff"></a>

## 補題 `c1SymbolV0_contDiff`

### 式

$$
V_0\ \text{は C}^1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基礎評価は C¹ 級です。

### 証明の概略

1. 距離の定数倍（`smul_const`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolSelectedPresence_contDiff"></a>

## 補題 `c1SymbolSelectedPresence_contDiff`

### 式

$$
P(\{0\},\cdot,t)\ \text{は C}^1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスが \(\{0\}\) のときの臨場感は C¹ 級です。

### 証明の概略

1. 臨場感は定数 1（次の補題）なので滑らか。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolSlope_contDiff"></a>

## 補題 `c1SymbolSlope_contDiff`

### 式

$$
s\ \text{は C}^1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

傾き関数は C¹ 級です。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolPresence_selected"></a>

## 補題 `c1SymbolPresence_selected`

### 式

$$
P(\{0\},x,t)=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスが \(\{0\}\) のとき、臨場感は 1 です。

### 証明の概略

1. 定義を展開して、基礎臨場感 0、増幅 1、\(\lambda=1\) を代入（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolAmplification_selected"></a>

## 補題 `c1SymbolAmplification_selected`

### 式

$$
A(\{0\})=1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスが \(\{0\}\) のとき、増幅は 1 です。

### 証明の概略

1. `simp`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolLambda_positive"></a>

## 補題 `c1SymbolLambda_positive`

### 式

$$
\lambda>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\lambda\) は正です。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolBasePresence_unitInterval"></a>

## 補題 `c1SymbolBasePresence_unitInterval`

### 式

$$
P_{\text{base}}\in[0,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基礎臨場感は区間 \([0,1]\) に入ります（定理20の値域条件）。

### 証明の概略

1. 値が 0（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolSlope_derivative"></a>

## 補題 `c1SymbolSlope_derivative`

### 式

$$
s'(d)=-1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

傾き関数の微分は \(-1\) です。

### 証明の概略

1. `hasDerivAt_neg`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolEffectivePotential_selected"></a>

## 補題 `c1SymbolEffectivePotential_selected`

### 式

$$
V_{\text{eff}}(x)=3D(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスが \(\{0\}\) のとき、有効ポテンシャルは距離の 3 倍です（\(2D+D\)）。

### 証明の概略

1. 定義を展開し、臨場感 \(=1\)、傾き \(-D\) を代入して整理（`ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolQ_positive"></a>

## 補題 `c1SymbolQ_positive`

### 式

$$
Q>0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(Q\) は正です。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolEffectivePotential_optimalFlow_decay"></a>

## 補題 `c1SymbolEffectivePotential_optimalFlow_decay`

### 式

$$
V_{\text{eff}}(\Phi^{(3)}(x))=V_{\text{eff}}(x)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適流れの上で、有効ポテンシャルも率 6 で指数減衰します。

### 証明の概略

1. 有効ポテンシャルは距離の 3 倍（前の補題）。距離の減衰（`c1SymbolDistance_optimalFlow_decay`）を適用。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolPresence_selected_bounds"></a>

## 補題 `c1SymbolPresence_selected_bounds`

### 式

$$
0\le P\le1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

アドレスが \(\{0\}\) のときの臨場感は、0 以上 1 以下です（定理20の値域条件）。

### 証明の概略

1. 臨場感が 1（`c1SymbolPresence_selected`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1SymbolQ_range"></a>

## 補題 `c1SymbolQ_range`

### 式

$$
Q\in[-1,1]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(Q\) は区間 \([-1,1]\) に入ります。

### 証明の概略

1. 値が 1（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.C1EuclideanAgentState"></a>

## 定義 `C1EuclideanAgentState`

### 式

$$
\mathbb R^2\ (\text{Euclid 空間})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

二主体の状態を、Euclid 空間 \(\mathbb R^2\)（内積・\(\ell^2\) ノルム）として表した型です。`AgentState` は sup ノルムで内積空間ではないため、定理20（勾配流）を適用するためにこの型を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanCoordinates"></a>

## 定義 `c1EuclideanCoordinates`

### 式

$$
\mathbb R^2_{\text{Euclid}}\ \simeq\ \mathbb R^2_{\text{sup}}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Euclid 表示と `AgentState` を結ぶ、座標の連続線形同値です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanCoordinates_toLp"></a>

## 補題 `c1EuclideanCoordinates_toLp`

### 式

$$
\text{coord}(\text{toLp}\,x)=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

座標変換は、Euclid 表示への埋め込みの逆です。

### 証明の概略

1. 同値の定義を展開し、`ofLp_toLp` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanDisagreementDirection"></a>

## 定義 `c1EuclideanDisagreementDirection`

### 式

$$
v=e_0-e_1
$$

### Lean のコメント（日本語訳）

> 二主体の合意の対角線に垂直な Euclid 方向。

### 定義の説明

合意の対角線 \(x_0=x_1\) に垂直な Euclid 方向のベクトル \(e_0-e_1\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance"></a>

## 定義 `c1EuclideanSymbolDistance`

### 式

$$
\tfrac14\langle v,x\rangle^2
$$

### Lean のコメント（日本語訳）

> Euclid 座標へ移した象徴の距離。

### 定義の説明

象徴の距離を、Euclid 座標へ移したものです。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistanceGradient"></a>

## 定義 `c1EuclideanSymbolDistanceGradient`

### 式

$$
\tfrac12\langle v,x\rangle\,v
$$

### Lean のコメント（日本語訳）

> 移した二次の距離の勾配。

### 定義の説明

移した二次の距離の勾配です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanDisagreement_inner"></a>

## 補題 `c1EuclideanDisagreement_inner`

### 式

$$
\langle v,x\rangle=x_0-x_1
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方向ベクトルとの内積は、二人の差です。

### 証明の概略

1. 成分ごとに計算する（`simp` と `ring`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanDisagreementDirection_norm_sq"></a>

## 補題 `c1EuclideanDisagreementDirection_norm_sq`

### 式

$$
\lVert v\rVert^2=2
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

方向ベクトルのノルムの二乗は 2 です。

### 証明の概略

1. \(\lVert e_0-e_1\rVert^2=1+1-2\langle e_0,e_1\rangle=2\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolGradient_inner_self"></a>

## 補題 `c1EuclideanSymbolGradient_inner_self`

### 式

$$
\langle\nabla D,\nabla D\rangle=2D
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配の自己内積は、距離の 2 倍です。

### 証明の概略

1. 勾配の定義を展開し、内積の線形性と \(\lVert v\rVert^2=2\)、\(\langle v,x\rangle=x_0-x_1\) を使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_hasGradientAt"></a>

## 補題 `c1EuclideanSymbolDistance_hasGradientAt`

### 式

$$
\nabla D(x)=\tfrac12\langle v,x\rangle v
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

距離は各点で勾配を持ち、その勾配は上の式です。

### 証明の概略

1. 内積の合成として、二乗ノルムの強微分と内積の連続線形写像の微分を合成する。
2. 微分を勾配（Riesz の表現）に直して一致を示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_eq_coordinates"></a>

## 補題 `c1EuclideanSymbolDistance_eq_coordinates`

### 式

$$
D_{\text{Euclid}}(x)=D(\mathrm{coord}(x))
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の距離は、座標を `AgentState` に直した距離に一致します。

### 証明の概略

1. 定義を展開して、成分ごとに計算する（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanEffectivePotential_hasGradientAt"></a>

## 補題 `c1EuclideanEffectivePotential_hasGradientAt`

### 式

$$
\nabla V_{\text{eff}}=3\,\nabla D
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

有効ポテンシャルの勾配は、距離の勾配の 3 倍です。

### 証明の概略

1. 距離の勾配（前の補題）、基礎評価（定数 0）の勾配、定数倍・符号を合成する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.differentiableConsensusOptimalFlow"></a>

## 定義 `differentiableConsensusOptimalFlow`

### 式

$$
\frac{d}{dt}\Phi^{(3)}=\text{ベクトル場}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適流れに「全時刻で微分でき、導関数がベクトル場に一致する」という性質を加えた流れです。

### 証明の概略

1. 指数の引数 \(-3(s-t_0)\) の微分は \(-3\)。成分ごとに \(\exp\) との合成を微分し、ベクトル場の式と一致することを確認する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.euclideanConsensusOptimalFlow"></a>

## 定義 `euclideanConsensusOptimalFlow`

### 式

$$
\text{Euclid 表示での最適流れ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最適流れを、Euclid 表示の状態空間へ、座標変換で移したものです。許容性・フィードバックは同じ。ベクトル場と流れは、座標変換でつなぎます。

### 証明の概略

1. 許容性は元の流れのもの。初期条件・やり直し則は、座標変換が同型であることと元の流れの性質から。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.euclideanConsensusOptimalFlow_coordinates"></a>

## 補題 `euclideanConsensusOptimalFlow_coordinates`

### 式

$$
\mathrm{coord}(\Phi^{E}(x))=\Phi^{(3)}(\mathrm{coord}\,x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の流れは、座標を戻すと元の流れに一致します。

### 証明の概略

1. 定義を展開し、座標変換の逆の性質を使う。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.differentiableEuclideanConsensusOptimalFlow"></a>

## 定義 `differentiableEuclideanConsensusOptimalFlow`

### 式

$$
\text{Euclid 表示でも微分可能}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Euclid 表示の流れも、全時刻で微分でき、導関数がベクトル場に一致します。

### 証明の概略

1. 元の流れの微分可能性に、座標変換（連続線形写像）を合成する（`clm_apply`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanBox"></a>

## 定義 `c1EuclideanBox`

### 式

$$
\{x\mid\mathrm{coord}(x)\in\mathrm{box}\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Euclid 表示での初期箱です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolTarget"></a>

## 定義 `c1EuclideanSymbolTarget`

### 式

$$
\{x\mid x_0=x_1\}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

Euclid 表示での象徴の目標集合（合意の対角線）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolTarget_nonempty"></a>

## 補題 `c1EuclideanSymbolTarget_nonempty`

### 式

$$
\ne\emptyset
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合は空でありません（原点）。

### 証明の概略

1. 原点が条件を満たす（`simp`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolTarget_closed"></a>

## 補題 `c1EuclideanSymbolTarget_closed`

### 式

$$
\text{閉集合}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合は閉集合です。

### 証明の概略

1. 二つの座標関数が連続で、等しい点の集合は閉（`isClosed_eq`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_nonneg"></a>

## 補題 `c1EuclideanSymbolDistance_nonneg`

### 式

$$
D(x)\ge0
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の距離は非負です。

### 証明の概略

1. 二乗の非負性（`positivity`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_zero_iff"></a>

## 補題 `c1EuclideanSymbolDistance_zero_iff`

### 式

$$
D(x)=0\iff x\in\mathrm{Tgt}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

距離が 0 であることと、目標集合に入ることは同値です。

### 証明の概略

1. 内積が \(x_0-x_1\)（前の補題）。\((x_0-x_1)^2=0\iff x_0=x_1\)。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_error_bound"></a>

## 補題 `c1EuclideanSymbolDistance_error_bound`

### 式

$$
\operatorname{dist}(x,\mathrm{Tgt})\le2\sqrt{D(x)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合までの距離は、\(2\sqrt{D(x)}\) 以下です（定理20の誤差境界）。

### 証明の概略

1. 平均 \(m\) の点 \((m,m)\) は目標集合に入る。
2. \(x\) とこの点の距離は \(\sqrt{(x_0-m)^2+(x_1-m)^2}=\lvert x_0-x_1\rvert/\sqrt2\)。
3. これは \(2\sqrt{D(x)}=\lvert x_0-x_1\rvert\) 以下。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.box_isCompact"></a>

## 補題 `box_isCompact`

### 式

$$
\mathrm{box}\ \text{はコンパクト}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

箱はコンパクトです。

### 証明の概略

1. 箱は各座標が閉区間に入る点の集合。閉区間はコンパクトで、積はコンパクト（`isCompact_pi_infinite`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanBox_eq_image"></a>

## 補題 `c1EuclideanBox_eq_image`

### 式

$$
\text{Euclid の箱}=\mathrm{coord}^{-1}\text{ による箱の像}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の箱は、箱を座標変換の逆で移した像です。

### 証明の概略

1. 両方向の包含を、座標変換の逆の性質（`symm_apply_apply`）で示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanBox_isCompact"></a>

## 補題 `c1EuclideanBox_isCompact`

### 式

$$
\text{Euclid の箱はコンパクト}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示の箱もコンパクトです。

### 証明の概略

1. 箱はコンパクトで、連続写像による像もコンパクト（`image`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.euclideanConsensusOptimalFlow_forward_invariant"></a>

## 補題 `euclideanConsensusOptimalFlow_forward_invariant`

### 式

$$
x\in\text{箱}\Rightarrow\Phi^E(x)\in\text{箱}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示でも、箱は前向き不変です。

### 証明の概略

1. 座標を戻すと元の流れ。元の流れの前向き不変性（`consensusOptimalFlow_forward_invariant`）を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.euclideanConsensusOptimalFlow_reachable_closure_eq_box"></a>

## 補題 `euclideanConsensusOptimalFlow_reachable_closure_eq_box`

### 式

$$
\overline{\mathrm{Reach}}=\text{箱}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示での閉到達集合は箱そのものです。

### 証明の概略

1. （⊆）到達点は箱に入り、箱はコンパクトなので閉（`closure_minimal`）。
2. （⊇）箱の点は時刻 \(t_0\) でそのまま到達できる。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalEuclideanFlow_theorem20"></a>

## 定理 `consensusOptimalEuclideanFlow_theorem20`

### 式

$$
D(x(t))\le D(x(t_0))\,e^{-(t-t_0)},\quad \operatorname{dist}(x(t),\mathrm{Tgt})\le2\sqrt{D(x(t_0))}\,e^{-(t-t_0)/2}\to0
$$

### Lean のコメント（日本語訳）

> 有限地平の最適性と定理1・2・4 で使ったのと同じ率 3 の合意の流れに、定理20の原文条件の入口を適用する。

### 補題の説明

定理1・2・4 と有限地平の最適性で使ったのと同じ率 3 の合意の流れに、定理20の「原文条件の入口」を適用します。結論は、象徴の距離 \(D\) の指数減衰と、目標集合までの距離の指数減衰（0 への収束）です。

### 証明の概略

1. Euclid 表示の流れ・箱・目標・距離・勾配を、定理20の入力としてそろえる（\(V_0=2D\)、\(P\equiv1\)、\(s(d)=-d\)、移動度は恒等）。
2. ベクトル場が有効ポテンシャルの勾配の \(-\)（\(\mathrm{id}\) 倍）であること（有効勾配は \(3\nabla D\)）を、前の補題から示す。
3. 箱はコンパクトで前向き不変、距離は非負で零集合 \(=\) 目標、誤差境界 \(2\sqrt D\) を渡す。
4. 定理20の入口 `theorem20_policy_flow_original_condition_conclusion` を適用して結論を得る。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanOptimalField_eq_neg_three_gradient"></a>

## 補題 `c1EuclideanOptimalField_eq_neg_three_gradient`

### 式

$$
F(x)=-3\,\nabla D(x)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最適流れのベクトル場は、距離の勾配の \(-3\) 倍です（勾配流）。

### 証明の概略

1. 座標変換が単射であることを使い、座標ごとの式を計算して一致を示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanOptimalField_contDiff"></a>

## 補題 `c1EuclideanOptimalField_contDiff`

### 式

$$
F\ \text{は C}^1
$$

### Lean のコメント（日本語訳）

> 選ばれた閉ループのベクトル場は、Euclid 表示の状態について大域的に滑らか（したがって局所リプシッツ）である。これは O13 の正則性の条件を、定理20のラッパーとは独立に供給する（ラッパーの API は、この条件を別の引数として要求しない）。

### 補題の説明

選ばれた閉ループのベクトル場は、Euclid 表示の状態について大域的に滑らか（したがって局所リプシッツ）です。定理20の入口の API は、この性質を別の引数として要求しないので、ここで別に示します。

### 証明の概略

1. ベクトル場が \(-3\nabla D\)（前の補題）と一致する。
2. \(\nabla D\) は一次式なので滑らか。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanOptimalField_locallyLipschitz"></a>

## 補題 `c1EuclideanOptimalField_locallyLipschitz`

### 式

$$
F\ \text{は局所リプシッツ}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ベクトル場は局所リプシッツです。

### 証明の概略

1. C¹ 級（前の補題）なら局所リプシッツ。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.c1EuclideanSymbolDistance_optimalFlow_decay"></a>

## 補題 `c1EuclideanSymbolDistance_optimalFlow_decay`

### 式

$$
D(\Phi^E(x))=D(x)\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

Euclid 表示でも、象徴の距離は率 6 で指数減衰します。

### 証明の概略

1. 座標を戻した距離（`c1EuclideanSymbolDistance_eq_coordinates`）に、`c1SymbolDistance_optimalFlow_decay` を適用する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_theorem4"></a>

## 定理 `consensusOptimalFlow_theorem4`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{weightedTCZ}\bigr)\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}\to0
$$

### Lean のコメント（日本語訳）

> 定理4をO02最適rate-3二主体flowへ適用する。Pは非定数だが、V₀に同じPを加えているため実効ポテンシャルでは相殺され、定量的な残差は共有ポテンシャルとなる。

### 補題の説明

最適流れに定理4（臨場感で重みづけた TCZ）を適用した結論です。(1) 閉到達集合に留まる。(2) 加重 TCZ までの距離が \(\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}\) 以下。(3) 0 に収束。\(P\) は定数でないが、\(V_0\) に同じ \(P\) を足してあるので、実効ポテンシャルで打ち消され、残差は共有残差になります。

### 証明の概略

1. 残差が絶対連続・a.e. 下降（率 3）であること（区間の端点は測度 0。内点では閉形式に一致）を示す。
2. 誤差境界は、加重 TCZ が共有 TCZ に一致する（`consensusPresence_weightedTCZ_eq_shared`）ことと、`consensus_global_error_bound` から。
3. 定理4の一般入口に渡し、初期残差で結論を書き換える。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusSelectedHorizonControl"></a>

## 定義 `consensusSelectedHorizonControl`

### 式

$$
u_{(t_0,x)}\equiv3
$$

### Lean のコメント（日本語訳）

> 最適制御選択は初期時刻・二主体状態についてBorel可測。

### 定義の説明

各初期時刻・二主体状態に対して選ぶ有限地平の制御（定数 3）です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusSelectedHorizonControl_measurable"></a>

## 補題 `consensusSelectedHorizonControl_measurable`

### 式

$$
\text{Borel 可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選択の規則は Borel 可測（定数）です。

### 証明の概略

1. `measurable_const`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusSelectedHorizonControl_rightLimit"></a>

## 補題 `consensusSelectedHorizonControl_rightLimit`

### 式

$$
\lim_{s\downarrow t_0}u(s)=\pi(x,t_0)
$$

### Lean のコメント（日本語訳）

> 定数最適制御列の開始点右極限は最適feedback `3`。

### 補題の説明

開始点の右極限が、最適なフィードバック 3 に一致します（反復ホライズン制御の条件）。

### 証明の概略

1. 両辺とも定数 3（`tendsto_const_nhds`）。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_eq_selected_orbit"></a>

## 補題 `consensusOptimalFlow_eq_selected_orbit`

### 式

$$
\Phi^{(3)}(x)=\text{state}_{u_{\max}}(x)
$$

### Lean のコメント（日本語訳）

> 選ばれた最適列の積分軌道と同じ制御の閉ループH-flowは同じ二主体状態を作る。

### 補題の説明

最適流れと、最大ゲイン信号で動かした積分軌道は、同じ状態を作ります。

### 証明の概略

1. 最大ゲインの積分軌道は \(d\,e^{-3(t-t_0)}\)（`c1MaxGain_accumulation`）。
2. 両辺を成分ごとに式で書いて一致を示す。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensus_two_distinct_admissible_controls"></a>

## 補題 `consensus_two_distinct_admissible_controls`

### 式

$$
u_0\ne u_{\max}
$$

### Lean のコメント（日本語訳）

> ゼロと最大ゲインは異なる許容制御列なので、方策族は非退化。

### 補題の説明

ゼロのゲインと最大ゲインは異なる許容制御なので、方策の集合は一点でなく、非退化です。

### 証明の概略

1. 一次元モデルの `c1_two_distinct_admissible_gains`。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_theorem2_distance"></a>

## 補題 `consensusOptimalFlow_theorem2_distance`

### 式

$$
\operatorname{dist}\bigl(x(t),\mathrm{sharedTCZ}\bigr)\le\sqrt{\Phi_2(x_0)}\,e^{-3(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 最適ゲインflowは定理2と同じ共有TCZへ、時計変換後の指数率で収束する。

`consensusOptimalFlow` は旧 `consensusFlow` の1.5倍速い時間再パラメータ化なので、TCZと残差は同じで距離率は2から3へ変わる。

### 補題の説明

最適流れは、定理2の共有 TCZ に、率 3 で近づきます。この流れは、率 2 の合意の流れの時間を 1.5 倍に速めたものなので、TCZ と残差は同じで、率が 2 から 3 に変わります。

### 証明の概略

1. \(t_0=t\) のときは、全箱の誤差境界（`consensus_global_error_bound`）から。
2. \(t_0<t\) のときは、率 2 の流れに時間変換で書き換え（`consensusOptimalFlow_eq_retimed`）、`consensusFlow_theorem2` の距離評価に時間変換後の時刻を入れて指数を整理する。

----

<a id="Tomabechi.Consistency.ConsistencyC1Consensus.consensusOptimalFlow_theorem2_full"></a>

## 定理 `consensusOptimalFlow_theorem2_full`

### 式

$$
\text{距離}\le\sqrt{\Phi_2}\,e^{-3(t-t_0)},\ \text{個人・辺の誤差}\le\frac{\Phi_2}{w}\,e^{-6(t-t_0)}
$$

### Lean のコメント（日本語訳）

> 定理2をrate-3最適flowへ適用し、共有距離に加えて個人残差と辺不整合の指数誤差も、箱内の任意の初期対・全ての後続時刻で与える。

### 補題の説明

最適流れへの定理2の完全版です。(1) 箱に留まり、共有 TCZ までの距離が \(\sqrt{\Phi_2}\,e^{-3(t-t_0)}\) 以下。(2) 各主体の個人の残差が \((\Phi_2/w_i)\,e^{-6(t-t_0)}\) 以下。(3) 各辺の不整合が \((\Phi_2/w_e)\,e^{-6(t-t_0)}\) 以下。箱の内側の任意の初期点・任意の後続時刻で成り立ちます。

### 証明の概略

1. 率 2 の流れに時間変換して、`consensusFlow_theorem2` の三つの結論を適用する。
2. 時間変換後の指数 \(-4\cdot\tfrac32(t-t_0)=-6(t-t_0)\) と、距離の \(-2\cdot\tfrac32=-3\) を整理する。

----


## コメント修正記録

節のコメントで、利用可能情報を `{∅, {0}, {0,1}}` としていたのを、定義（全体 `{0,1}` を含まない）に合わせて `{∅, {0}}` に直しました（コメントのみ）。
