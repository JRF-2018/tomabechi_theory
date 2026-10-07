# Tomabechi/Consistency/ConsistencyC6_ControlCore.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_ControlCore.lean`](../Tomabechi/Consistency/ConsistencyC6_ControlCore.lean)（C6: 中心と累積ゲインを共有する制御流の核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 反復ホライズン制御 | 各時刻で有限先の最適制御を解き、最初の制御だけ使うことを繰り返す方式。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| Banach の不動点定理 | 完備距離空間の縮小写像に唯一の固定点があり、反復で幾何収束する。 |
| 逆極限 | 射影で整合的な点列（各層の点の組）全体のなす空間。 |
| 固定点 | \(F(x)=x\) をみたす点。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| 一様可積分（UI） | 積分の「尾」が一様に小さい関数族。極限と積分の交換（Vitali）に使う。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 決定論的方策 | ランダムさのない（入力から出力が決まる）方策。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| 同時分布 | 複数の確率変数の組の確率分布。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**中心と累積ゲインを共有する制御流の核**を作るファイルです。C1・C3・C4・C5 を、中心 \(c\)、累積ゲイン \(A\)、エントロピー増分 \(E\) を持つ、**一つの状態更新則**から取り出します。C1/C5 は、最適方策だけでなく、元の全ゲイン族を保持します。中心・許容族・基礎評価が異なる文脈を、同一の最適軌道へ強制的に同定しません。

主な内容は次のとおりです。

* **核：** 状態更新 \(\mathrm{step}(c,A,E)\)（認知座標 \(q\) は中心へ \(e^{-A}\) 倍で縮み、物理観測は収支 \((y+q^2)'=\sigma\) を満たす）。二次評価 \(\Phi_c=\tfrac12(q-c)^2\) は \(e^{-2A}\) 倍される。再中心化と可換。
* **C1・C3・C4・C5 の回収：** C1 の全許容ゲインの軌道、C3 の凍結した二次軌道・谷の証人の軌道、C4 の全履歴・全初期値の勾配流、C5 の全有界可測ゲインのベクトル軌道が、**同じ核の射影**として得られる。評価は係数つきで対応する（C1 は \(1+16\Phi\)、C5 の走行費は \(6\Phi\)、最適価値は \(2\Phi\)）。
* **C3/A7 の接続した経路：** 元の C3 の段を、完全状態（認知座標と物理観測）で、率 3 のエントロピー生成に合わせて接続する。全時刻で観測エントロピーは \(3t\)、再訪しない（定理 15→23 の入口）。一つの C1 の許容ゲインへ貼り合わせられる。
* **結合法則：** 上の経路・C1 の中心サンプルを、既存の C1/C2/C4/C5/C3 の結合法則に付加し、元の法則を周辺として回収する。
* **アダプター：** C4 の流れ・TCZ、共通ポテンシャル、段 \(n\) の結合法則のアダプター。

### 0.2 このファイルが証明していないこと

* この核は、**共有署名・全費用・全 SCM の統合の存在の証人ではありません**。
* C1 の評価と C5 の走行費は、係数つきで共通の二次評価に対応しますが、基礎費用そのものが一致するわけではありません（合意点ですら等しくない）。
* 中心を変更する段間の切り替えでは、端点の一致を別に要求します。
* C3/A7 の接続した経路が C1 の最大ゲインの選択軌道と同一だとは、主張しません。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> C1・C3・C4・C5を、中心c、累積ゲインA、エントロピー増分Eを持つ一つの状態更新則から取り出す。C1/C5は最適方策だけでなく元の全ゲイン族を保持する。中心・許容族・基礎評価が異なるcontextを、同一の最適軌道へ強制的に同定しない。この核は共有署名・全費用・全SCMの統合存在証人ではない。

---

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep"></a>

## 定義 `centeredGainEntropyStep`

### 式

$$
q'=g\,(c-q),\ \ (y+q^2)'=\sigma
$$

### Lean のコメント（日本語訳）

> q'=g(c-q)、(y+q²)'=σ の累積ゲインA・収支増分Eに対する状態更新。状態にはqと物理観測yを置き、独立時計は置かない。

### 定義の説明

中心 \(c\)・累積ゲイン \(A\)・エントロピー増分 \(E\) に対する**状態更新**です。認知座標 \(q\) を、中心 \(c\) に向けて \(e^{-A}\) 倍だけ縮め、物理観測 \(y\) を、収支 \((y+q^2)'=\sigma\) を満たすように更新します。状態には \(q\) と物理観測 \(y\) を置き、独立な時計の座標は置きません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_cognitive"></a>

## 補題 `centeredGainEntropyStep_cognitive`

### 式

$$
q_{\rm new}=c+(q-c)\,e^{-A}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

更新後の認知座標は、\(c+(q-c)e^{-A}\) です。

### 証明の概略

1. 定義を展開する。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_entropy"></a>

## 補題 `centeredGainEntropyStep_entropy`

### 式

$$
\mathrm{entropy}(\mathrm{step}(z))=\mathrm{entropy}(z)+E
$$

### Lean のコメント（日本語訳）

> 同じ観測から収支増分を回収する。

### 補題の説明

更新で、観測されるエントロピーは、\(E\) だけ増えます。

### 証明の概略

1. 定義を展開して `ring`。

----

<a id="Tomabechi.Consistency.C6.centeredQuadraticPotential"></a>

## 定義 `centeredQuadraticPotential`

### 式

$$
\Phi_c(z)=\tfrac12(q-c)^2
$$

### Lean のコメント（日本語訳）

> 共通核の中心からの二次評価。C3/C4の凍結谷・勾配流評価に対応する。

### 定義の説明

共通核の、中心 \(c\) からの**二次評価** \(\tfrac12(q-c)^2\) です。C3/C4 の凍結谷・勾配流の評価に対応します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.centeredQuadraticPotential_step"></a>

## 補題 `centeredQuadraticPotential_step`

### 式

$$
\Phi_c(\mathrm{step})=\Phi_c(z)\,e^{-2A}
$$

### Lean のコメント（日本語訳）

> 中心からの二次評価は、累積ゲインAだけで `exp(-2A)` 倍される。物理収支Eはこの評価に影響しない。

### 補題の説明

二次評価は、累積ゲイン \(A\) だけで \(e^{-2A}\) 倍されます。物理収支 \(E\) は、この評価に影響しません。

### 証明の概略

1. 更新後の認知座標の式から、\((q-c)^2e^{-2A}\)。

----

<a id="Tomabechi.Consistency.C6.centeredQuadraticPotential_eq_C4"></a>

## 補題 `centeredQuadraticPotential_eq_C4`

### 式

$$
\Phi_c=\text{C4 の履歴別評価}
$$

### Lean のコメント（日本語訳）

> C4の履歴別評価は、同じ認知座標上の共通二次評価そのもの。これは評価関数の同定で、逆極限やTCZの集合同定は別の接続義務である。

### 補題の説明

C4 の履歴別評価は、同じ認知座標の上の、共通の二次評価**そのもの**です。これは評価関数の同定で、逆極限や TCZ の集合の同定は、別の接続の義務です。

### 証明の概略

1. C4 の評価の定義を展開。

----

<a id="Tomabechi.Consistency.C6.c4Potential_flow_decay"></a>

## 補題 `c4Potential_flow_decay`

### 式

$$
V_h(\varphi_t(x))=V_h(x)\,e^{-2t}
$$

### Lean のコメント（日本語訳）

> C4の実勾配流に沿う評価減衰を、共通核の二次評価減衰と同じ式で表す。

### 補題の説明

C4 の実際の勾配流に沿う評価の減衰を、共通核の二次評価の減衰と、同じ式で表します。

### 証明の概略

1. 流れの式 \(c+(x-c)e^{-t}\) を、評価に代入。

----

<a id="Tomabechi.Consistency.C6.centeredQuadraticPotential_eq_C3_stage"></a>

## 補題 `centeredQuadraticPotential_eq_C3_stage`

### 式

$$
\Phi_c=\text{C3 の段の実効二次谷評価}
$$

### Lean のコメント（日本語訳）

> C3の元H-stageで使う実効二次谷評価も、同じ共有評価のpullbackである。ここでは元の `hStageSequence` の段を保ち、別の谷列を作り直さない。

### 補題の説明

C3 の元の H-stage で使う実効の二次谷評価も、同じ共有評価の引き戻しです。ここでは元の `hStageSequence` の段を保ち、別の谷列を作り直しません。

### 証明の概略

1. 段の実効ポテンシャルの定義を展開して、二次式を比べる。

----

<a id="Tomabechi.Consistency.C6.c5RunningCost_eq_six_centeredPotential"></a>

## 補題 `c5RunningCost_eq_six_centeredPotential`

### 式

$$
\text{C5 の走行費}=6\,\Phi_c
$$

### Lean のコメント（日本語訳）

> C5上位走行費は共通核の二次評価の6倍。係数を保持するので、C1/C5の異なる基礎評価を同一視しない。

### 補題の説明

C5 の上位の走行費は、共通核の二次評価の **6 倍**です。係数を保持するので、C1/C5 の異なる基礎評価を同一視しません。

### 証明の概略

1. C5 の走行費の定義と、完全状態の射影の式から、係数を比べる。

----

<a id="Tomabechi.Consistency.C6.c5OptimalValue_eq_two_centeredPotential"></a>

## 補題 `c5OptimalValue_eq_two_centeredPotential`

### 式

$$
V^*_{\rm C5}=2\,\Phi_c
$$

### Lean のコメント（日本語訳）

> C5上位最適価値は共通核の二次評価の2倍である。

### 補題の説明

C5 の上位の最適価値は、共通核の二次評価の **2 倍**です。

### 証明の概略

1. 最適価値の明示式（割引 1・走行費 6）から。

----

<a id="Tomabechi.Consistency.C6.c1V0_eq_baseline_add_centeredPotential"></a>

## 補題 `c1V0_eq_baseline_add_centeredPotential`

### 式

$$
V_0^{\rm C1}=1+16\,\Phi_c\ \ (\text{箱の上})
$$

### Lean のコメント（日本語訳）

> C1定理1の箱上評価は共通核二次評価の16倍にbaseline 1を加えたもの。これにより共有する残差とcontext固有のbaselineを明示的に分ける。

### 補題の説明

C1 の定理 1 の箱の上の評価は、共通核の二次評価の **16 倍に基準値 1 を加えた**ものです。これにより、共有する残差と、文脈に固有の基準値を、明示的に分けます。

### 証明の概略

1. 箱の内部で個人の閾値の残差が消えること（`DA.potential`）と、二次式の展開。

----

<a id="Tomabechi.Consistency.C6.c1V0_ne_C5_runningCost_at_consensus"></a>

## 補題 `c1V0_ne_C5_runningCost_at_consensus`

### 式

$$
V_0^{\rm C1}(0)\ne\text{C5 の走行費}
$$

### Lean のコメント（日本語訳）

> C1定理1の基礎評価とC5上位走行費は、合意点ですら等しくない。残差の係数付き対応を、同一contextの基礎費用そのものの一致と読み替えてはならない。

### 補題の説明

C1 の定理 1 の基礎評価と、C5 の上位の走行費は、合意点ですら**等しくありません**。残差の係数つきの対応を、同一の文脈の基礎費用そのものの一致と、読み替えてはなりません。

### 証明の概略

1. 合意点での値を計算して比べる（1 と 0）。

----

<a id="Tomabechi.Consistency.C6.recenterEntropyState"></a>

## 定義 `recenterEntropyState`

### 式

$$
(q,y)\mapsto(q+d-c,\ \mathrm{entropy}-(q+d-c)^2)
$$

### Lean のコメント（日本語訳）

> 中心cの認知座標を中心dへ平行移動し、物理観測を補正して総エントロピーを保つ。C1の座標上の中心1を、共通束の頂点と無条件に同一視せずに移送するための写像。

### 定義の説明

中心 \(c\) の認知座標を中心 \(d\) へ平行移動し、物理観測を補正して、総エントロピーを保つ写像です。C1 の座標上の中心 1 を、共通束の頂点と無条件に同一視せずに移送するために使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.recenterEntropyState_entropy"></a>

## 補題 `recenterEntropyState_entropy`

### 式

$$
\text{再中心化は総エントロピーを変えない}
$$

### Lean のコメント（日本語訳）

> 再中心化は物理観測と認知二乗の総和を変えない。

### 補題の説明

再中心化は、物理観測と認知座標の二乗の総和を変えません。

### 証明の概略

1. 定義を展開して `simp`。

----

<a id="Tomabechi.Consistency.C6.recenterEntropyState_step"></a>

## 補題 `recenterEntropyState_step`

### 式

$$
\text{再中心化は制御更新と可換}
$$

### Lean のコメント（日本語訳）

> 再中心化は同じ累積ゲイン・同じ生成量の制御更新に可換する。

### 補題の説明

再中心化は、同じ累積ゲイン・同じ生成量の制御更新と可換です。

### 証明の概略

1. 両辺の座標を計算して比べる。

----

<a id="Tomabechi.Consistency.C6.recenterEntropyState_potential"></a>

## 補題 `recenterEntropyState_potential`

### 式

$$
\Phi_d(\mathrm{recenter}(z))=\Phi_c(z)
$$

### Lean のコメント（日本語訳）

> 再中心化で同じ二次残差を保持する。baselineや閾値は変更しない。

### 補題の説明

再中心化で、同じ二次残差が保持されます。基準値や閾値は変更しません。

### 証明の概略

1. 認知座標の差が \(q+d-c-d=q-c\)。

----

<a id="Tomabechi.Consistency.C6.recenterEntropyState_inverse"></a>

## 補題 `recenterEntropyState_inverse`

### 式

$$
\mathrm{recenter}_{d,c}\circ\mathrm{recenter}_{c,d}=\mathrm{id}
$$

### Lean のコメント（日本語訳）

> 逆向きの再中心化で元の完全状態を復元する。

### 補題の説明

逆向きの再中心化で、元の完全状態を復元します。

### 証明の概略

1. 座標で場合分けして `ring`。

----

<a id="Tomabechi.Consistency.C6.c1V0_eq_recentered_finite_layer_evaluation"></a>

## 補題 `c1V0_eq_recentered_finite_layer_evaluation`

### 式

$$
V_0^{\rm C1}=\text{再中心化した有限層の評価}（\text{正の基準値と係数を保つ）}
$$

### Lean のコメント（日本語訳）

> C1 の評価を有限層 `n` の中心へ移しても、正の基準値と係数を保つ。これは有限層のC1側評価の保存式であり、C5頂点の走行費とは別のcontextに置く。

### 補題の説明

C1 の評価を、有限層 \(n\) の中心へ移しても、正の基準値と係数を保ちます。これは、有限層の C1 側の評価の保存式であり、C5 の頂点の走行費とは別の文脈に置きます。

### 証明の概略

1. 再中心化の補題と、C1 の評価の式。

----

<a id="Tomabechi.Consistency.C6.c1V0_eq_finite_layer_coordinate"></a>

## 補題 `c1V0_eq_finite_layer_coordinate`

### 式

$$
V_0^{\rm C1}=1+16\cdot\tfrac12(\text{移した座標}-\text{有限層の中心})^2
$$

### Lean のコメント（日本語訳）

> 再中心化後の有限層評価は、移した座標と有限層中心との差で表せる。

### 補題の説明

再中心化後の有限層の評価は、移した座標と、有限層の中心との差で表せます。

### 証明の概略

1. 前の補題を展開。

----

<a id="Tomabechi.Consistency.C6.c1FiniteLayer_discounted_cost_minimal_pointwise"></a>

## 補題 `c1FiniteLayer_discounted_cost_minimal_pointwise`

### 式

$$
\text{最大ゲインの割引被積分量}\le\text{任意の可測ゲインのそれ}
$$

### Lean のコメント（日本語訳）

> 有限層でC1評価を走行費に使うとき、最大ゲインの割引被積分量はすべての可測 `[0,3]` ゲイン競合以下となる。割引率は定理24/26の `rho=1`。

### 補題の説明

有限層で C1 の評価を走行費に使うとき、最大ゲインの割引被積分量は、すべての可測 \([0,3]\) ゲインの競合以下となります。割引率は、定理 24/26 の \(\rho=1\) です。

### 証明の概略

1. 最大ゲインの軌道の二乗の比較（`c1MaxGain_orbit_sq_le`）と、割引の重みの非負性。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_initial"></a>

## 補題 `centeredGainEntropyStep_initial`

### 式

$$
\mathrm{step}(c,0,0,z)=z
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

累積ゲイン 0・生成 0 の更新は、恒等です。

### 証明の概略

1. 定義を展開。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_add"></a>

## 補題 `centeredGainEntropyStep_add`

### 式

$$
\mathrm{step}_{B,F}\circ\mathrm{step}_{A,E}=\mathrm{step}_{A+B,E+F}
$$

### Lean のコメント（日本語訳）

> 同じ凍結中心で累積ゲイン・収支が加法的なら、全状態更新も再始動する。中心を変更する段間切替は別に端点一致を要求する。

### 補題の説明

同じ凍結中心で、累積ゲイン・収支が加法的なら、全状態更新も再始動します（\(\mathrm{step}_{B,F}\circ\mathrm{step}_{A,E}=\mathrm{step}_{A+B,E+F}\)）。中心を変更する段間の切り替えは、別に端点の一致を要求します。

### 証明の概略

1. 認知座標は \(e^{-A}e^{-B}=e^{-(A+B)}\)、物理座標は収支の加法性。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_cognitive_hasDerivAt"></a>

## 補題 `centeredGainEntropyStep_cognitive_hasDerivAt`

### 式

$$
\dot A=g\Rightarrow \dot q=g(c-q)
$$

### Lean のコメント（日本語訳）

> 累積ゲインAの導関数がgなら、同じ状態則の認知座標は指定制御場を満たす。可測ゲインのa.e.版にも、この補題を各微分可能点で適用できる。

### 補題の説明

累積ゲイン \(A\) の導関数が \(g\) なら、同じ状態則の認知座標は、指定した制御場 \(\dot q=g(c-q)\) を満たします。可測ゲインのほとんど至る所の版にも、この補題を、各微分可能点で適用できます。

### 証明の概略

1. 指数関数の合成関数の微分。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_physical_hasDerivAt"></a>

## 補題 `centeredGainEntropyStep_physical_hasDerivAt`

### 式

$$
\dot A=g,\ \dot E=\sigma\Rightarrow\dot y=\sigma-2q\,\dot q
$$

### Lean のコメント（日本語訳）

> 物理観測の微分は同じ認知微分と生成率σから定まる。エントロピー収支を独立な時計座標で代用しない。

### 補題の説明

物理観測の微分は、同じ認知座標の微分と生成率 \(\sigma\) から定まります。エントロピー収支を独立な時計の座標で代用しません。

### 証明の概略

1. 収支の式 \((y+q^2)'=\sigma\) と積の微分。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyField"></a>

## 定義 `centeredGainEntropyField`

### 式

$$
F_{c,g,\sigma}(z)=\bigl(g(c-q),\ \sigma-2q\,g(c-q)\bigr)
$$

### Lean のコメント（日本語訳）

> 中心c・実ゲインg・生成率σを引数に持つ共通制御場。

### 定義の説明

中心 \(c\)・実ゲイン \(g\)・生成率 \(\sigma\) を引数に持つ、共通の制御場です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_hasDerivAt"></a>

## 補題 `centeredGainEntropyStep_hasDerivAt`

### 式

$$
\frac{d}{dt}\mathrm{step}=F_{c,g,\sigma}(\mathrm{step})
$$

### Lean のコメント（日本語訳）

> 状態更新は、この同じ制御場の微分方程式を満たす。

### 補題の説明

状態更新は、この同じ制御場の微分方程式を満たします。

### 証明の概略

1. 二つの座標の微分の補題を合わせる。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_eq_completeEntropyFlow"></a>

## 補題 `centeredGainEntropyStep_eq_completeEntropyFlow`

### 式

$$
\mathrm{step}(1,t,t,z)=\text{C2 の完全エントロピー流}
$$

### Lean のコメント（日本語訳）

> 元のC2共通エントロピーflowは、この核のc=1、A=E=tの場合。

### 補題の説明

元の C2 の共通エントロピー流は、この核の \(c=1\)、\(A=E=t\) の場合です。

### 証明の概略

1. 座標ごとに計算して `ring`。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_all_C1_controls"></a>

## 補題 `centeredGainEntropyStep_projects_all_C1_controls`

### 式

$$
\text{C1 の全許容ゲイン信号の実軌道}=\text{核の更新の射影}
$$

### Lean のコメント（日本語訳）

> C1の全許容ゲイン信号の実軌道を、同じ状態更新の射影から回収する。最適ゲインだけの一致やC5へのゲイン族同一視には限定しない。

### 補題の説明

C1 の全許容ゲイン信号の実軌道を、同じ状態更新の射影から回収します。最適ゲインだけの一致や、C5 へのゲイン族の同一視には限定しません。

### 証明の概略

1. C1 の軌道の閉形式（累積ゲイン \(\int u\) による）と、核の更新の式を比べる。

----

<a id="Tomabechi.Consistency.C6.c1CoreTrajectory"></a>

## 定義 `c1CoreTrajectory`

### 式

$$
\mathrm{step}(1,\ \textstyle\int u,\ 0,\ z_0)
$$

### Lean のコメント（日本語訳）

> C1の任意ゲイン信号を共有核上で表す完全状態軌道。平均は別の `MeanCompleteState` 成分に保存し、この状態では不一致座標を追う。

### 定義の説明

C1 の任意のゲイン信号を、共有核の上で表す、完全状態の軌道です。平均は別の `MeanCompleteState` の成分に保存し、この状態では不一致座標を追います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1CoreTrajectory_projects_controlledState"></a>

## 補題 `c1CoreTrajectory_projects_controlledState`

### 式

$$
\text{核の軌道の C1 への射影}=\text{実二主体軌道}
$$

### Lean のコメント（日本語訳）

> C1の全許容ゲインについて、核軌道のC1射影が実二主体軌道そのもの。

### 補題の説明

C1 の全許容ゲインについて、核の軌道の C1 への射影が、実際の二主体軌道そのものです。

### 証明の概略

1. `centeredGainEntropyStep_projects_all_C1_controls`。

----

<a id="Tomabechi.Consistency.C6.c1CoreTrajectory_theorem1_runningCost"></a>

## 補題 `c1CoreTrajectory_theorem1_runningCost`

### 式

$$
\text{定理 1 の被積分費用}=1+16\,\Phi_c
$$

### Lean のコメント（日本語訳）

> C1の定理1被積分費用は、共有核の基準値1と二次評価16Pの和。箱内条件を使って、原文の `DA.potential` を元の二主体状態から評価する。

### 補題の説明

C1 の定理 1 の被積分費用は、共有核の基準値 1 と、二次評価 \(16\Phi\) の和です。箱の内部の条件を使って、原文の `DA.potential` を、元の二主体の状態から評価します。

### 証明の概略

1. 箱の内部での個人の閾値の残差の消滅と、核の軌道の射影。

----

<a id="Tomabechi.Consistency.C6.c1CoreTheorem1HorizonCost"></a>

## 定義 `c1CoreTheorem1HorizonCost`

### 式

$$
\int_{T}^{T+H}\bigl(1+16\Phi\bigr)\,dt
$$

### Lean のコメント（日本語訳）

> C1定理1の有限地平費用を、核評価とbaselineに分けて積分する表示。

### 定義の説明

C1 の定理 1 の有限地平の費用を、核の評価と基準値に分けて積分する表示です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c1CoreTheorem1HorizonCost_eq_dataCost"></a>

## 補題 `c1CoreTheorem1HorizonCost_eq_dataCost`

### 式

$$
\text{核側の表示}=\text{実際の定理 1 の費用積分}
$$

### Lean のコメント（日本語訳）

> C1の実際の定理1費用積分は、共有核上の基準費用＋二次評価積分。

### 補題の説明

C1 の実際の定理 1 の費用積分は、共有核の上の基準費用と二次評価の積分の和に等しいです。

### 証明の概略

1. 被積分関数の一致（前の補題）。

----

<a id="Tomabechi.Consistency.C6.c1CoreTheorem1HorizonCost_optimal_minimal"></a>

## 補題 `c1CoreTheorem1HorizonCost_optimal_minimal`

### 式

$$
\text{最大ゲインは核側の有限地平費用でも最小}
$$

### Lean のコメント（日本語訳）

> C1の最大ゲインは、共有核の有限地平費用表示でも全許容ゲインに対し最小。

### 補題の説明

C1 の最大ゲインは、共有核の有限地平の費用表示でも、全許容ゲインに対して最小です。

### 証明の概略

1. 最大ゲインの二乗の比較（`c1MaxGain_orbit_sq_le`）を、積分に移す。

----

<a id="Tomabechi.Consistency.C6.C6C1C5OptimalityAdapter"></a>

## 構造体 `C6C1C5OptimalityAdapter`

### 式

$$
\text{C1 の元の費用 argmin と、C5 へ写した実 feedback の最適性を一つのアダプターに束ねる}
$$

### Lean のコメント（日本語訳）

> C1の元費用argminと、その同じ箱contextからC5へ写した実feedbackの最適性を一つの保存adapterに束ねる。

### 定義の説明

C1 の元の費用 argmin と、その同じ箱の文脈から C5 へ写した実際のフィードバックの最適性を、一つの保存アダプターに束ねたものです。フィールドは、状態・費用のアダプター、保存した平均を内部に持つ完全状態（現在時刻の C1 二主体の状態と C2 の完全状態を、同じ状態から読む）、平均の保存、O24 で型を分けた Self・Ego・TCZ を保持するアダプター、O24 の流れは同じ文脈の C1 の選択の流れ、O24 の型つき TCZ は C1 の定理 1 の目標に一致、TCZ の所属は C5 の零価値目標の所属としても読める、定理 1 の実際の有限地平費用と共有二次評価の核の上の費用の一致、最大ゲインは元の定理 1 の費用に対して全許容入力中で最小、同じ文脈から C5 へ射影した方策は C5 の各有限地平でも実データの最適方策、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C5OptimalityAdapter"></a>

## 定義 `c6C1C5OptimalityAdapter`

### 式

$$
\mathrm{C6C1C5OptimalityAdapter}(x,t_0,t)
$$

### Lean のコメント（日本語訳）

> box内の全contextでC1定理1の全競合最小性とC5の実方策最適性を構成する。

### 定義の説明

箱の内部の全文脈で、C1 の定理 1 の全競合に対する最小性と、C5 の実方策の最適性を構成します。

### 証明の概略

1. 各フィールドは、上の補題（核の軌道の射影・費用の一致・最小性）と、C5 の既存の最適性の定理から。

----

<a id="Tomabechi.Consistency.C6.meanCenteredGainEntropyStep"></a>

## 定義 `meanCenteredGainEntropyStep`

### 式

$$
(m,z)\mapsto(m,\mathrm{step}(z))
$$

### Lean のコメント（日本語訳）

> 保存平均を状態内に保持した同じ更新則。

### 定義の説明

保存される平均を状態の中に保持した、同じ更新則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.meanCenteredGainEntropyStep_projects_all_C1_controls"></a>

## 補題 `meanCenteredGainEntropyStep_projects_all_C1_controls`

### 式

$$
\text{C1 の全制御族の射影は、現在の完全状態だけから読める}
$$

### Lean のコメント（日本語訳）

> C1全制御族の射影は、初期平均を外部引数にせず、現在の完全状態だけから読める。

### 補題の説明

C1 の全制御族の射影は、初期の平均を外部の引数にせず、現在の完全状態だけから読めます。

### 証明の概略

1. 平均が状態の成分として保存されることと、前の射影の補題。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_quadraticFrozenOrbit"></a>

## 補題 `centeredGainEntropyStep_projects_quadraticFrozenOrbit`

### 式

$$
\text{C3 の凍結した二次軌道}=\text{中心 }c\text{・ゲイン 1 の核の更新の射影}
$$

### Lean のコメント（日本語訳）

> C3の凍結二次軌道は、中心c・ゲイン1の同じ核から得る。

### 補題の説明

C3 の凍結した二次軌道は、中心 \(c\)・ゲイン 1 の同じ核から得られます。

### 証明の概略

1. 凍結軌道の式 \(c+(x-c)e^{-(t-s)}\) と、更新後の認知座標の式を比べる。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_C3_witness"></a>

## 補題 `centeredGainEntropyStep_projects_C3_witness`

### 式

$$
\text{元の C3 の谷の証人が選ぶ軌道}=\text{核の更新の射影}
$$

### Lean のコメント（日本語訳）

> 元C3の谷証人が選ぶ軌道にも一致する。中心到達のサンプリングへ置き換えない。

### 補題の説明

元の C3 の谷の証人が選ぶ軌道にも一致します。中心に到達するサンプリングに置き換えません。

### 証明の概略

1. 谷の証人の軌道が凍結軌道であること（開始時刻以降）と、前の補題。

----

<a id="Tomabechi.Consistency.C6.c3CoreStageTrajectory"></a>

## 定義 `c3CoreStageTrajectory`

### 式

$$
\text{C3 の段 }n\text{ の完全状態の拡張}
$$

### Lean のコメント（日本語訳）

> C3各段の完全状態拡張。物理観測座標yを保ち、累積観測増分Eには`q(t)^2-q(start)^2` を入れるため、E−q²の変化が打ち消し合う。

### 定義の説明

C3 の各段の完全状態の拡張です。物理観測の座標 \(y\) を保ち、累積の観測増分 \(E\) には \(q(t)^2-q(\mathrm{start})^2\) を入れるため、\(E-q^2\) の変化が打ち消し合います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3CoreStageTrajectory_cognitive"></a>

## 補題 `c3CoreStageTrajectory_cognitive`

### 式

$$
\text{認知座標}=\text{凍結した二次軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の完全状態の認知座標は、凍結した二次軌道です。

### 証明の概略

1. 定義を展開して、更新後の認知座標の式。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_physical_preserved_by_quadraticIncrement"></a>

## 補題 `centeredGainEntropyStep_physical_preserved_by_quadraticIncrement`

### 式

$$
E=q^2-q_0^2\Rightarrow\text{物理座標は不変}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

累積の観測増分が、認知座標の二乗の増分に等しいなら、物理座標は変わりません。

### 証明の概略

1. 収支の式から、\(y\) の変化が打ち消し合う。

----

<a id="Tomabechi.Consistency.C6.c3CoreStageTrajectory_physical"></a>

## 補題 `c3CoreStageTrajectory_physical`

### 式

$$
\text{物理座標}\equiv y
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の完全状態の物理座標は、常に \(y\) です。

### 証明の概略

1. 前の補題を適用する。

----

<a id="Tomabechi.Consistency.C6.c3CoreStageTrajectory_entropyObserved"></a>

## 補題 `c3CoreStageTrajectory_entropyObserved`

### 式

$$
\text{観測されるエントロピー}=q^2\ \ (y=0)
$$

### Lean のコメント（日本語訳）

> このC3拡張で観測される完全状態エントロピーは、段内では認知座標の二乗。

### 補題の説明

この C3 の拡張で観測される完全状態のエントロピーは、段内では、認知座標の二乗です。

### 証明の概略

1. 物理座標が 0 で、観測エントロピーが \(y+q^2\)。

----

<a id="Tomabechi.Consistency.C6.c3CoreStage_entropy_increases"></a>

## 補題 `c3CoreStage_entropy_increases`

### 式

$$
\text{段の終点でのエントロピー}>\text{始点でのエントロピー}
$$

### Lean のコメント（日本語訳）

> 元C3各段は共有核の観測エントロピーを真に増加させる。増加は時刻カウンタではなく、段の実軌道が初期点から中心へ動いた二乗差である。

### 補題の説明

元の C3 の各段は、共有核の観測エントロピーを、**真に増加**させます。増加は時刻のカウンタではなく、段の実際の軌道が初期点から中心へ動いた、二乗差です。

### 証明の概略

1. 観測エントロピーが \(q^2\) で、初期点と終点の認知座標が、中心との距離で、異なる（初期点が中心でなく、段の滞在時間が正）。

----

<a id="Tomabechi.Consistency.C6.c3CoreStageTrajectory_initial"></a>

## 補題 `c3CoreStageTrajectory_initial`

### 式

$$
\text{初期時刻での完全状態}=(x_0,y)
$$

### Lean のコメント（日本語訳）

> 初期時刻では完全状態も正確に入力を再現する。

### 補題の説明

初期時刻では、完全状態も、入力を正確に再現します。

### 証明の概略

1. 指数が 1、\(E=0\)。

----

<a id="Tomabechi.Consistency.C6.C6C3CoreStageAdapter"></a>

## 構造体 `C6C3CoreStageAdapter`

### 式

$$
\text{元の C3-H-stage を、共有状態核・同じ段時間・S7 の情報法則と同時に保持する}
$$

### Lean のコメント（日本語訳）

> 元のC3-H-stageを、共有状態核・同じ段時間・S7情報lawと同時に保持するadapter。完全状態の第1座標が段階軌道、第2座標は核上に残る物理観測である。

### 定義の説明

元の C3 の H-stage を、共有の状態核・同じ段の時間・S7 の情報の法則と、同時に保持するアダプターです。完全状態の第 1 座標が段階の軌道、第 2 座標は、核の上に残る物理観測です。フィールドは、情報のアダプター、元の段の仕様（元の段であること）、共通束の住所（元の層の住所）、開始時刻（元の段の開始時刻）、滞在時間（正）、核の軌道（等式）、物理座標が保たれる、認知座標の射影が段の軌道、評価が元の段の評価、観測エントロピーが増加する、終点が次の段の初期点、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C3CoreStageAdapter"></a>

## 定義 `c6C3CoreStageAdapter`

### 式

$$
\mathrm{C6C3CoreStageAdapter}(n)
$$

### Lean のコメント（日本語訳）

> 全てのフィールドに元H-stage列と実情報adapterを代入した具体証人。

### 定義の説明

すべてのフィールドに、元の H-stage の列と、実際の情報アダプターを代入した、具体的な証人です。

### 証明の概略

1. 各フィールドを、上の補題（核の軌道・物理座標・エントロピーの増加）と、C3 の段の補題から埋める。

----

<a id="Tomabechi.Consistency.C6.c6C3CoreStageAdapter_nonempty"></a>

## 補題 `c6C3CoreStageAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段のアダプターが存在します。

### 証明の概略

1. `c6C3CoreStageAdapter n` が証人。

----

<a id="Tomabechi.Consistency.C6.c6C3CoreStageAdapter_endpoint_completeState"></a>

## 補題 `c6C3CoreStageAdapter_endpoint_completeState`

### 式

$$
\text{段の終端}=\text{次の段の初期完全状態}
$$

### Lean のコメント（日本語訳）

> C3段の終端は、認知座標だけでなく物理座標を含む完全状態のまま次段初期点へ渡る。

### 補題の説明

C3 の段の終端は、認知座標だけでなく、物理座標を含む完全状態のまま、次の段の初期点へ渡ります。

### 証明の概略

1. 段の終点の認知座標が、次の段の初期点であること（C3 の補題）と、物理座標が保たれること。

----

<a id="Tomabechi.Consistency.C6.c6C3CoreStageAdapter_restart"></a>

## 補題 `c6C3CoreStageAdapter_restart`

### 式

$$
\text{隣り合うアダプターの端点}=\text{次段の初期値（物理座標を含む）}
$$

### Lean のコメント（日本語訳）

> 隣り合うadapterの端点と次段初期値は、物理座標を含めて同じ完全状態である。

### 補題の説明

隣り合うアダプターの端点と、次の段の初期値は、物理座標を含めて、同じ完全状態です。

### 証明の概略

1. 前の補題。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_C4_history_flow"></a>

## 補題 `centeredGainEntropyStep_projects_C4_history_flow`

### 式

$$
\text{C4 の全履歴・全初期値の勾配流}=\text{核の中心パラメータからの更新の射影}
$$

### Lean のコメント（日本語訳）

> C4の全履歴・全初期値の勾配流も、同じ核の中心パラメータから得る。

### 補題の説明

C4 の全履歴・全初期値の勾配流も、同じ核の中心パラメータから得られます。

### 証明の概略

1. 勾配流の式 \(c_h+(x-c_h)e^{-t}\) と、更新後の認知座標の式。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_all_C5_gains"></a>

## 補題 `centeredGainEntropyStep_projects_all_C5_gains`

### 式

$$
\text{C5 の全有界可測ゲインのベクトル軌道}=\text{零目標保存射影で回収}
$$

### Lean のコメント（日本語訳）

> C5の全有界可測ゲインのベクトル軌道を、零目標保存射影で回収する。半径だけでなく位相も一致し、C5の元時刻T,tを維持する。

### 補題の説明

C5 の全有界可測ゲインのベクトルの軌道を、零目標を保つ射影で回収します。半径だけでなく位相も一致し、C5 の元の時刻 \(T,t\) を維持します。

### 証明の概略

1. C5 のベクトル軌道の閉形式（半径の指数減衰と位相）と、核の更新の射影を比べる。

----

<a id="Tomabechi.Consistency.C6.centeredGainEntropyStep_projects_C5_data_trajectory"></a>

## 補題 `centeredGainEntropyStep_projects_C5_data_trajectory`

### 式

$$
\text{C5 の実際の費用データが定める軌道}=\text{核の更新の射影}
$$

### Lean のコメント（日本語訳）

> C5の実際の費用データが定めるtrajectoryへ、全方策・全初期値でつなぐ。方策の許容性や最適性はC5の既存定理から別に取り出す。

### 補題の説明

C5 の実際の費用データが定める軌道へ、全方策・全初期値でつなぎます。方策の許容性や最適性は、C5 の既存の定理から別に取り出します。

### 証明の概略

1. C5 のデータの軌道が、方策のゲインで定まるベクトル軌道であること。

----

<a id="Tomabechi.Consistency.C6.c5CoreTrajectory"></a>

## 定義 `c5CoreTrajectory`

### 式

$$
\text{C5 上位の各許容 feedback が選ぶ有界可測ゲインに対応する核の軌道}
$$

### Lean のコメント（日本語訳）

> C5上位の各許容feedbackが選ぶ有界可測ゲインに対応する共有核trajectory。

### 定義の説明

C5 の上位の各許容フィードバックが選ぶ、有界可測ゲインに対応する、共有核の軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c5CoreTrajectory_projects_data_trajectory"></a>

## 補題 `c5CoreTrajectory_projects_data_trajectory`

### 式

$$
\text{C5 の費用データが定める全 feedback の軌道}=\text{核の軌道の射影}
$$

### Lean のコメント（日本語訳）

> C5の費用データが定める全feedbackの軌道は、同じ核trajectoryへの射影。

### 補題の説明

C5 の費用データが定める、全フィードバックの軌道は、同じ核の軌道への射影です。

### 証明の概略

1. 前の補題。

----

<a id="Tomabechi.Consistency.C6.c5CoreTrajectory_runningCost"></a>

## 補題 `c5CoreTrajectory_runningCost`

### 式

$$
\text{C5 の実走行費}=6\,\Phi_c(\text{核の軌道})
$$

### Lean のコメント（日本語訳）

> C5の実走行費は、同じ実trajectoryを生成する共有核の二次評価の6倍。許容feedbackの選択も積分区間 `[T,∞)` も変更しない。

### 補題の説明

C5 の実際の走行費は、同じ実際の軌道を生成する、共有核の二次評価の 6 倍です。許容フィードバックの選択も、積分区間 \([T,\infty)\) も変更しません。

### 証明の概略

1. 走行費の式（6 倍）と、軌道の射影。

----

<a id="Tomabechi.Consistency.C6.c5CoreDiscountedCost"></a>

## 定義 `c5CoreDiscountedCost`

### 式

$$
\int_T^\infty e^{-(t-T)}\,6\,\Phi_c(\text{核の軌道})\,dt
$$

### Lean のコメント（日本語訳）

> C5費用の共有核側での割引積分表示。

### 定義の説明

C5 の費用の、共有核の側での、割引つき積分の表示です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c5CoreDiscountedCost_eq_dataCost"></a>

## 補題 `c5CoreDiscountedCost_eq_dataCost`

### 式

$$
\text{核側の割引積分}=\text{実際の C5 の割引走行費の積分}
$$

### Lean のコメント（日本語訳）

> 実際のC5割引走行費積分と共有核二次評価積分は等しい。これはrunning costの単なる点wise比ではなく、費用汎関数そのもののpullbackである。

### 補題の説明

実際の C5 の割引走行費の積分と、共有核の二次評価の積分は、等しいです。これは走行費の単なる各点の比ではなく、**費用の汎関数そのもの**の引き戻しです。

### 証明の概略

1. 被積分関数の一致（前の補題）から、積分も等しい。

----

<a id="Tomabechi.Consistency.C6.c5CoreDiscountedCost_optimal_attained"></a>

## 補題 `c5CoreDiscountedCost_optimal_attained`

### 式

$$
\text{最適方策は核側の割引費用の最適値を達成する}
$$

### Lean のコメント（日本語訳）

> C5の最適方策は、共有核で積分した同じ割引費用も最小化し、最適値を達成する。

### 補題の説明

C5 の最適方策は、共有核で積分した同じ割引費用も最小化し、最適値を達成します。

### 証明の概略

1. 最適値の達成（C5 の既存定理）と、前の補題。

----

<a id="Tomabechi.Consistency.C6.c5CoreDiscountedCost_optimal_minimal"></a>

## 補題 `c5CoreDiscountedCost_optimal_minimal`

### 式

$$
\text{全許容 feedback に対する最適性も核側の費用積分へ移る}
$$

### Lean のコメント（日本語訳）

> 全ての許容feedbackに対するC5最適性も、同じ共有核の費用積分へ移る。

### 補題の説明

すべての許容フィードバックに対する C5 の最適性も、同じ共有核の費用積分へ移ります。

### 証明の概略

1. C5 の最適性（全許容フィードバックに対して最小）と、前の補題。

----

<a id="Tomabechi.Consistency.C6.c6C1C3CenterSamplingAdapter_tendsto_atTop"></a>

## 補題 `c6C1C3CenterSamplingAdapter_tendsto_atTop`

### 式

$$
\mathrm{sampleTime}_n\to\infty
$$

### Lean のコメント（日本語訳）

> 到達時刻列の有限シフトも発散する。固定版MathlibのAPI名は`tendsto_add_atTop_nat` であり、実数castへ変えてから合成する必要はない。

### 補題の説明

C1 が C3 の中心列を通る時刻の列は、発散します（有限のシフトを加えても）。

### 証明の概略

1. 到達時刻列の発散（`c1TimeAtC3StageCenter_tendsto_atTop`）と、自然数のシフトの補題（`tendsto_add_atTop_nat`）の合成。

----

<a id="Tomabechi.Consistency.C6.c3A7StageInitial"></a>

## 定義 `c3A7StageInitial`

### 式

$$
(x_0^{(n)},\ 3\,t_n-(x_0^{(n)})^2)
$$

### Lean のコメント（日本語訳）

> C2のA7率3に合わせるC3段の完全初期状態。物理座標は時間を別に数える時計ではなく、全エントロピー値 `3·stageTime` と認知二乗から定める。

### 定義の説明

C2 の A7（率 3）に合わせる、C3 の段の完全な初期状態です。物理座標は、時間を別に数える時計ではなく、全エントロピーの値 \(3\cdot\mathrm{stageTime}\) と、認知座標の二乗から定めます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory"></a>

## 定義 `c3A7StageTrajectory`

### 式

$$
\text{元の C3 の認知軌道を保ちながら、全エントロピーを率 3 で増やす完全状態}
$$

### Lean のコメント（日本語訳）

> 元C3認知軌道を保ちながら、完全状態の全エントロピーをC2 A7と同じ率3で増やす。

### 定義の説明

元の C3 の認知軌道を保ちながら、完全状態の全エントロピーを、C2 の A7 と同じ率 3 で増やす軌道です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.entropyObservedElapsed_measurable"></a>

## 補題 `entropyObservedElapsed_measurable`

### 式

$$
\text{観測されるエントロピーは可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

観測されるエントロピーの関数は、可測です。

### 証明の概略

1. 定義を展開して、可測性の自動証明（`fun_prop`）。

----

<a id="Tomabechi.Consistency.C6.cognitiveCoordinate_measurable"></a>

## 補題 `cognitiveCoordinate_measurable`

### 式

$$
\text{認知座標は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知座標を取る関数は、可測です。

### 証明の概略

1. 第 1 射影は可測。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_entropyObserved"></a>

## 補題 `c3A7StageTrajectory_entropyObserved`

### 式

$$
\text{観測エントロピー}=3t
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の軌道の観測エントロピーは、\(3t\) です。

### 証明の概略

1. 更新のエントロピーの補題（`centeredGainEntropyStep_entropy`）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_satisfies_A7"></a>

## 補題 `c3A7StageTrajectory_satisfies_A7`

### 式

$$
\frac{d}{dt}\text{物理}=-\sum_n w_n\,\frac{d}{dt}\text{層}_n+3
$$

### Lean のコメント（日本語訳）

> C3元stageの物理座標と全正層の重み付き生成率は、原文A7の収支式を満たす。生産率3をstageの物理成分と層成分へ実際に分配している。

### 補題の説明

C3 の元の段の物理座標と、全正層の重みつき生成率は、原文 A7 の収支式を満たします。生産率 3 を、段の物理成分と層成分へ、実際に分配しています。

### 証明の概略

1. 観測エントロピーが \(3t\) であること、各層のエントロピーが \(1+q^2\) であること、重みの和の項別微分。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_cognitive"></a>

## 補題 `c3A7StageTrajectory_cognitive`

### 式

$$
\text{認知座標}=\text{元の C3 の認知軌道}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の軌道の認知座標は、元の C3 の認知軌道に一致します。

### 証明の概略

1. 更新後の認知座標の式。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_cognitive_formula"></a>

## 補題 `c3A7StageTrajectory_cognitive_formula`

### 式

$$
q(t)=c+(x_0-c)e^{-(t-t_n)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の軌道の認知座標の閉形式です。

### 証明の概略

1. 前の補題と、凍結軌道の式。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_cognitive_le_center"></a>

## 補題 `c3A7StageTrajectory_cognitive_le_center`

### 式

$$
t\ge t_n\Rightarrow q(t)\le c
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の開始時刻以降、認知座標は中心以下です。

### 証明の概略

1. \(x_0\le c\) と、\(0<e^{-(t-t_n)}\le1\)。

----

<a id="Tomabechi.Consistency.C6.c3StageTime_strictMono"></a>

## 補題 `c3StageTime_strictMono`

### 式

$$
\mathrm{stageTime}\ \text{は狭義単調増加}
$$

### Lean のコメント（日本語訳）

> 元C3のstage時刻列はduration正値により狭義増加する。

### 補題の説明

元の C3 の段の時刻列は、滞在時間が正であることにより、狭義単調に増加します。

### 証明の概略

1. 漸化式の一歩の増分が正（`strictMono_nat_of_lt_succ`）。

----

<a id="Tomabechi.Consistency.C6.c3StageTime_tendsto_atTop"></a>

## 補題 `c3StageTime_tendsto_atTop`

### 式

$$
\forall B,\ \exists n,\ B<\mathrm{stageTime}(n)
$$

### Lean のコメント（日本語訳）

> 元C3のstage時刻は非有界で、全有限時刻のstage番号選択を可能にする。

### 補題の説明

元の C3 の段の時刻は非有界で、全有限時刻の段の番号の選択を可能にします。

### 証明の概略

1. C3 の段の時刻の非有界性の補題。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex"></a>

## 定義 `c3StageActiveIndex`

### 式

$$
\mathrm{activeIndex}(t)=\min\{n\mid t<\mathrm{stageTime}(n+1)\}
$$

### Lean のコメント（日本語訳）

> 任意の実時刻を、C3の最初のまだ先にあるstage endpointで分類する。

### 定義の説明

任意の実時刻を、C3 の最初のまだ先にある段の端点で分類する写像です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex_endpoint_bound"></a>

## 補題 `c3StageActiveIndex_endpoint_bound`

### 式

$$
t<\mathrm{stageTime}(\mathrm{activeIndex}(t)+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻は、選ばれた段の次の段の開始時刻より前です。

### 証明の概略

1. 最小値の性質（`Nat.find_spec`）。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex_eq_zero_iff"></a>

## 補題 `c3StageActiveIndex_eq_zero_iff`

### 式

$$
\mathrm{activeIndex}(t)=0\iff t<\mathrm{stageTime}(1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選ばれた段が 0 であることは、時刻が段 1 の開始前であることと同値です。

### 証明の概略

1. 定義の最小値の性質。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex_eq_on_dwell"></a>

## 補題 `c3StageActiveIndex_eq_on_dwell`

### 式

$$
t\in[\mathrm{stageTime}(n),\mathrm{stageTime}(n+1))\Rightarrow\mathrm{activeIndex}(t)=n
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段 \(n\) の滞在区間の上では、選ばれた段は \(n\) です。

### 証明の概略

1. 区間の半開性と、最小値の性質。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex_dwell_iff"></a>

## 補題 `c3StageActiveIndex_dwell_iff`

### 式

$$
\mathrm{activeIndex}(t)=n\iff t\in[\mathrm{stageTime}(n),\mathrm{stageTime}(n+1))\ (n>0)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n>0\) のとき、選ばれた段が \(n\) であることは、時刻が段 \(n\) の滞在区間に入ることと同値です。

### 証明の概略

1. 前の補題と、最小値の性質（\(n\) が最小）。

----

<a id="Tomabechi.Consistency.C6.measurable_c3StageActiveIndex"></a>

## 補題 `measurable_c3StageActiveIndex`

### 式

$$
\mathrm{activeIndex}\ \text{は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

選ばれた段の番号を返す関数は、可測です。

### 証明の概略

1. 値が可算なので、各値の逆像が可測であることを示す（`measurable_to_countable'`）。

----

<a id="Tomabechi.Consistency.C6.c3StageTime_nonneg"></a>

## 補題 `c3StageTime_nonneg`

### 式

$$
0\le\mathrm{stageTime}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の開始時刻は非負です。

### 証明の概略

1. \(n\) に関する帰納法。

----

<a id="Tomabechi.Consistency.C6.c3StageActiveIndex_mem_dwell"></a>

## 補題 `c3StageActiveIndex_mem_dwell`

### 式

$$
t\ge0\Rightarrow t\in[\mathrm{stageTime}(\mathrm{activeIndex}\,t),\ \cdots)
$$

### Lean のコメント（日本語訳）

> 各非負時刻はちょうど選択されたstageのhalf-open dwellに入る。

### 補題の説明

各非負時刻は、ちょうど選ばれた段の半開の滞在区間に入ります。

### 証明の概略

1. 非負時刻の段 0 以降の分割（滞在区間の和集合が \([0,\infty)\)）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageC1Gain"></a>

## 定義 `c3A7StageC1Gain`

### 式

$$
u=\frac{c-q}{1-q}
$$

### Lean のコメント（日本語訳）

> C3の一段をC1の中心1・状態依存ゲインで表す候補入力。stage内では `u=(c-q)/(1-q)` とし、C3認知速度 `q'=c-q` をC1形式 `q'=u(1-q)` に変換する。段開始前の延長は許容性のため0とする。

### 定義の説明

C3 の一段を、C1 の中心 1・状態依存のゲインで表す、**候補の入力**です。段の内部では \(u=(c-q)/(1-q)\) とし、C3 の認知速度 \(q'=c-q\) を、C1 の形式 \(q'=u(1-q)\) に変換します。段の開始前の延長は、許容性のため 0 とします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageC1Gain_ode"></a>

## 補題 `c3A7StageC1Gain_ode`

### 式

$$
\dot q=u\,(1-q)
$$

### Lean のコメント（日本語訳）

> C3 stage内の認知軌道は、上で作った許容C1ゲイン信号のCarathéodory方程式を満たす。

### 補題の説明

C3 の段の内部の認知軌道は、上で作った許容な C1 のゲイン信号の Carathéodory 方程式を満たします。

### 証明の概略

1. 認知座標の微分 \(q'=c-q\) と、ゲインの定義 \(u(1-q)=c-q\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StageC1Gain_matches_C1_trajectory"></a>

## 補題 `c3A7StageC1Gain_matches_C1_trajectory`

### 式

$$
\text{C1 の積分軌道}=\text{C3 の認知軌道（各有限段区間上）}
$$

### Lean のコメント（日本語訳）

> 上の対応入力で、C1の実際の積分軌道は各有限stage区間上のC3認知軌道を再現する。この入力は許容族の一員であり、C1最大ゲインの選択軌道と同一だとは主張しない。

### 補題の説明

上の対応する入力で、C1 の実際の積分軌道は、各有限の段区間の上で、C3 の認知軌道を再現します。この入力は許容族の一員であり、C1 の最大ゲインの選択軌道と同一だとは主張しません。

### 証明の概略

1. Carathéodory の解の一意性（前の補題の方程式と、同じ初期値）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_initial"></a>

## 補題 `c3A7StageTrajectory_initial`

### 式

$$
\text{初期時刻の完全状態}=\mathrm{c3A7StageInitial}(n)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期時刻の段の軌道は、初期の完全状態です。

### 証明の概略

1. 更新が恒等（累積ゲイン・生成 0）。

----

<a id="Tomabechi.Consistency.C6.c3A7StageTrajectory_endpoint"></a>

## 補題 `c3A7StageTrajectory_endpoint`

### 式

$$
\text{段の終点}=\mathrm{c3A7StageInitial}(n+1)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の終点は、次の段の初期の完全状態に等しいです。

### 証明の概略

1. 終点の認知座標が次の段の初期点であること（C3 の段の接続）と、全エントロピーが \(3(t_n+d_n)=3t_{n+1}\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory"></a>

## 定義 `c3A7StitchedTrajectory`

### 式

$$
z(t)=\mathrm{stage}_{\mathrm{activeIndex}(t)}(t)
$$

### Lean のコメント（日本語訳）

> 元C3のA7段をactive-stage indexで接続した全時刻完全状態path。

### 定義の説明

元の C3 の A7 の段を、選ばれた段の番号で接続した、全時刻の完全状態の経路です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_eq_active_stage"></a>

## 補題 `c3A7StitchedTrajectory_eq_active_stage`

### 式

$$
z(t)=\mathrm{stage}_{\mathrm{activeIndex}(t)}(t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

接続した経路は、選ばれた段の軌道です。

### 証明の概略

1. 定義から。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_eq_stage"></a>

## 補題 `c3A7StitchedTrajectory_eq_stage`

### 式

$$
t\in\text{段 }n\text{ の滞在区間}\Rightarrow z(t)=\mathrm{stage}_n(t)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段 \(n\) の滞在区間の上では、接続した経路は、段 \(n\) の軌道です。

### 証明の概略

1. 選ばれた段の番号が \(n\)（滞在区間での段の番号の補題）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_at_stageTime"></a>

## 補題 `c3A7StitchedTrajectory_at_stageTime`

### 式

$$
z(t_n)=\mathrm{c3A7StageInitial}(n)
$$

### Lean のコメント（日本語訳）

> 切替時刻では新しい段を選び、全状態がその段の初期値に一致する。

### 補題の説明

切り替えの時刻では、新しい段を選び、全状態がその段の初期値に一致します。

### 証明の概略

1. 半開区間の左端が含まれるので、選ばれる段は \(n\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_at_stageEndpoint"></a>

## 補題 `c3A7StitchedTrajectory_at_stageEndpoint`

### 式

$$
z(t_n+d_n)=\mathrm{c3A7StageInitial}(n+1)
$$

### Lean のコメント（日本語訳）

> stitched path は各stage endpointで次段の完全初期状態へ正確につながる。

### 補題の説明

接続した経路は、各段の端点で、次の段の完全な初期状態へ、正確につながります。

### 証明の概略

1. 段の端点は次の段の開始時刻（`t_n+d_n=t_{n+1}`）。前の補題。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_entropyObserved"></a>

## 補題 `c3A7StitchedTrajectory_entropyObserved`

### 式

$$
\text{観測されるエントロピー}=3t
$$

### Lean のコメント（日本語訳）

> stitched完全状態の物理観測と二乗認知観測は、全実時刻で総和 `3t` を保つ。

### 補題の説明

接続した完全状態の、物理観測と認知座標の二乗は、全実時刻で、総和 \(3t\) を保ちます。

### 証明の概略

1. 各段の観測エントロピーが \(3t\)（段の補題）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_matches_C5_upper_optimalFlow"></a>

## 補題 `c3A7StitchedTrajectory_matches_C5_upper_optimalFlow`

### 式

$$
\text{C3/A7 の大域の完全経路を 27 の状態へ写す}=\text{C5 上位の最大方策の流れ（時間 }3t\text{）}
$$

### Lean のコメント（日本語訳）

> C3/A7の大域完全pathを27の状態へ写すと、C4 true履歴に結び付いたC5上層の最大方策flowを時間 `3t` で正確に再現する。比較は同じ総エントロピー観測から従う。

### 補題の説明

C3/A7 の大域の完全経路を 27 の状態へ写すと、C4 の true 履歴に結びついた C5 の上層の最大方策の流れを、時間 \(3t\) で正確に再現します。比較は、同じ総エントロピーの観測から従います。

### 証明の概略

1. 27 の状態への射影が総エントロピーで決まること。C5 の最大方策の流れが、時間 \(3t\) の指数で与えられること。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_C5_flow_nonconstant"></a>

## 補題 `c3A7StitchedTrajectory_C5_flow_nonconstant`

### 式

$$
\text{共通の経路から射影した C5 上層の流れは非定常}
$$

### Lean のコメント（日本語訳）

> 共通pathから射影されたC5上層flowは、非負時間で実際に非定常である。

### 補題の説明

共通の経路から射影された C5 の上層の流れは、非負時間で、実際に**非定常**です。

### 証明の概略

1. 流れが時間に依存する（半径が指数で減衰する）ことを、二つの時刻で比べて示す。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_generalizedEntropy"></a>

## 補題 `c3A7StitchedTrajectory_generalizedEntropy`

### 式

$$
\text{一般化エントロピー}=1+3t
$$

### Lean のコメント（日本語訳）

> C2の重み付き無限層和で定義する一般化エントロピーも、全時間で `1+3t` となる。

### 補題の説明

C2 の重みつきの無限層の和で定義する、一般化エントロピーも、全時間で \(1+3t\) となります。

### 証明の概略

1. 一般化エントロピーが観測エントロピーに \(1\) を足したもの（`generalizedEntropy_eq_observedElapsed`）で、観測エントロピーが \(3t\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_generalizedEntropy_strictMono"></a>

## 補題 `c3A7StitchedTrajectory_generalizedEntropy_strictMono`

### 式

$$
t\mapsto\text{一般化エントロピー}\ \text{は狭義単調増加}
$$

### Lean のコメント（日本語訳）

> 完全状態から読むC2一般化エントロピーは、時刻とともに厳密に増加する。

### 補題の説明

完全状態から読む、C2 の一般化エントロピーは、時刻とともに**厳密に増加**します。

### 証明の概略

1. \(1+3t\) は狭義単調。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_injective"></a>

## 補題 `c3A7StitchedTrajectory_injective`

### 式

$$
z(s)=z(t)\Rightarrow s=t
$$

### Lean のコメント（日本語訳）

> stitched完全状態に独立時計を追加しなくても、二時刻の状態再訪は起こらない。

### 補題の説明

接続した完全状態に独立な時計を追加しなくても、二つの時刻の状態の再訪は起こりません。

### 証明の概略

1. 一般化エントロピーが狭義単調なので、状態が等しければ時刻が等しい。

----

<a id="Tomabechi.Consistency.C6.measurable_c3A7StitchedTrajectory"></a>

## 補題 `measurable_c3A7StitchedTrajectory`

### 式

$$
z(\cdot)\ \text{は可測}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

接続した経路は、時刻の関数として可測です。

### 証明の概略

1. 選ばれた段の番号が可測で、各段の軌道が連続なので、可測な場合分けで貼り合わせる。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain"></a>

## 定義 `c3A7StitchedC1Gain`

### 式

$$
u(t)=\text{選ばれた段の中心に対する状態依存ゲイン（}t<0\text{ では }0\text{）}
$$

### Lean のコメント（日本語訳）

> 全C3 stage列を一つのC1許容ゲインへ貼り合わせる。非負時間ではactive stageの中心に対する状態依存ゲインを使い、負時間では0とする。

### 定義の説明

全 C3 の段の列を、一つの C1 の許容ゲインへ**貼り合わせます**。非負時間では、選ばれた段の中心に対する状態依存のゲインを使い、負時間では 0 とします。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain_eq_stage"></a>

## 補題 `c3A7StitchedC1Gain_eq_stage`

### 式

$$
t\in\text{段 }n\text{ の滞在区間}\Rightarrow u(t)=\text{段 }n\text{ のゲイン}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段 \(n\) の滞在区間の上で、貼り合わせたゲインは、段 \(n\) のゲインです。

### 証明の概略

1. 選ばれた段の番号が \(n\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain_le_one"></a>

## 補題 `c3A7StitchedC1Gain_le_one`

### 式

$$
t\ge0\Rightarrow u(t)\le1
$$

### Lean のコメント（日本語訳）

> 各stitched stageで選ばれる実効ゲインは実は高々1である。これはC1の許容上限3より強く、微分和の一様評価に使う。

### 補題の説明

各接続した段で選ばれる実効のゲインは、実は高々 1 です。これは C1 の許容の上限 3 より強く、微分の和の一様な評価に使います。

### 証明の概略

1. ゲインが \((c-q)/(1-q)\) で、\(q\le c\le1\) から。

----

<a id="Tomabechi.Consistency.C6.c1ControlledState_eq_of_gain_eq_on_interval"></a>

## 補題 `c1ControlledState_eq_of_gain_eq_on_interval`

### 式

$$
u=v\text{ on }[a,b)\Rightarrow\text{区間内の積分状態が等しい}
$$

### Lean のコメント（日本語訳）

> 区間上で一致する二つの許容ゲインは、その区間内の積分状態を同じにする。

### 補題の説明

区間の上で一致する二つの許容ゲインは、その区間内の積分状態を、同じにします。

### 証明の概略

1. 積分の区間への制限。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain_matches_global_C1_trajectory"></a>

## 補題 `c3A7StitchedC1Gain_matches_global_C1_trajectory`

### 式

$$
\text{大域の許容入力の積分軌道}=\text{接続した C3/A7 の認知経路}\ (t\ge0)
$$

### Lean のコメント（日本語訳）

> 一つの大域許容入力の積分軌道は、全ての非負時刻でstitched C3/A7認知pathに一致する。証明は各dwellの一意性とswitchごとのrestartを自然数帰納法でつなぐ。

### 補題の説明

一つの**大域の許容入力**の積分軌道は、全ての非負時刻で、接続した C3/A7 の認知経路に一致します。証明は、各滞在区間での一意性と、切り替えごとの再始動を、自然数の帰納法でつなぎます。

### 証明の概略

1. 段 \(n\) までの一致を帰納で示す。各滞在区間で、貼り合わせたゲインと段のゲインが一致する（区間上のゲインの一致の補題）ので、段の一致の補題（`c3A7StageC1Gain_matches_C1_trajectory`）から。切り替えの端点で、状態が一致する（段の端点の補題）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedCognitive_absolutelyContinuousOnInterval"></a>

## 補題 `c3A7StitchedCognitive_absolutelyContinuousOnInterval`

### 式

$$
q(\cdot)\ \text{は非負有限区間で絶対連続}
$$

### Lean のコメント（日本語訳）

> C3/A7で段を貼り合わせた認知座標は、非負有限区間上で絶対連続である。箱条件に依存しないC1の積分軌道ACを、大域path一致を通して移送する。

### 補題の説明

C3/A7 で段を貼り合わせた認知座標は、非負の有限区間の上で**絶対連続**です。箱の条件に依存しない C1 の積分軌道の絶対連続性を、大域の経路の一致を通して移送します。

### 証明の概略

1. C1 の積分軌道は絶対連続。大域の経路の一致（前の補題）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedTrajectory_cognitive_mem_unitInterval"></a>

## 補題 `c3A7StitchedTrajectory_cognitive_mem_unitInterval`

### 式

$$
t\ge0\Rightarrow q(t)\in[0,1]
$$

### Lean のコメント（日本語訳）

> 大域stitched認知座標は全ての非負時刻で `[0,1]` に入る。

### 補題の説明

大域の接続した認知座標は、全ての非負時刻で \([0,1]\) に入ります。

### 証明の概略

1. 各段で、\(0\le x_0\le q\le c<1\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedCognitiveSq_absolutelyContinuousOnInterval"></a>

## 補題 `c3A7StitchedCognitiveSq_absolutelyContinuousOnInterval`

### 式

$$
q^2\ \text{も絶対連続}
$$

### Lean のコメント（日本語訳）

> 認知座標の二乗も同じ有限区間上で絶対連続である。

### 補題の説明

認知座標の二乗も、同じ有限区間の上で絶対連続です。

### 証明の概略

1. 絶対連続関数の積。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedLayerEntropy_absolutelyContinuousOnInterval"></a>

## 補題 `c3A7StitchedLayerEntropy_absolutelyContinuousOnInterval`

### 式

$$
1+q^2\ \text{は絶対連続（全正層）}
$$

### Lean のコメント（日本語訳）

> 全ての正層エントロピー `1+q²` は同じstitched path上で絶対連続である。

### 補題の説明

全ての正層のエントロピー \(1+q^2\) は、同じ接続した経路の上で絶対連続です。

### 証明の概略

1. 定数と絶対連続関数の和。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedPhysicalEntropy_absolutelyContinuousOnInterval"></a>

## 補題 `c3A7StitchedPhysicalEntropy_absolutelyContinuousOnInterval`

### 式

$$
3t-q^2\ \text{は絶対連続}
$$

### Lean のコメント（日本語訳）

> 物理エントロピー `3t-q²` も同じstitched path上で絶対連続である。

### 補題の説明

物理エントロピー \(3t-q^2\) も、同じ接続した経路の上で絶対連続です。

### 証明の概略

1. \(3t\) と \(q^2\) が絶対連続。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedLayerEntropy_ac_between"></a>

## 補題 `c3A7StitchedLayerEntropy_ac_between`

### 式

$$
\text{任意の生存区間 }[a,b]\text{ へ、正層の絶対連続性を制限する}
$$

### Lean のコメント（日本語訳）

> 15→23入口が要求する任意の生存区間[a,b]へ、正層ACを制限する。

### 補題の説明

15→23 の入口が要求する任意の生存区間 \([a,b]\) へ、正層の絶対連続性を制限します。

### 証明の概略

1. 有限区間 \([0,b]\) 上の絶対連続性の制限。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedPhysicalEntropy_ac_between"></a>

## 補題 `c3A7StitchedPhysicalEntropy_ac_between`

### 式

$$
\text{任意の生存区間へ、物理層の絶対連続性を制限する}
$$

### Lean のコメント（日本語訳）

> 15→23入口が要求する任意の生存区間[a,b]へ、物理層ACを制限する。

### 補題の説明

15→23 の入口が要求する任意の生存区間 \([a,b]\) へ、物理層の絶対連続性を制限します。

### 証明の概略

1. 同上。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_endpoint_layer_summable"></a>

## 補題 `c3A7Stitched_endpoint_layer_summable`

### 式

$$
\sum_n w_n\,\mathrm{layer}_n(z(t))<\infty
$$

### Lean のコメント（日本語訳）

> 同じpathの各有限時刻で、15→23入口の端点層和は可算和可能である。

### 補題の説明

同じ経路の各有限時刻で、15→23 の入口の端点の層の和は、可算和が可能です。

### 証明の概略

1. 各層のエントロピーは \(1+q^2\le2\) で有界。重みの和は有限。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_production_integral_pos"></a>

## 補題 `c3A7Stitched_production_integral_pos`

### 式

$$
0<\int_a^b3\,dt
$$

### Lean のコメント（日本語訳）

> 生成率3は、非負生存区間のどの長さにも厳密に正の生成積分を与える。

### 補題の説明

生成率 3 は、非負の生存区間の、どの長さに対しても、厳密に正の生成の積分を与えます。

### 証明の概略

1. 定数の積分 \(3(b-a)>0\)。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_production_nonnegative_ae"></a>

## 補題 `c3A7Stitched_production_nonnegative_ae`

### 式

$$
0\le3\ \ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> 生成率を切替時刻を含む区間全体で非負とする。

### 補題の説明

生成率を、切り替えの時刻を含む区間の全体で非負とします。

### 証明の概略

1. 定数 3 は非負。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_A6_endpoint_summable"></a>

## 補題 `c3A7Stitched_A6_endpoint_summable`

### 式

$$
\text{A6′ の端点条件が、両端で成り立つ}
$$

### Lean のコメント（日本語訳）

> 15→23のA6′端点条件を、この同じstitched pathの両端で供給する。

### 補題の説明

15→23 の A6′ の端点の条件を、この同じ接続した経路の両端で供給します。

### 証明の概略

1. 端点の層の和が可算和可能（端点の層の和の補題）。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedCognitive_ae_ode"></a>

## 補題 `c3A7StitchedCognitive_ae_ode`

### 式

$$
\dot q=u\,(1-q)\ \ (\text{a.e. on }[a,b])
$$

### Lean のコメント（日本語訳）

> 各正の非負時刻区間でstitched認知座標はC1入力方程式をa.e.満たす。有限切替点は測度零として処理し、区間内部では大域path一致から微分を移す。

### 補題の説明

各正の非負時刻区間で、接続した認知座標は、C1 の入力方程式を、ほとんど至る所で満たします。有限の切り替えの点は測度零として処理し、区間の内部では、大域の経路の一致から微分を移します。

### 証明の概略

1. 切り替えの点は可算（測度零）。区間の内部では、貼り合わせたゲインが、段のゲインに一致し、段の方程式（`c3A7StageC1Gain_ode`）が成り立つ。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedLayerEntropy_deriv_eq_sq"></a>

## 補題 `c3A7StitchedLayerEntropy_deriv_eq_sq`

### 式

$$
\frac{d}{dt}\mathrm{layer}_n=\frac{d}{dt}q^2
$$

### Lean のコメント（日本語訳）

> 同じ認知微分を持つとき、全正層のエントロピー導関数は `q²` の導関数に一致する。

### 補題の説明

同じ認知座標の微分を持つとき、全ての正層のエントロピーの導関数は、\(q^2\) の導関数に一致します。

### 証明の概略

1. 各層のエントロピー \(1+q^2\) を微分する。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedCognitiveSq_deriv_bound_ae"></a>

## 補題 `c3A7StitchedCognitiveSq_deriv_bound_ae`

### 式

$$
\bigl|(q^2)'\bigr|\le2\ \ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> A.e.ではstitched正層の共通導関数は絶対値2以下。状態と実効ゲインがともに `[0,1]` にあることを使う。

### 補題の説明

ほとんど至る所で、接続した正層の共通の導関数は、絶対値 2 以下です。状態と実効ゲインが、ともに \([0,1]\) にあることを使います。

### 証明の概略

1. \((q^2)'=2q\dot q=2q\,u(1-q)\)、\(0\le q\le1\)、\(0\le u\le1\)。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedFiniteLayerDerivative"></a>

## 定義 `c3A7StitchedFiniteLayerDerivative`

### 式

$$
\sum_{n\in s}w_n\cdot\mathrm{layer}_n'(t)
$$

### Lean のコメント（日本語訳）

> 有限正層部分集合の実導関数和を固定した時刻関数として表す。

### 定義の説明

有限の正層の部分集合の、実際の導関数の和を、固定した時刻の関数として表します。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_A6_finite_UI"></a>

## 補題 `c3A7Stitched_A6_finite_UI`

### 式

$$
\{\text{有限正層部分集合の導関数和}\}\ \text{は一様可積分}
$$

### Lean のコメント（日本語訳）

> 任意の有限正層部分集合に対する導関数和は一様可積分である。各層の導関数を `q²` の共通導関数へ畳み、幾何重みの部分和≤1を使う。

### 補題の説明

任意の有限の正層の部分集合に対する、導関数の和は、**一様可積分**です。各層の導関数を \(q^2\) の共通の導関数へ畳み、幾何的な重みの部分和 \(\le1\) を使います。

### 証明の概略

1. 各層の導関数が共通の \((q^2)'\)（導関数が \(q^2\) の導関数に等しい補題）で、絶対値 2 以下（導関数の上界の補題）。重みの有限和は 1 以下。したがって一様有界で、一様可積分。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_A6_prefix_tendsto_at"></a>

## 補題 `c3A7Stitched_A6_prefix_tendsto_at`

### 式

$$
\sum_{n\le N}w_n\,\mathrm{layer}_n'(t)\to\sum_nw_n\,\mathrm{layer}_n'(t)
$$

### Lean のコメント（日本語訳）

> 微分可能な一点では、stitched層の導関数prefixは総層導関数へ収束する。

### 補題の説明

微分可能な一点では、接続した層の導関数の先頭部分の和は、総層の導関数へ収束します。

### 証明の概略

1. 各層の導関数が共通の値 \(v'\)（\(q^2\) の導関数）。重みの和への収束。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_A7_at"></a>

## 補題 `c3A7Stitched_A7_at`

### 式

$$
\text{physical}'=3-\sum_nw_n\,\mathrm{layer}_n'
$$

### Lean のコメント（日本語訳）

> A7収支は、微分可能な一点では `physical'=3-Σwₙ(layerₙ')` となる。

### 補題の説明

A7 の収支は、微分可能な一点では、\(\text{physical}'=3-\sum_nw_n(\text{layer}_n)'\) となります。

### 証明の概略

1. 物理エントロピー \(3t-q^2\) の微分 \(3-(q^2)'\)、層の導関数の和 \(=(q^2)'\)（重みの和は 1）。

----

<a id="Tomabechi.Consistency.C6.c3A7Stitched_theorem15_23_nonrecurrence"></a>

## 定理 `c3A7Stitched_theorem15_23_nonrecurrence`

### 式

$$
\forall t_1<t_2,\ z(t_2)\ne z(t_1)
$$

### Lean のコメント（日本語訳）

> 同じstitched pathに15(I)→23-A入口を適用し、非再訪を得る。

### 補題の説明

同じ接続した経路に、定理 15(I)→23-A の入口を適用し、**非再訪**を得ます。

### 証明の概略

1. 15→23 の入口の仮定（絶対連続性・端点の可算和・生成の正値・A6′・A7）を、上の補題で供給して適用する。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain_matches_twoAgent_flow"></a>

## 補題 `c3A7StitchedC1Gain_matches_twoAgent_flow`

### 式

$$
\text{C1 二主体の実状態の流れ}=\text{C3/A7 の認知座標から復元した状態}
$$

### Lean のコメント（日本語訳）

> C1二主体の実状態flowも、C3/A7の認知座標から復元した状態と一致する。初期状態 `![1,-1]` はC1の費用最適性用box外なので、この等式を最適性主張には使わない。

### 補題の説明

C1 の二主体の実際の状態の流れも、C3/A7 の認知座標から復元した状態と一致します。初期状態 \((1,-1)\) は、C1 の費用最適性のための箱の外なので、この等式を最適性の主張には使いません。

### 証明の概略

1. 二主体の状態が平均と半差で決まること。半差が認知座標に対応すること。

----

<a id="Tomabechi.Consistency.C6.c3A7StitchedC1Gain_twoAgent_initial_not_in_box"></a>

## 補題 `c3A7StitchedC1Gain_twoAgent_initial_not_in_box`

### 式

$$
(1,-1)\notin\mathrm{box}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

初期状態 \((1,-1)\) は箱の外です。

### 証明の概略

1. 座標の絶対値が \(1>1/4\)。

----

<a id="Tomabechi.Consistency.C6.c6C1C3CenterSample_eq_A7StageCenter"></a>

## 補題 `c6C1C3CenterSample_eq_A7StageCenter`

### 式

$$
\text{C1/C2 の実 flow のサンプル認知値}=\text{A7 の段の凍結中心}
$$

### Lean のコメント（日本語訳）

> C1/C2実flowのサンプル認知値は、対応するA7 stageの凍結中心と一致する。これはstage中心の一致であり、段有限時刻で軌道値が中心へ到達することや完全状態の一致を意味しない。

### 補題の説明

C1/C2 の実際の流れのサンプルの認知値は、対応する A7 の段の凍結中心と、一致します。これは段の中心の一致であり、段の有限時刻で軌道の値が中心へ到達することや、完全状態の一致を意味しません。

### 証明の概略

1. サンプルの認知値の定義と、段の中心の表象。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4CoreStageJointLaw"></a>

## 定義 `c6C1C3C4CoreStageJointLaw`

### 式

$$
\text{先の C1/C2/C4/C5/C3 結合法則に、C3 の段の完全状態の始点・終点を付加した法則}
$$

### Lean のコメント（日本語訳）

> C3元H-stageに対応し、A7率3を満たす完全状態の始点・終点も、先のC1/C2/C4/C5/C3結合lawへ付加する。拡張後も元の結合lawを周辺として回収できる。

### 定義の説明

C3 の元の H-stage に対応し、A7 の率 3 を満たす完全状態の、始点・終点も、先の C1/C2/C4/C5/C3 の結合法則へ付加します。拡張後も、元の結合法則を周辺として回収できます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4CoreStageJointLaw_isProbability"></a>

## 補題 `c6C1C3C4CoreStageJointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この結合法則は、確率測度です。

### 証明の概略

1. 元の結合法則が確率測度で、像の測度も確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4CoreStageJointLaw_observation_marginal"></a>

## 補題 `c6C1C3C4CoreStageJointLaw_observation_marginal`

### 式

$$
\text{観測の周辺}=\text{元の結合法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 1 周辺（観測）は、元の結合法則に一致します。

### 証明の概略

1. 像の合成。付加した座標は観測の関数。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4CoreStageJointLaw_endpoint_ae"></a>

## 補題 `c6C1C3C4CoreStageJointLaw_endpoint_ae`

### 式

$$
\text{結合法則の上でも、段の終点は次の段の初期状態を物理収支とともに保持}
$$

### Lean のコメント（日本語訳）

> 結合law上でもA7対応C3段の終点は、元H-stage列の次段初期状態を物理収支とともに保持する。

### 補題の説明

結合法則の上でも、A7 に対応する C3 の段の終点は、元の H-stage の列の次の段の初期状態を、物理収支とともに保持します。

### 証明の概略

1. 段の終点の補題（`c3A7StageTrajectory_endpoint`）を、ほとんど至る所で適用する。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4CoreStageJointLaw_restart_ae"></a>

## 補題 `c6C1C3C4CoreStageJointLaw_restart_ae`

### 式

$$
\text{第 }n\text{ 段の終点}=\text{次の段の A7 軌道の初期状態}
$$

### Lean のコメント（日本語訳）

> 結合lawに付加した第n段の終点は、次段A7対応trajectoryの初期状態でもある。元H-stage切替とlaw上の完全状態座標のrestart一致を結ぶ。

### 補題の説明

結合法則に付加した第 \(n\) 段の終点は、次の段の A7 に対応する軌道の初期状態でもあります。元の H-stage の切り替えと、法則の上の完全状態の座標の再始動の一致を、結びます。

### 証明の概略

1. 前の補題と、次の段の初期状態の補題。

----

<a id="Tomabechi.Consistency.C6.C6C1C3C4A7PathObservation"></a>

## 定義 `C6C1C3C4A7PathObservation`

### 式

$$
\text{C3/A7 の完全な段の経路を含めた共通結合法則の観測型}
$$

### Lean のコメント（日本語訳）

> C3/A7完全stage pathを含めた共通結合lawの観測型。

### 定義の説明

C3/A7 の完全な段の経路を含めた、共通の結合法則の観測型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6C1C3C4A7SamplePathObservation"></a>

## 定義 `C6C1C3C4A7SamplePathObservation`

### 式

$$
\text{観測型}\times\mathrm{CompleteState}
$$

### Lean のコメント（日本語訳）

> C1中心サンプルも含めた拡張観測型。

### 定義の説明

C1 の中心サンプルも含めた、拡張した観測型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.C6C1C3C4A7GlobalPathObservation"></a>

## 定義 `C6C1C3C4A7GlobalPathObservation`

### 式

$$
\text{観測型}\times(\mathbb R\to\mathrm{CompleteState})
$$

### Lean のコメント（日本語訳）

> C1中心サンプルに加え、全stageを通るstitched C3/A7軌道も保持する観測型。

### 定義の説明

C1 の中心サンプルに加え、全段を通る、接続した C3/A7 の軌道も保持する観測型です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw"></a>

## 定義 `c6C1C3C4A7PathJointLaw`

### 式

$$
\text{C3/A7 の完全な段の経路を含む共通結合法則}
$$

### Lean のコメント（日本語訳）

> C3/A7完全stage pathを含めた共通結合law。

### 定義の説明

C3/A7 の完全な段の経路を含めた、共通の結合法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_isProbability"></a>

## 補題 `c6C1C3C4A7PathJointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この結合法則は、確率測度です。

### 証明の概略

1. 元の結合法則が確率測度で、像の測度も確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_observation_marginal"></a>

## 補題 `c6C1C3C4A7PathJointLaw_observation_marginal`

### 式

$$
\text{観測の周辺}=\text{元の結合法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

観測の周辺は、元の結合法則に一致します。

### 証明の概略

1. 像の合成。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7SamplePathJointLaw"></a>

## 定義 `c6C1C3C4A7SamplePathJointLaw`

### 式

$$
\text{C1 の中心サンプルを、同じ確率空間へ載せた法則}
$$

### Lean のコメント（日本語訳）

> C1が同じC3中心列を実際に通る状態も、A7対応stage pathと同一確率空間へ載せる。追加座標はC1側の中心サンプルであり、C3 stage pathの有限時刻状態とは同一視しない。

### 定義の説明

C1 が同じ C3 の中心列を、実際に通る状態も、A7 に対応する段の経路と同一の確率空間へ載せます。追加の座標は C1 の側の中心サンプルであり、C3 の段の経路の有限時刻の状態とは、同一視しません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7SamplePathJointLaw_isProbability"></a>

## 補題 `c6C1C3C4A7SamplePathJointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この結合法則は、確率測度です。

### 証明の概略

1. 経路の法則が確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7SamplePathJointLaw_path_marginal"></a>

## 補題 `c6C1C3C4A7SamplePathJointLaw_path_marginal`

### 式

$$
\text{第 1 周辺}=\text{経路の結合法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 1 周辺（経路）は、経路の結合法則に一致します。

### 証明の概略

1. 像の合成。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7SamplePathJointLaw_c1_sample_marginal"></a>

## 補題 `c6C1C3C4A7SamplePathJointLaw_c1_sample_marginal`

### 式

$$
\text{第 2 周辺}=\text{C1 の中心サンプルの法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 2 周辺は、C1 の中心サンプルの法則（点の質量）に一致します。

### 証明の概略

1. サンプルは決定論的な値で、その点の質量。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7SamplePathJointLaw_c1_center_marginal"></a>

## 補題 `c6C1C3C4A7SamplePathJointLaw_c1_center_marginal`

### 式

$$
\text{サンプルの認知座標}=\text{段の中心}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

サンプルの認知座標の周辺は、段の中心の点の質量に一致します。

### 証明の概略

1. サンプルの認知値が段の中心（`c6C1C3CenterSample_eq_A7StageCenter`）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw"></a>

## 定義 `c6C1C3C4A7GlobalPathJointLaw`

### 式

$$
\text{C1 の中心サンプルと全段の接続軌道を同じ確率空間に載せた法則}
$$

### Lean のコメント（日本語訳）

> C1中心サンプルと全stage stitched trajectoryを同じ確率空間に載せる。

### 定義の説明

C1 の中心サンプルと、全段の接続した軌道を、同じ確率空間へ載せます。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C4ObservationFromGlobalPath"></a>

## 定義 `c6C1C4ObservationFromGlobalPath`

### 式

$$
z\mapsto z_{1,1,1,1,1}
$$

### Lean のコメント（日本語訳）

> 大域A7 path lawから、元のC1/C2/C4/C5介入観測座標を取り出す射影。

### 定義の説明

大域の A7 の経路の法則から、元の C1/C2/C4/C5 の介入観測の座標を取り出す射影です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw_C1C4_marginal"></a>

## 補題 `c6C1C3C4A7GlobalPathJointLaw_C1C4_marginal`

### 式

$$
\text{全経路の法則を元の介入観測へ射影}=\text{既存の C1/C2/C4/C5 の法則}
$$

### Lean のコメント（日本語訳）

> 全path lawを元の介入観測へ射影すると、既存のC1/C2/C4/C5 lawへ戻る。stage端点・サンプル・全pathの追加はSCM観測周辺を変えない。

### 補題の説明

全経路の法則を、元の介入観測へ射影すると、既存の C1/C2/C4/C5 の法則へ戻ります。段の端点・サンプル・全経路の追加は、SCM の観測の周辺を変えません。

### 証明の概略

1. 像の合成を、座標ごとに計算する。付加した座標は、観測座標に影響しない。

----

<a id="Tomabechi.Consistency.C6.c6C1C4ActualSCMObservationLaw"></a>

## 定義 `c6C1C4ActualSCMObservationLaw`

### 式

$$
\text{元の 25-C3 SCM の外生法則から直接押し出した、C1/C2・SCM・C5 実費用の観測法則}
$$

### Lean のコメント（日本語訳）

> 元の25-C3 SCMの外生法則から直接押し出す、C1/C2・SCM・C5実費用の観測law。

### 定義の説明

元の 25-C3 の SCM の外生法則から、直接押し出した、C1/C2・SCM・C5 の実費用の観測の法則です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw_eq_actualSCMLaw"></a>

## 補題 `c6C1C3C4A7GlobalPathJointLaw_eq_actualSCMLaw`

### 式

$$
\text{A7 全経路法則の C1/C2・SCM・C5 費用観測}=\text{同じ無作為化 25-C3 SCM の外生法則から直接得る結合法則}
$$

### Lean のコメント（日本語訳）

> A7全path lawのC1/C2・SCM・C5実費用観測は、同じ無作為化25-C3 SCMの外生法則から直接得るjoint lawと一致する。

### 補題の説明

A7 の全経路の法則の、C1/C2・SCM・C5 の実費用の観測は、同じ無作為化した 25-C3 の SCM の外生法則から、直接得る結合法則と一致します。

### 証明の概略

1. 前の補題（元の観測への射影）と、元の結合法則が SCM の外生法則の押し出しであること。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw_isProbability"></a>

## 補題 `c6C1C3C4A7GlobalPathJointLaw_isProbability`

### 式

$$
\text{確率測度}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

この結合法則は、確率測度です。

### 証明の概略

1. サンプル・経路の法則が確率測度。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw_sample_marginal"></a>

## 補題 `c6C1C3C4A7GlobalPathJointLaw_sample_marginal`

### 式

$$
\text{第 1 周辺}=\text{サンプル付き経路の結合法則}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

第 1 周辺は、サンプル付きの経路の結合法則に一致します。

### 証明の概略

1. 像の合成。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7GlobalPathJointLaw_trajectory_evaluation"></a>

## 補題 `c6C1C3C4A7GlobalPathJointLaw_trajectory_evaluation`

### 式

$$
\text{時刻 }s\text{ での軌道の評価の周辺}=\text{接続した軌道の点の質量}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

時刻 \(s\) での、大域の接続した軌道の評価の周辺は、接続した軌道の \(s\) での値の点の質量です。

### 証明の概略

1. 軌道の成分は決定論的。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_stageEvaluation"></a>

## 補題 `c6C1C3C4A7PathJointLaw_stageEvaluation`

### 式

$$
\text{段の経路の評価の周辺}=\text{段の軌道の値の点の質量}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の経路の評価の周辺は、段の軌道の値の点の質量です。

### 証明の概略

1. 経路の成分は決定論的。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_entropyEvaluation"></a>

## 補題 `c6C1C3C4A7PathJointLaw_entropyEvaluation`

### 式

$$
\text{観測エントロピーの評価の周辺}=\delta_{3s}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

観測エントロピーの評価の周辺は、\(3s\) の点の質量です。

### 証明の概略

1. 段の経路の観測エントロピーが \(3s\)。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_cognitiveEvaluation"></a>

## 補題 `c6C1C3C4A7PathJointLaw_cognitiveEvaluation`

### 式

$$
\text{認知座標の評価の周辺}=\delta_{q(s)}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

認知座標の評価の周辺は、認知座標の値の点の質量です。

### 証明の概略

1. 経路の認知座標。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathJointLaw_c3_marginal"></a>

## 補題 `c6C1C3C4A7PathJointLaw_c3_marginal`

### 式

$$
\text{同時に観測される C3 の情報 joint 座標}
$$

### Lean のコメント（日本語訳）

> A7 stage path lawで、同時に観測されるC3の情報joint座標。

### 補題の説明

A7 の段の経路の法則で、同時に観測される C3 の情報の結合法則の座標です。

### 証明の概略

1. 元の結合法則の C3 の情報の座標の周辺。

----

<a id="Tomabechi.Consistency.C6.C6C4FlowTCZAdapter"></a>

## 構造体 `C6C4FlowTCZAdapter`

### 式

$$
\text{C4 の履歴 flow と正準 TCZ・全層 carrier を、共通制御核と同じ制御データへ結ぶ}
$$

### Lean のコメント（日本語訳）

> C4の履歴flowと正準TCZ・全層carrierを、共通制御核と同じ制御データへ結ぶ。固定点の位相・完備性・縮小率の全署名は別途必要である。

### 定義の説明

C4 の履歴の流れと、正準の TCZ・全層の担体を、共通の制御核と同じ制御データへ結びます。固定点の位相・完備性・縮小率の全署名は、別途必要です。フィールドは、各履歴・全初期状態の C4 の勾配流を共有核の中心更新から回収、C4 の正準 TCZ は履歴ごとの全自然数の担体に等しい、層ごとの TCZ と担体の等式を元の全自然数の添字で保持、同じ履歴別 SC の固定点を保持し履歴で値が分かれる、固定点の全座標が共通層の履歴表象を復元、固定点を C3 の \(\Gamma\) の符号に入れると 25 の共有 SCM の関係状態になる、引き戻し距離から得る等長写像と積部分空間位相の同相写像は同じ写像、同じ SC 距離の上で C4 の逆極限が完備、同じ距離・同じ層作用素が率 \(\exp(-1)\) で縮小、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C4FlowTCZAdapter"></a>

## 定義 `c6C4FlowTCZAdapter`

### 式

$$
\mathrm{C6C4FlowTCZAdapter}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

C4 の流れ・TCZ のアダプターの、具体的な証人です。

### 証明の概略

1. 各フィールドは、C4 の履歴の流れの射影の補題（`centeredGainEntropyStep_projects_C4_history_flow`）と、定理 16→25 の既存の補題（担体・固定点・完備性・縮小性）から。

----

<a id="Tomabechi.Consistency.C6.c6C4FlowTCZAdapter_nonempty"></a>

## 補題 `c6C4FlowTCZAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C4 の流れ・TCZ のアダプターが存在します。

### 証明の概略

1. `c6C4FlowTCZAdapter` が証人。

----

<a id="Tomabechi.Consistency.C6.C6CommonPotentialAdapter"></a>

## 構造体 `C6CommonPotentialAdapter`

### 式

$$
\text{C1–C5 の異なる評価量を、係数・基準値を保って共通二次評価または完全状態エントロピー生成へ結ぶ}
$$

### Lean のコメント（日本語訳）

> C1–C5の異なる評価量を、係数・baselineを保って共通二次評価または完全状態entropy生成へ結ぶS2の部分adapter。

### 定義の説明

C1–C5 の異なる評価量を、係数・基準値を保って、共通の二次評価、または完全状態のエントロピー生成へ結ぶ、S2 の部分アダプターです。フィールドは、C1 の定理 1 の評価（閾値の基準値 1 と残差の係数 16 を保つ）、有限層に C1 の評価を置く候補で最大ゲインの割引費用が最小、C2 の完全状態上の一般化エントロピーの生成率 1、C3 の元の H-stage の段評価を段の共通束の表象へ同定、C4 の履歴ごとのポテンシャルを共通二次評価へ同定、C5 の上位の走行費は係数 6 の共通二次評価、C5 の上位の最適価値は係数 2 の共通二次評価、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6CommonPotentialAdapter"></a>

## 定理 `c6CommonPotentialAdapter`

### 式

$$
\mathrm{C6CommonPotentialAdapter}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通ポテンシャルのアダプターが成り立ちます。

### 証明の概略

1. 各フィールドは、上の補題（`c1V0_eq_baseline_add_centeredPotential`・`c1FiniteLayer_discounted_cost_minimal_pointwise`・C3/C4 の評価の同定・`c5RunningCost_eq_six_centeredPotential`・`c5OptimalValue_eq_two_centeredPotential`）。

----

<a id="Tomabechi.Consistency.C6.c6CommonPotentialAdapter_nonempty"></a>

## 補題 `c6CommonPotentialAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

共通ポテンシャルのアダプターが存在します。

### 証明の概略

1. `c6CommonPotentialAdapter` が証人。

----

<a id="Tomabechi.Consistency.C6.C6C1C3C4A7PathLawAdapter"></a>

## 構造体 `C6C1C3C4A7PathLawAdapter`

### 式

$$
\text{段 }n\text{ の結合法則アダプター（C1/C2/C4/C5 観測と C3 情報法則を保ち、A7 収支を満たす）}
$$

### Lean のコメント（日本語訳）

> C1/C2/C4/C5観測とC3情報lawを保ち、元H-stage全pathのA7収支も満たす段nの結合law adapter。C3/C4の共通law証人にはN4/N6等の既存条件が含まれる。

### 定義の説明

C1/C2/C4/C5 の観測と C3 の情報の法則を保ち、元の H-stage の全経路の A7 収支も満たす、段 \(n\) の結合法則のアダプターです。C3/C4 の共通法則の証人には、N4/N6 などの既存の条件が含まれます。フィールドは多数ありますが、大きくは次のとおりです。

* 結合法則 `law` が経路の押し出しで確率測度、段の端点の観測の周辺、C3 の情報の周辺、
* C3/C4 の元のアダプター、共有ポテンシャル、C4 の流れ・TCZ のアダプター、
* C1/C2/C5 の箱の保存・最適性の保存（同じ C1 の箱の文脈ごとの元の argmin と C5 の実フィードバックの最適性）、N7 で参照する各文脈の非空の証拠、
* C1 のサンプルが C3 の中心列を通る時刻の発散・H-stage への到達・C5 の価値の差と正値・0 への収束、
* 段・接続した C1 のゲインとその一致・大域の認知座標の一致、
* サンプル付き経路・大域の経路の法則とその周辺・C1/C4 の観測・実際の SCM の観測の法則、
* C4 の無作為化した履歴の法則が元の SCM の法則・正の質量・25-A(2)・介入の制御・費用の結合法則、
* 大域経路の評価、C4 の true の制御・住所が履歴・N5 の混合の目標の証人・大域の流れの非定常、C5 の最適な流れ・alive・一般化エントロピー、接続した経路の単射性、段の A7 収支・再始動、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathLawAdapter"></a>

## 定義 `c6C1C3C4A7PathLawAdapter`

### 式

$$
\mathrm{C6C1C3C4A7PathLawAdapter}(n,x,t_0,t,T,\tau)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段 \(n\) の結合法則のアダプターの、具体的な証人です。

### 証明の概略

1. 各フィールドに、上のファイルの定義・補題を代入する。この定義の長さは、フィールドの多さによる。

----

<a id="Tomabechi.Consistency.C6.c6C1C3C4A7PathLawAdapter_nonempty"></a>

## 補題 `c6C1C3C4A7PathLawAdapter_nonempty`

### 式

$$
\mathrm{Nonempty}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

結合法則のアダプターが存在します。

### 証明の概略

1. `c6C1C3C4A7PathLawAdapter n x t₀ t T τ` が証人。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
