# Tomabechi/Consistency/ConsistencyC6_CenteredContexts.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyC6_CenteredContexts.lean`](../Tomabechi/Consistency/ConsistencyC6_CenteredContexts.lean)（凍結した中心を保つ、完全状態から二主体状態への射影）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理1・2・4・20 の**二主体の状態**と、定理16・25 や段階の谷の**完全状態**（認知座標 \(q\) と物理の観測量 \(y\)）を、**一つの射影**で結ぶファイルです。無矛盾性の証明（[見取り図](Consistency_Overview.md)）の「統合モデル」（C6）の部品です。

* **凍結した中心 \(c\)** と**保存された平均 \(m\)** を決めると、完全状態 \(z\) から二主体の状態 \((m+(c-q),\ m-(c-q))\) が復元できます（`centeredC1Projection`）。差の半分は \(c-q\)。
* この射影のもとで、有限層の走行費は \(1+16P_c\)（\(P_c=(q-c)^2/2\)）。
* **段階の谷（C3）の段**の軌道、**定理16・25（C4）の履歴**の軌道は、この射影で、二主体モデルの**ゲイン 1** の実際の制御軌道に移ります。
* 閾値の換算：C4 のポテンシャルの閾値 \(\tfrac12\) は、走行費の閾値 9 に対応します。
* **段の切り替え**で中心が変わるのは、文脈の変更であり、完全状態の不連続ではありません。

### 0.2 このファイルが証明していないこと

* 射影は全域で定義されますが、定理1を適用するには箱に入ることが別に必要です。
* 評価の無条件な同一視はしません（基準値 1・係数 16・閾値の換算を明示しています）。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 元の認知座標 q を変えず、context の中心 c を明示して二主体状態を読む。半差は c-q であり、有限層費用は 1+16P_c となる。段切替での中心変更は context の変更であり、この射影の値を完全状態の不連続と解釈しない。

---

<a id="Tomabechi.Consistency.C6.centeredC1Projection"></a>

## 定義 `centeredC1Projection`

### 式

$$
(m+(c-q),\ m-(c-q))
$$

### Lean のコメント（日本語訳）

> 保存平均mと凍結中心cから二主体を復元する。全域で定義するが、定理1の適用には別途box所属が必要である。

### 定義の説明

完全状態 \(z\)（認知座標 \(q\)）を、**保存された平均 \(m\)** と**凍結した中心 \(c\)** から、二主体の状態 \((m+(c-q),\ m-(c-q))\) に**復元**する写像です。差の半分は \(c-q\) です。全域で定義されますが、定理1を適用するには、箱に入っていることが別に必要です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_mean"></a>

## 補題 `centeredC1Projection_mean`

### 式

$$
\text{mean}(\mathrm{proj})=m
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

復元した二主体の平均は、保存平均 \(m\) です。

### 証明の概略

1. 定義を展開して整理する（`simp`）。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_halfDifference"></a>

## 補題 `centeredC1Projection_halfDifference`

### 式

$$
\text{halfDiff}(\mathrm{proj})=c-q
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

復元した二主体の差の半分は、\(c-q\) です。

### 証明の概略

1. 定義を展開（`simp`）。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_runningCost"></a>

## 補題 `centeredC1Projection_runningCost`

### 式

$$
\text{有限層の走行費}=1+16\,P_c(z)
$$

### Lean のコメント（日本語訳）

> 同じ元状態での費用保存。box外でもDの実走行費の等式は成立する。

### 補題の説明

同じ元の状態での**費用の保存**です。有限層の走行費は \(1+16P_c(z)\)（\(P_c=(q-c)^2/2\)）に等しいです。箱の外でも、この走行費の等式は成り立ちます。

### 証明の概略

1. 有限層の走行費は \(1+8\,(\text{差の半分})^2\)。
2. 差の半分は \(c-q\)（前の補題）なので \(1+8(c-q)^2=1+16\cdot\tfrac{(q-c)^2}2\)。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_all_controls"></a>

## 補題 `centeredC1Projection_all_controls`

### 式

$$
\mathrm{proj}\bigl(\text{共通更新核}\bigr)=\text{二主体の実軌道}
$$

### Lean のコメント（日本語訳）

> 中心固定の共通更新核から、全許容ゲインの実二主体軌道を回収する。費用保存と同じ射影を使うので、中心一致だけの接続ではない。

### 補題の説明

中心を固定した**共通の更新核**を、この射影で二主体に移すと、**すべての許容ゲイン**が作る**実際の二主体の軌道**が回収されます。費用の保存と同じ射影を使うので、中心が一致するというだけの接続ではありません。

### 証明の概略

1. 二主体の軌道の定義（`controlledConsensusState`）を展開する。
2. 平均は保存平均、差の半分は \(c-q\)（前の補題）。更新核の認知座標は中心へ \(e^{-\text{累積ゲイン}}\) で近づく。
3. 成分ごとに一致を示す（`ext`）。

----

<a id="Tomabechi.Consistency.C6.c6UnitGainSignal"></a>

## 定義 `c6UnitGainSignal`

### 式

$$
u(t)\equiv1
$$

### Lean のコメント（日本語訳）

> 元C3の凍結段はゲイン1であり、C1の全可測[0,3]族に属する。最大ゲイン選択とは同一視しない。

### 定義の説明

ゲインが常に 1 の信号です。もとの段階の谷（C3）の凍結した段はゲイン 1 で、これは二主体モデルの許容ゲインの族（可測で \([0,3]\) に入るもの）に属します。**最大ゲイン 3 の選択とは別**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c6UnitGainSignal_accumulated"></a>

## 補題 `c6UnitGainSignal_accumulated`

### 式

$$
\int_T^t1=t-T
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

ゲイン 1 の累積量は \(t-T\) です。

### 証明の概略

1. 定数の積分（`simp`）。

----

<a id="Tomabechi.Consistency.C6.c3A7Stage_centeredC1_trajectory"></a>

## 補題 `c3A7Stage_centeredC1_trajectory`

### 式

$$
\mathrm{proj}(\text{C3 段の軌道})=\text{二主体の実制御軌道（ゲイン 1）}
$$

### Lean のコメント（日本語訳）

> 元C3段の時刻・状態を保持して、有限層の実制御軌道へ射影する。

### 補題の説明

段階の谷（C3）の段の軌道を、同じ時刻・同じ状態のまま、**有限層の実際の制御軌道**（ゲイン 1）に射影します。

### 証明の概略

1. 段の軌道は、中心 \(\mathrm{rep}(n+1)\) へゲインの累積量だけ近づく更新核。
2. 共通更新核の補題（`centeredC1Projection_all_controls`）をゲイン 1 に適用する。

----

<a id="Tomabechi.Consistency.C6.c3A7Stage_centeredC1_runningCost"></a>

## 補題 `c3A7Stage_centeredC1_runningCost`

### 式

$$
\text{走行費}=1+16\,V_{\text{eff}}^{\text{段}}
$$

### Lean のコメント（日本語訳）

> 同じ元C3段の実効評価を、同じ射影上のD費用として読む。baseline1と係数16を保ち、評価の無条件な同一視を避ける。

### 補題の説明

同じ段の実効評価（段階の谷の有効ポテンシャル）を、同じ射影の上の**有限層の走行費**として読みます。基準値 1 と係数 16 を保ち、評価の無条件な同一視は避けています。

### 証明の概略

1. 走行費の保存（`centeredC1Projection_runningCost`）。
2. 中心二次のポテンシャルが、段の有効ポテンシャルに等しい（`centeredQuadraticPotential_eq_C3_stage`）。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_mem_box_iff"></a>

## 補題 `centeredC1Projection_mem_box_iff`

### 式

$$
\mathrm{proj}\in\mathrm{box}\iff|m\pm(c-q)|\le\tfrac14
$$

### Lean のコメント（日本語訳）

> 箱内条件を中心からの距離と保存平均で判定する。射影の全域定義から、定理1の適用域を無条件に推論しない。

### 補題の説明

復元した二主体が箱に入ることと、\(\lvert m+(c-q)\rvert\le\tfrac14\) かつ \(\lvert m-(c-q)\rvert\le\tfrac14\) は同値です。射影が全域で定義されているからといって、定理1の適用域を無条件に推論はしません。

### 証明の概略

1. （→）箱の定義から各座標の評価を取り出す。（←）各座標の評価をそのまま箱の定義に入れる。

----

<a id="Tomabechi.Consistency.C6.c4CenteredCompleteTrajectory"></a>

## 定義 `c4CenteredCompleteTrajectory`

### 式

$$
\text{C4 履歴 }h\text{ の完全状態の軌道}
$$

### Lean のコメント（日本語訳）

> C4履歴contextの完全状態。物理観測は元のq,y上に保持する。

### 定義の説明

定理16・25（C4）の履歴 \(h\) の文脈での、完全状態の軌道です。物理の観測量は、もとの \((q,y)\) の上に保持します。履歴の中心（\(\mathrm{theorem16\_intervalGradientCenter}\ h\)）へ、ゲイン 1 で近づく更新核を使います。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.C6.c4CenteredC1_trajectory"></a>

## 補題 `c4CenteredC1_trajectory`

### 式

$$
\mathrm{proj}(\text{C4 軌道})=\text{二主体の実制御軌道（ゲイン 1）}
$$

### Lean のコメント（日本語訳）

> C4全履歴・全初期状態で、同じ凍結中心射影がゲイン1の実軌道を回収する。

### 補題の説明

C4 のすべての履歴・すべての初期状態で、**同じ凍結中心の射影**が、ゲイン 1 の実際の軌道を回収します。

### 証明の概略

1. 共通更新核の補題（`centeredC1Projection_all_controls`）を、ゲイン 1・中心 \(=\) 履歴の中心に適用する。

----

<a id="Tomabechi.Consistency.C6.c4CenteredCompleteTrajectory_cognitive"></a>

## 補題 `c4CenteredCompleteTrajectory_cognitive`

### 式

$$
q(\text{C4 完全軌道})=\text{履歴勾配流}
$$

### Lean のコメント（日本語訳）

> 同じC4完全軌道の認知座標は元の履歴勾配流そのもの。

### 補題の説明

C4 の完全軌道の認知座標は、もとの**履歴の勾配流**そのものです。

### 証明の概略

1. 更新核の認知座標の式（`centeredGainEntropyStep_cognitive`）と、勾配流の式を比べる。

----

<a id="Tomabechi.Consistency.C6.c4CenteredC1_runningCost"></a>

## 補題 `c4CenteredC1_runningCost`

### 式

$$
\text{走行費}=1+16\,V_h(q)
$$

### Lean のコメント（日本語訳）

> 同じC4元状態で、有限層D費用と元の履歴potentialを換算する。

### 補題の説明

同じ C4 の元の状態で、有限層の走行費と、もとの履歴のポテンシャル \(V_h\) を換算します（走行費 \(=1+16V_h(q)\)）。

### 証明の概略

1. 走行費の保存（`centeredC1Projection_runningCost`）と、中心二次のポテンシャルが履歴ポテンシャルに等しい（`centeredQuadraticPotential_eq_C4`）。

----

<a id="Tomabechi.Consistency.C6.c4CenteredC1_threshold_iff"></a>

## 補題 `c4CenteredC1_threshold_iff`

### 式

$$
\text{走行費}\le9\iff V_h(q)\le\tfrac12
$$

### Lean のコメント（日本語訳）

> C4のpotential閾値1/2は有限層の基礎費用閾値9に対応する。C1の閾値1とは異なるcontextであり、到達集合条件は別途保持する。

### 補題の説明

C4 のポテンシャルの閾値 \(\tfrac12\) は、有限層の走行費の閾値 **9** に対応します（\(1+16\cdot\tfrac12=9\)）。二主体合意系（C1）の閾値 1 とは**別の文脈**で、到達集合の条件は別に保持します。

### 証明の概略

1. 走行費の式 \(1+16V_h(q)\le9\iff V_h(q)\le\tfrac12\)（一次不等式、`linarith`）。

----

<a id="Tomabechi.Consistency.C6.c4CenteredC1_canonicalTCZ_iff"></a>

## 補題 `c4CenteredC1_canonicalTCZ_iff`

### 式

$$
q\in\mathrm{TCZ}^{\text{正典}}_h\iff\exists\tau,\ q\in\mathrm{Reach}_\tau\ \wedge\ \text{走行費}\le9
$$

### Lean のコメント（日本語訳）

> C4正準TCZの到達条件を保った閾値換算。評価だけの部分集合をTCZと呼ばない。

### 補題の説明

C4 の正典 TCZ に属することを、到達条件を保ったまま、走行費の閾値 9 の条件に言い換えます。**評価の条件だけの部分集合を TCZ とは呼びません**（到達できることが必要）。

### 証明の概略

1. 正典 TCZ の定義（到達する点で評価が \(\tfrac12\) 以下）を展開する。
2. 閾値の換算（`c4CenteredC1_threshold_iff`）で評価の条件を書き換える。

----

<a id="Tomabechi.Consistency.C6.centeredC1Projection_context_change"></a>

## 補題 `centeredC1Projection_context_change`

### 式

$$
\text{halfDiff}_d=\text{halfDiff}_c+(d-c)
$$

### Lean のコメント（日本語訳）

> 同じ完全状態を次の中心contextへ渡すと、半差だけが中心差だけ変わる。完全状態自体の跳躍を仮定する式ではない。

### 補題の説明

同じ完全状態を、次の中心 \(d\) の文脈へ渡すと、差の半分だけが、中心の差 \(d-c\) だけ変わります。**完全状態そのものが跳ぶ**ことを仮定する式ではありません（段の切り替えは文脈の変更で、状態の不連続ではない）。

### 証明の概略

1. 差の半分の式（\(c-q\)、\(d-q\)）を代入して整理する。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
