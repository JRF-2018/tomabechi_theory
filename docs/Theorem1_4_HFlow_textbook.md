# Theorem1_4_HFlow.lean 解説

> 対象: [`Theorem1_4_HFlow.lean`](../Theorem1_4_HFlow.lean)（定理1〜4のH-flowアダプタ（方策の流れから軌道と到達集合を生成））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 基礎評価関数 \(V_0\) | 不快・不安定・内部不整合などのコスト。小さいほどよい。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 誤差境界 | \(\operatorname{dist}^2\le C\,\Phi\)。残差が小さいなら目標に近い、という保証。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| H-flow | 1つの閉ループ方策の、軌道・出発点・やり直し則をまとめたデータ（`ClosedLoopPolicyFlow`）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理1・2・3・4 の「到達可能な目標領域への収束」の定理を、**1 つの閉ループの方策の流れ**（`ClosedLoopPolicyFlow`）から**軌道と到達可能集合の両方を生成する**形に結ぶ、**アダプタ**（つなぎの定理）です。定理1では「評価する軌道」と「到達可能な目標領域」を別々に仮定していましたが、ここでは同じ方策の流れ \(F\) から両方を作ります。

### 0.2 構成

| 宣言 | 内容 |
| --- | --- |
| `theorem1_policy_flow_reachable_tcz_distance_tendsto_zero` | 定理1：方策の流れから軌道と到達集合を生成 |
| `weighted_policy_flow_reachable_tcz_distance_tendsto_zero` | 定理4（臨場感加重） |
| `policy_flow_reachable_quantitative_conclusion` | 定理2（共有 TCZ） |
| `policy_flow_reachable_state_tcz_from_statePairSystem` | 定理3/P2（抽象共有 TCZ） |

### 0.3 このファイルが証明していないこと

- **前向き不変性**（到達集合から出発した流れが到達集合に留まること）は、原文の条件として**明示的に保持**します。有限ホライズンの最適性だけからは出ません。
- Lyapunov 残差の**正則性・下降・目標の非空性・誤差境界**は、定理1〜4の結論と同じく**明示的な仮定**です。
- 方策の流れそのものの存在・一意性は扱いません（構造体 `ClosedLoopPolicyFlow` が与える）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理1と4（および2・3）の H-flow アダプタ**
>
> これらのインターフェースは、1 つの `ClosedLoopPolicyFlow` から、方策の軌道と、その時刻ごとの到達可能な集合を構成する。Lyapunov の正則性・下降・目標の非空性・誤差境界の仮定は、明示的なままである。

（H-flow：方策の「流れ」（flow）から作る、の意。）名前空間は `Tomabechi.Theorem1`・`Tomabechi.Theorem4`・`Tomabechi.Theorem2.StatePairResidualSystem`・`Tomabechi.Theorem3.AbstractSharedSystem`。`open MeasureTheory Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem1.theorem1_policy_flow_reachable_tcz_distance_tendsto_zero"></a>

## 定理 `theorem1_policy_flow_reachable_tcz_distance_tendsto_zero`

### 式

$$\operatorname{dist}\bigl(F(t_0,x_0)(t),\ \{y\in\text{Reach}\mid V_0(y,t)\le\theta\}\bigr)\le\sqrt{C\,r_1(t_0)}\,e^{-c(t-t_0)}\ \wedge\ \to0$$

### Lean のコメント（日本語訳）

> 評価する軌道とその到達可能な目標の、両方が 1 つの選択された方策の流れから生成される、定理1。前向きの不変性は、原文の条件として明示的に保持する。有限ホライズンの最適性だけからは、それは得られない。

### 補題の説明

**定理1の方策の流れ版**：同じ方策の流れ \(F\) から、軌道 \(F(t_0,x_0)(t)\) と、到達可能集合 `policyFlowReachableAt F initialSet t₀`（その閉包 `closedLoopReachableSet`）を作り、閾値 \(\theta\) 以下の到達可能な点の集合（目標領域）への距離が指数的に減ることを示します。

### 証明の概略

1. `theorem1_reachable_tcz_distance_tendsto_zero`（Theorem1 の到達可能集合版）を、軌道 `F.flow t₀ x₀`、到達可能集合 `policyFlowReachableAt F initialSet t₀` で適用する。

----

<a id="Tomabechi.Theorem4.weighted_policy_flow_reachable_tcz_distance_tendsto_zero"></a>

## 定理 `weighted_policy_flow_reachable_tcz_distance_tendsto_zero`

### 式

$$\operatorname{dist}\bigl(F(t_0,x_0)(t),\Omega_P\bigr)\le\sqrt{C\,r_4(t_0)}\,e^{-c(t-t_0)}\ \wedge\ \to0$$

### Lean のコメント（日本語訳）

> 評価する軌道と、その臨場感加重 TCZ で使う到達可能な集合を、同じ選択された方策の流れが生成する、定理4。

### 補題の説明

**定理4（臨場感加重）の方策の流れ版**です。

### 証明の概略

1. `weighted_reachable_tcz_distance_tendsto_zero`（Theorem4）を適用。

----

<a id="Tomabechi.Theorem2.StatePairResidualSystem.policy_flow_reachable_quantitative_conclusion"></a>

## 定理 `policy_flow_reachable_quantitative_conclusion`

### 式

$$\text{ReachableStatePairConclusion}\ (\text{共同方策の流れ})$$

### Lean のコメント（日本語訳）

> 定理2のアダプタ：共同の閉ループの方策の流れが、多主体の軌道と、共有 TCZ で使う到達可能な集合の、両方を生成する。

### 補題の説明

**定理2（共有 TCZ）の方策の流れ版**：全主体の状態の積空間で動く共同の方策の流れから、軌道と到達集合を作ります。

### 証明の概略

1. `theorem2_reachable_state_pair_quantitative_conclusion`（Theorem2）を、軌道 `F.flow t₀ x₀` で適用。

----

<a id="Tomabechi.Theorem3.AbstractSharedSystem.policy_flow_reachable_state_tcz_from_statePairSystem"></a>

## 定理 `policy_flow_reachable_state_tcz_from_statePairSystem`

### 式

$$\text{軌道は閉到達集合内},\ \text{共有 TCZ・LUB 表象への指数評価と極限}$$

### Lean のコメント（日本語訳）

> 定理3/P2 のアダプタ：1 つの共同の方策の流れが、積状態の軌道と到達可能な集合を供給する。同じ明示的な状態の写像が、その軌道を、定理2の残差の系に結びつける。

### 補題の説明

**定理3の方策の流れ版**です。

### 証明の概略

1. `theorem3_reachable_state_tcz_from_statePairSystem`（Theorem3）を適用。

----


## コメント修正記録

（なし）
