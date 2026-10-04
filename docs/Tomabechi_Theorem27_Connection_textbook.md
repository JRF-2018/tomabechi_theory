# Tomabechi/Theorem27/Connection.lean 解説

> 対象: [`Tomabechi/Theorem27/Connection.lean`](../Tomabechi/Theorem27/Connection.lean)（定理27.6以降の残差減衰と行為帰結への接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| やり直し則（半群則） | 途中の時刻から同じ方策でやり直しても同じ軌道になる性質。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| 右微分商（Dini 微分） | 右側から見た傾き \(\frac{f(z)-f(x)}{z-x}\)（\(z\downarrow x\)）。折れ曲がりでも定義できる。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理27の (27.6) 以降（**残差の減衰・行為への帰結**）を、定理26の**フィードバックの流れ**（PZS・\(J^\*\)・軌道が同じフィードバックの力学から決まる）に**接続**するファイルです。`Abstract.lean`（無明の分類と目標の外の残差の下降）と `Actuator.lean`（アクチュエータへの帰属・行の非零性）の結果を、同じ共通の最適フィードバックの流れに載せます。

- **(27.6)**：無明（\(x\notin N_{\text{top}}\)）なら、残差は**定量的に下降**し、その速さは**正**。
- **(27.7)**：無明から、アクチュエータの寄与が正、入力の差（**行**）が非零。
- **(27.9)**：目標への進入の後は、残差の下降率が 0、行（アクチュエータの寄与）も a.e. で 0（**寂静**）。
- **(27.10)**：「操作的な無明 ⇔ 残差が正の速さで下降 ⇔ 行の寄与が正」（a.e.）。

### 0.2 このファイルが証明していないこと

- 将来の測度・フィードバックの許容性・軌道の走る価値・大域的な最適性/達成・条件 26-A/27-A（Lyapunov 関数の評価・連鎖律・参照ループの相殺など）は、**すべて明示的な仮定**です。結論は、(27.6) と同じく**点ごと**（または a.e.）の量化です。
- 「無明」「行」は、**モデル相対の操作的な定義**で、仏教語の思想的な意味と同一視してはいけません。
- 定理26の「単一の共通フィードバック」は、各初期の組から同じフィードバックを使うという再始動の整合性（`restart`）を仮定します。

### 0.3 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理 27.6 以降の、残差の減衰と、行為の帰結への接続。

名前空間は `Tomabechi.Theorem27`。`open _root_.Tomabechi.Theorem24_26`。

---

<a id="Tomabechi.Theorem27.residualDescentRateAlong"></a>

## 定義 `residualDescentRateAlong`

### 式

$$\text{Des}(t)=-\overline D^+\bigl(W(s,x(s))\bigr)(t)$$

### Lean のコメント（日本語訳）

> 指定した閉ループの軌道に沿った、残差の下降率。論文の記法 \(\mathrm{Des}=-D^+W\) に従う。

### 定義の説明

軌道に沿った残差 \(W(s,x(s))\) の下降の速さ（上右 Dini 微分の符号反転）です。

### 証明の概略

1. 定義：`-Actuator.upperRightDiniDerivative (fun s => W s (x s)) t`。

----

<a id="Tomabechi.Theorem27.theorem27_residual_descent_at_time"></a>

## 定理 `theorem27_residual_descent_at_time`

### 式

$$x(t)\notin N(t)\ \Longrightarrow\ \text{decayRate}\,c_1\,d(x(t),N(t))^2\le\text{Des}(t)\ \wedge\ \text{Des}(t)>0$$

### Lean のコメント（日本語訳）

> 時間に依存する閉の零残差の目標についての、点ごとの式 (27.6)。下側の距離の比較と、厳密な Dini の減衰は、まさに 26-A から継承される条件であり、操作的な無明は \(x\,t\notin N\,t\) である。

### 補題の説明

**(27.6)**：目標の外なら、残差は定量的に（距離の 2 乗に比例して）、正の速さで下降します。

### 証明の概略

1. `residual_descent_of_outside_closed_target`（Abstract）と、Dini の減衰（\(\text{decayRate}\,W\le\text{Des}\)）、下側の距離の比較 \(c_1d^2\le W\)。

----

<a id="Tomabechi.Theorem27.theorem27_feedback_ignorance_implies_residual_descent"></a>

## 定理 `theorem27_feedback_ignorance_implies_residual_descent`

### 式

$$\text{無明（PZS でない）}\ \Longrightarrow\ \text{decayRate}\,c_1\,d(x(t),N_{\text{top}}(t))^2\le\text{Des}(t)\ \wedge\ \text{Des}(t)>0$$

### Lean のコメント（日本語訳）

> 統合された最上位の結論 (27.6)：共通の最適フィードバックと、定理26の PZS の定義のもとで、生存する初期の組からの操作的な無明は、定量的な残差の下降の境界を意味する。データは、指定した軌道に沿った初期の組 \((x\,t,t)\) で添字づけられる。将来の時間の測度、フィードバックの許容性と軌道の走る価値、大域的な最適性/達成、条件 26-A は、すべて明示的な仮定であり、結論は、(27.6) のとおり、点ごとである。

### 補題の説明

定理26の「PZS ⇔ 目標への所属」（`feedbackPZS_iff_mem_theorem26ZeroValueTarget`）を使って、「PZS でない」を「目標の外」に翻訳し、`theorem27_residual_descent_at_time` に渡します。

### 証明の概略

1. `feedbackPZS_iff_mem_theorem26ZeroValueTarget`（Theorem24_26）で \(x(t)\notin N_{\text{top}}(t)\)。
2. `theorem27_residual_descent_at_time` を適用。

----

<a id="Tomabechi.Theorem27.theorem27_feedbackFlow_ignorance_implies_residual_descent"></a>

## 定理 `theorem27_feedbackFlow_ignorance_implies_residual_descent`

### 式

$$\text{(27.6)}\ \text{(走る価値 = 流れに沿った }V\text{)}$$

### Lean のコメント（日本語訳）

> (27.6) の流れに基づく版。走る価値は、もはや独立の族ではない：それは、同じフィードバックが、同じ初期の組から生成する軌道に沿って評価した \(V\) である。したがって、PZS・\(J^\*\)・Lyapunov の残差が下降する軌道が、1 つの明示的なフィードバックの力学のモデルを共有する。

### 補題の説明

上の定理の、走る価値を `V (flow π y S s) s`（流れに沿った評価）として具体化した版です。

### 証明の概略

1. 上の定理を、`runningValue π y S s := V (flow π y S s) s` として適用。

----

<a id="Tomabechi.Theorem27.theorem27_feedbackFlow_ignorance_implies_actuator_action_of_ac_ode"></a>

## 定理 `theorem27_feedbackFlow_ignorance_implies_actuator_action_of_ac_ode`

### 式

$$\text{a.e.で PZS でない}\ \Longrightarrow\ 0<-\langle\nabla W,G\Delta u\rangle\ \wedge\ \Delta u\neq0\ \wedge\ G\Delta u\neq0\ \ \text{a.e.}$$

### Lean のコメント（日本語訳）

> 流れの水準の含意 (27.7)。方策は大域的な Markov フィードバックであり、その走る価値は、それ自身の状態の流れに沿って評価した \(V\) である。再始動の恒等式は、指定した閉ループの軌道の各将来の区間を、その現在の状態から始めた同じフィードバックに結びつける。PZS のほとんど至るところの失敗から、定理26の最適値の特徴づけと 26-A は、ほとんど至るところ正の残差を意味し、そのあと、27-A の連鎖律と参照ループの相殺が、正のアクチュエータの寄与と、非零の入力/状態の作用を与える。

### 補題の説明

**(27.7)（フィードバックの流れ版）**：無明（PZS でない）から、行（入力の差）が非零。

### 証明の概略

1. a.e. で PZS でない ⇒ 目標の外（定理26の `feedbackPZS_iff_mem_theorem26ZeroValueTarget_expDiscount`）。
2. `Actuator.ae_ignorance_implies_model_relative_action_of_ac_ode`（Actuator）を適用して、行の寄与が正、入力差が非零、\(G\Delta u\ne0\) を得る。入力差の下界の版は `ae_control_difference_distance_lower_bound_of_dini_of_ac_ode`（108 行）。

----

<a id="Tomabechi.Theorem27.theorem27_target_entry_implies_quiescence"></a>

## 定理 `theorem27_target_entry_implies_quiescence`

### 式

$$x(T)\in N_{\text{top}}(T)\ \Longrightarrow\ \forall t\ge T:\ \text{Des}(t)=0\ \wedge\ \langle\nabla W,G\Delta u\rangle=0\ \text{a.e.}$$

### Lean のコメント（日本語訳）

> (27.9) の目標への進入の部分で、目標は、定理26の零の最適値の集合に固定される。両側の 26-A の距離の比較が、まず \(N_{\text{top}}\) の上で \(W=0\) を与え、そのあと、前向きの不変性が、すべての後の時刻での零の Dini の下降と、その後ほとんど至るところでのアクチュエータの寄与の零を与える。

### 補題の説明

**(27.9)（寂静）**：寂静の集合 \(N_{\text{top}}\) に入ったら、残差の下降は止まり、行（アクチュエータの寄与）も消えます。

### 証明の概略

1. `residual_eq_zero_on_theorem26_target`（Abstract）で \(N_{\text{top}}\) 上で \(W=0\)。
2. `residualDescentRate_zero_after_target_entry` と `ae_actuator_contribution_zero_after_target_entry`（Actuator）。

----

<a id="Tomabechi.Theorem27.theorem27_target_entry_implies_quiescence_on_future"></a>

## 定理 `theorem27_target_entry_implies_quiescence_on_future`

### 式

$$\text{将来の ray 版の (27.9)}$$

### Lean のコメント（日本語訳）

> (27.9) の将来の領域のアダプタ。目標への進入/零の下降の部分は、すべての後の時刻での点ごとのものであり、アクチュエータの結論のための、モデルのデータと正則性は、将来の半直線の上のほとんど至るところでだけ必要である。

### 補題の説明

将来の半直線だけの仮定で成り立つ版です。

### 証明の概略

1. `ae_actuator_contribution_zero_after_target_entry_on_future`（Actuator）。

----

<a id="Tomabechi.Theorem27.theorem27_feedbackPZS_entry_implies_quiescence"></a>

## 定理 `theorem27_feedbackPZS_entry_implies_quiescence`

### 式

$$\text{PZS}\ \Longleftrightarrow\ \text{entry to}\ N_{\text{top}}\ \Longrightarrow\ \text{寂静 (27.9)}$$

### Lean のコメント（日本語訳）

> 定理26の PZS そのものからの、式 (27.9)。共通の Markov フィードバックの流れと、走る価値 \(V\) が、PZS と \(J^\*\) を定義する。その最適性は、PZS を \(N_{\text{top}}\) への進入と同一視する。条件 26-A の両側の距離の境界が、そこで零の残差を与え、26-A/27-A の不変性と力学が、論文の点ごと/a.e. の量化で、2 つの静止の結論を与える。

### 補題の説明

PZS（永続的な苦ゼロ）のフィードバックの流れから出発して、寂静の集合へ入ったことを導き、(27.9) の結論を得ます。

### 証明の概略

1. `feedbackPZS_iff_mem_theorem26ZeroValueTarget` で PZS ⇔ 目標への所属。上の `theorem27_target_entry_implies_quiescence` を適用。

----

<a id="Tomabechi.Theorem27.theorem27_operational_ignorance_iff_descent_and_action_ae"></a>

## 定理 `theorem27_operational_ignorance_iff_descent_and_action_ae`

### 式

$$\text{a.e.}:\ \text{無明}\Longleftrightarrow\text{Des}>0\ \wedge\ \text{無明}\Longleftrightarrow\text{sankhara27Contribution}$$

### Lean のコメント（日本語訳）

> 定理26の PZS の特徴づけのあとの、式 (27.10)：操作的な無明が、点ごとに、\(N_{\text{top}}\) の外にあることと同一視されると、既存の Lyapunov とアクチュエータの同値が、論文のほとんど至るところの同値を、2 つとも与える。2 つの結論は、異なる量化と仮定を保つ：(27.10) の下降の同値は 26-A を使い、そのアクチュエータの同値は、27-A も使う。

### 補題の説明

**(27.10)**：操作的な無明 ⇔ 残差が正の速さで下降 ⇔ 行の寄与が正（a.e.）。

### 証明の概略

1. `ae_outside_target_iff_positive_descent`（Abstract）と `ae_outside_target_iff_positive_actuator_contribution_of_dini`（Actuator）を、無明 ⇔ 目標の外（定理26）につなぐ。

----

<a id="Tomabechi.Theorem27.theorem27_operational_ignorance_iff_descent_and_action_ae_after_time"></a>

## 定理 `theorem27_operational_ignorance_iff_descent_and_action_ae_after_time`

### 式

$$\text{(27.10) の将来の ray 版}$$

### Lean のコメント（日本語訳）

> (27.10) の将来の半直線の形。すべての目標と 26-A の境界は、\([T,\infty)\) の上でだけ要求され、定理26の非負の時間の領域に合う。結論は、同じ制限された将来の Lebesgue 測度を使う。連鎖律の仮定は、27-A の大域的な Lebesgue-a.e. の仮定のままで、そのあと、半直線に制限する。

### 補題の説明

(27.10) を \([T,\infty)\) の仮定だけで述べた版です。

### 証明の概略

1. 上の定理を、将来の測度で。

----


## コメント修正記録

（なし）
