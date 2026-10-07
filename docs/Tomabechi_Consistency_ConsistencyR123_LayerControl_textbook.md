# Tomabechi/Consistency/ConsistencyR123_LayerControl.lean 解説

> 対象: [`Tomabechi/Consistency/ConsistencyR123_LayerControl.lean`](../Tomabechi/Consistency/ConsistencyR123_LayerControl.lean)（正典 TCZ を生成する制御系を署名に入れる）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 絶対連続（AC） | ほとんど至る所で微分でき、導関数の積分で元に戻せる関数。折れ曲がりを許す程度の滑らかさ。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| Carathéodory 解 | 絶対連続で、ほとんど至る所 ODE を満たす解。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**正典 TCZ を生成する制御系を、署名に入れる**ファイルです。指摘は、16 の `VelControl`（速度制御）と、24 の `C1GainSignal`（ゲイン制御）を、同じ添字で暗黙に使い分けていた、ということでした。ここでは、**層別の独立な生成系を認める形式化**（案 1）として、16 の層の TCZ 生成系を専用の署名 `CognitiveControlSystem` に入れ、各 \((\text{主体 }d,\text{履歴 }h,\text{層 }i)\) の表（`SharedModelSignature.layerControlTable`）で次を指定します。

| 項目 | 内容 |
|---|---|
| 状態型 | \(\mathbb R\)（認知座標） |
| 許容入力 | 可測で \(|u|\le1\) の信号（`VelControl`） |
| \(f(x,u,t)\) | \(u\)（状態について 0-Lipschitz） |
| 解 | \(x_0+\int_{t_0}^tu\)（**全開始時刻** \(t_0\)、Carathéodory 解：絶対連続・ほとんど至る所で微分可能） |
| 一意解 | 絶対連続で、ほとんど至る所で \(\dot x=u\)、初期値 \(x_0\) なら、解に一致 |
| 到達集合 | \(\mathcal R(\tau;x_0,t_0)=\{\text{解}(\tau)\}=[x_0-(\tau-t_0),\,x_0+(\tau-t_0)]\)（全許容信号に量化） |
| 評価 | `N.data` の層 `index16 i` の実走行費の閾値集合 \(\Omega_\theta\)（`layerOmega`） |
| 正典 TCZ | \(\bigcup_{\tau\ge t_0}[\mathcal R(\tau;x_0,t_0)\cap\Omega_\theta(\tau)]\)（閉包なし）\(=\)`ball16 h` |

24 の制御系（`C1GainSignal`、`controlledConsensusState`）は**別の入力型・別の生成系**であり、この表では 16 の層の系として使いません。共有するのは、評価 \(\Omega\)（`N.data` の層の実走行費）と、選択方策の指定の軌道（`core_step_is_selected_flow`）だけです。

### 0.2 このファイルが証明していないこと

* これは、「**層別の生成系を認める定式化での同時充足**」であって、native の層の制御から、正典 TCZ を構成したものではありません。`nativeReach = velReach` を要求しません（同じ証人で、中心の所属が異なる：`core_step_misses_center` と `center_reached`）。
* 強い共有モデルの認定には、速度とゲインを**同じ制御族**に埋め込む別の証人（案 2）が必要で、本ファイルでは行いません。この点は、[見取り図](Consistency_Overview.md)の「限定」に記しています。

### 0.3 ファイル冒頭のコメント（日本語訳は原文が日本語なので、そのまま）

> 指摘：16 の VelControl（速度制御）と 24 の C1GainSignal（ゲイン制御）を同じ添字で暗黙に使い分けていた。ここでは層別の独立生成系を認める形式化（案1）として、16 の層の TCZ 生成系を専用の署名 CognitiveControlSystem に入れ、各 (主体 d, 履歴 h, 層 i) の表（SharedModelSignature.layerControlTable）で（上の表）を指定する。24 の制御系（C1GainSignal、controlledConsensusState）は別の入力型・別の生成系であり、この表では 16 の層の系として使わない。共有するのは評価 Ω（N.data の層の実走行費）と、選択方策の指定軌道（core_step_is_selected_flow）だけである。報告範囲：これは「層別生成系を認める定式化での同時充足」であって、native の層制御から正典 TCZ を構成したものではない。…強い共有モデルの認定には、速度とゲインを同じ制御族に埋め込む別証人（案2）が必要で、本ファイルでは行わない。

---

<a id="Tomabechi.Consistency.R123.velTrajAt"></a>

## 定義 `velTrajAt`

### 式

$$
x(t)=x+\int_{t_0}^tu
$$

### Lean のコメント（日本語訳）

> 開始時刻t₀、初期値xの解x+∫_{t₀}^{t}u。

### 定義の説明

開始時刻 \(t_0\)・初期値 \(x\) の**解** \(x+\int_{t_0}^tu\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velTrajAt_start"></a>

## 補題 `velTrajAt_start`

### 式

$$
x(t_0)=x
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻での値は、初期値です。

### 証明の概略

1. 積分の区間が空。`simp`。

----

<a id="Tomabechi.Consistency.R123.velTrajAt_lipschitz"></a>

## 補題 `velTrajAt_lipschitz`

### 式

$$
x(\cdot)\text{ は 1-Lipschitz}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

解は 1-Lipschitz です。

### 証明の概略

1. 差が \(\int_t^su\) で、絶対値は \(|s-t|\) 以下。

----

<a id="Tomabechi.Consistency.R123.velTrajAt_ac"></a>

## 補題 `velTrajAt_ac`

### 式

$$
x(\cdot)\text{ は全区間で絶対連続}
$$

### Lean のコメント（日本語訳）

> 全区間で絶対連続。

### 補題の説明

解は、全区間で絶対連続です。

### 証明の概略

1. Lipschitz なので絶対連続。

----

<a id="Tomabechi.Consistency.R123.velControl_locallyIntegrable"></a>

## 補題 `velControl_locallyIntegrable`

### 式

$$
u\text{ は局所可積分}
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容制御は、局所可積分です。

### 証明の概略

1. 各点の近傍の閉区間で可積分（有界・可測）。

----

<a id="Tomabechi.Consistency.R123.velTrajAt_ae_hasDerivAt"></a>

## 補題 `velTrajAt_ae_hasDerivAt`

### 式

$$
\dot x(t)=u(t)\ \ (\text{a.e.})
$$

### Lean のコメント（日本語訳）

> Carathéodory解：ほとんど至る所ẋ=u(t)（Lebesgueの微分定理）。

### 補題の説明

**Carathéodory の解**です。ほとんど至る所で \(\dot x=u(t)\) となります（Lebesgue の微分定理）。

### 証明の概略

1. 局所可積分な関数の積分は、ほとんど至る所で微分可能（`ae_hasDerivAt_integral`）。

----

<a id="Tomabechi.Consistency.R123.velTrajAt_unique"></a>

## 補題 `velTrajAt_unique`

### 式

$$
\text{AC・a.e. で }\dot y=u,\ y(t_0)=x\Rightarrow y=x(\cdot)
$$

### Lean のコメント（日本語訳）

> 一意性：ACで、ほとんど至る所ẏ=u、初期値xなら解に一致する。

### 補題の説明

**一意性**です。絶対連続で、ほとんど至る所 \(\dot y=u\)、初期値 \(x\) なら、解に一致します（開始時刻以降）。

### 証明の概略

1. 差 \(y-x(\cdot)\) は絶対連続で、ほとんど至る所で微分が 0。絶対連続関数は、導関数の積分で復元できる（微積分学の基本定理）ので、定数で、初期値が 0 なので 0。

----

<a id="Tomabechi.Consistency.R123.velReachAt"></a>

## 定義 `velReachAt`

### 式

$$
\mathcal R(\tau;x,t_0)=\{x(\tau)\mid u\text{ 許容}\}
$$

### Lean のコメント（日本語訳）

> 全許容信号に量化した、時刻τの到達集合ℛ(τ; x, t₀)。

### 定義の説明

全許容信号に量化した、時刻 \(\tau\) の**到達集合** \(\mathcal R(\tau;x,t_0)\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velReachAt_eq"></a>

## 補題 `velReachAt_eq`

### 式

$$
\mathcal R(\tau;x,t_0)=[x-(\tau-t_0),\ x+(\tau-t_0)]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

到達集合は、閉区間です。

### 証明の概略

1. 前のファイルの `velReach_eq` と同様。絶対値の評価と、定数の制御による実現。

----

<a id="Tomabechi.Consistency.R123.CognitiveControlSystem"></a>

## 構造体 `CognitiveControlSystem`

### 式

$$
\text{認知座標の制御系 }(\text{許容入力},f,\text{解},\text{ODE},\text{一意性})
$$

### Lean のコメント（日本語訳）

> 認知座標ℝの制御系（状態ℝ、入力ℝ）：許容入力・f(x,u,t)・全開始時刻の解・ODE・一意性。

### 定義の説明

認知座標 \(\mathbb R\) の**制御系**の型です（状態 \(\mathbb R\)、入力 \(\mathbb R\)）。フィールドは、許容入力、方程式 \(\dot x=f(x,u,t)\)、開始時刻 \(t_0\)・初期値 \(x\) の解、\(f\) が状態についてリプシッツ、解の初期値、解が絶対連続、解が ODE を満たす、一意性（絶対連続で、ほとんど至る所で ODE・初期値を満たす関数は、解に一致する）、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.CognitiveControlSystem.reach"></a>

## 定義 `CognitiveControlSystem.reach`

### 式

$$
\mathcal R(\tau;x,t_0)
$$

### Lean のコメント（日本語訳）

> 全許容入力に量化した到達集合ℛ(τ; x, t₀)。

### 定義の説明

全許容入力に量化した、到達集合 \(\mathcal R(\tau;x,t_0)\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velocityControlSystem"></a>

## 定義 `velocityControlSystem`

### 式

$$
\dot x=u,\ |u|\le1,\ \text{解 }x+\int_{t_0}^tu
$$

### Lean のコメント（日本語訳）

> 16の層のTCZ生成系：速度制御ẋ=u、許容入力は可測で|u|≤1、解はx+∫_{t₀}^{t}u。

### 定義の説明

16 の層の **TCZ を生成する系**です。速度制御 \(\dot x=u\)、許容入力は可測で \(|u|\le1\)、解は \(x+\int_{t_0}^tu\) です。\(f(x,u,t)=u\) は状態について 0-Lipschitz。各性質（初期値・絶対連続・ODE・一意性）は、前の補題から。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velocityControlSystem_reach_eq"></a>

## 補題 `velocityControlSystem_reach_eq`

### 式

$$
\mathcal R=[x-(\tau-t_0),\ x+(\tau-t_0)]
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

速度制御系の到達集合は、閉区間です。

### 証明の概略

1. `velReachAt_eq` に帰着。

----

<a id="Tomabechi.Consistency.R123.LayerControlSignature"></a>

## 構造体 `LayerControlSignature`

### 式

$$
\text{各 }(d,h,i)\text{ の制御系を指定する}
$$

### Lean のコメント（日本語訳）

> 各(d,h,i)の制御系を指定する署名field。

### 定義の説明

各 \((d,h,i)\) の制御系を指定する、**署名のフィールド**です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.velocityLayerControlSignature"></a>

## 定義 `velocityLayerControlSignature`

### 式

$$
\text{全 }(d,h,i)\text{ で速度制御系}
$$

### Lean のコメント（日本語訳）

> 16の層の系はすべての(d,h,i)で速度制御系。24のゲイン制御系は使わない。

### 定義の説明

16 の層の系は、すべての \((d,h,i)\) で速度制御系です。24 のゲイン制御系は使いません。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.canonicalTCZAt"></a>

## 定義 `SharedModelSignature.canonicalTCZAt`

### 式

$$
\bigcup_{\tau\ge t_0}[\mathcal R(\tau;x,t_0)\cap\Omega_\theta(\tau)]
$$

### Lean のコメント（日本語訳）

> 評価（N.dataの層の実走行費）と、制御系から作る正典TCZ ⋃_{τ≥t₀}[ℛ(τ;x,t₀) ∩ Ω_θ(τ)]。

### 定義の説明

評価（`N.data` の層の実走行費）と、制御系から作る、**正典の TCZ** \(\bigcup_{\tau\ge t_0}[\mathcal R(\tau;x,t_0)\cap\Omega_\theta(\tau)]\) です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.canonicalTCZAt_velocity_eq"></a>

## 補題 `SharedModelSignature.canonicalTCZAt_velocity_eq`

### 式

$$
\mathrm{TCZ}=\mathrm{ball}_{16}(h)\ (\text{全初期点・全開始時刻、閉包なし})
$$

### Lean のコメント（日本語訳）

> 正典TCZ＝ball16 h（全初期点・全開始時刻、閉包なし）。

### 補題の説明

正典の TCZ は `ball16 h` に等しいです（全初期点・全開始時刻、閉包なし）。

### 証明の概略

1. \(\subseteq\)：評価の閾値集合が担体（`layerOmega_eq`）。\(\supseteq\)：担体の各点 \(y\) は、\(\tau=t_0+|y-x|\) で到達する。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.canonicalTCZAt_eq_canonicalLayerTCZ"></a>

## 補題 `SharedModelSignature.canonicalTCZAt_eq_canonicalLayerTCZ`

### 式

$$
\text{一点 }x_0=\tfrac12\text{・開始時刻 }0\text{ の正典 TCZ}=\mathrm{canonicalLayerTCZ}
$$

### Lean のコメント（日本語訳）

> 一点x₀=1/2・開始時刻0の正典TCZはcanonicalLayerTCZと一致する。

### 補題の説明

一点 \(x_0=1/2\)・開始時刻 0 の正典 TCZ は、前のファイルの `canonicalLayerTCZ` と一致します。

### 証明の概略

1. 両方とも `ball16 h`。

----

<a id="Tomabechi.Consistency.R123.selected_flow_admissible_at"></a>

## 補題 `selected_flow_admissible_at`

### 式

$$
\varphi_{t-t_0}(y)=\text{許容入力による解}
$$

### Lean のコメント（日本語訳）

> 選択フィードバックの閉ループ軌道は、全開始時刻で許容入力による解。

### 補題の説明

選択フィードバックの閉ループの軌道は、**全開始時刻で、許容入力による解**です。

### 証明の概略

1. 前のファイルの `selected_flow_admissible` を、時刻をずらして適用する。入力を \(u(s-t_0)\) に取り替える。

----

<a id="Tomabechi.Consistency.R123.LayerControlSound"></a>

## 構造体 `LayerControlSound`

### 式

$$
\text{署名の表の健全性}
$$

### Lean のコメント（日本語訳）

> 署名の表の健全性：各(d,h,i)で、制御系・評価・正典TCZ・選択方策・24の系との違いを同じ署名で。

### 定義の説明

**署名の表の健全性**です。各 \((d,h,i)\) で、制御系・評価・正典 TCZ・選択方策・24 の系との違いを、同じ署名で述べます。フィールドは、16 の層の系は速度制御系（24 のゲイン系ではない）、正典 TCZ \(=\)`ball16 h`（全初期点・全非負開始時刻）、署名の TCZ が前のファイルの正典 TCZ に一致、評価は `N.data` の層の実走行費の閾値集合、中心は有限時刻で許容入力により到達、24 の有界ゲインの力学（共有核）は中心に届かない（生成系が別である理由）、選択フィードバックの閉ループの軌道は許容入力による解（全開始時刻）で、共有核の認知座標の動きと一致、です。

### 証明の概略

1. 定義です（証明はありません）。

----

<a id="Tomabechi.Consistency.R123.SharedModelSignature.layerControlSound"></a>

## 定理 `SharedModelSignature.layerControlSound`

### 式

$$
\mathrm{LayerControlSound}(N,\text{速度制御の署名})
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

保存式と追加条件のもとで、速度制御の署名の表が健全です。

### 証明の概略

1. 各フィールドは、上の補題と、前のファイルの定理（`canonicalLayerTCZ_eq`・`core_step_misses_center`・`selected_flow_admissible` など）。

----

<a id="Tomabechi.Consistency.R123.sharedModel_layerControlSound"></a>

## 定理 `sharedModel_layerControlSound`

### 式

$$
\mathrm{LayerControlSound}(\text{sharedModel},\ldots)
$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

具体的な共有モデルが、署名の表の健全性を満たします。

### 証明の概略

1. 前の定理を適用する。

----

<a id="Tomabechi.Consistency.R123.final_consistency_with_layer_control"></a>

## 定理 `final_consistency_with_layer_control`

### 式

$$
\exists N,\mathrm{sig},\ \mathrm{SharedFinalConsistency}(N)\wedge\mathrm{LayerControlSound}(N,\mathrm{sig})
$$

### Lean のコメント（日本語訳）

> 層別生成系を認める定式化での同時充足：最終統合（v11）に、署名の表を加えた存在宣言。

### 補題の説明

層別の生成系を認める定式化での**同時充足**です。最終の統合（第 11 版）に、署名の表を加えた存在宣言です。

### 証明の概略

1. `sharedModel`、速度制御の署名、最終統合の定理、署名の表の健全性。

----


## コメント修正記録

`.lean` のコメントの修正はありません。
