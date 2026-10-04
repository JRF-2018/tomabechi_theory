# Tomabechi/Examples/Theorem27_Operational.lean 解説

> 対象: [`Tomabechi/Examples/Theorem27_Operational.lean`](../Tomabechi/Examples/Theorem27_Operational.lean)（定理27の一般定理（操作的無明の同値）の輪モデルへの適用）。
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
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理27の一般定理（操作的無明の同値）を、2 次元の輪のモデルへ適用**するファイルです（`examples/theorem26_27_dynamic_quiescence.py`）。

状態 \(x=(r,\varphi)\in E_2=\mathbb R^2\)（ユークリッド）、制御 \(u\in E_2\)、アクチュエータ \(G=\mathrm{id}\)、自然ドリフト \(f_0(x)=(-\mu r,0)\)、指定方策 \(\pi^0(t,x)=u_0=(-\kappa r,\omega)\)（\(\mu=\kappa=\tfrac12\)、\(\omega=\tfrac32\)）、閉ループ \(\dot r=-r\)、\(\dot\varphi=3/2\)。基準入力 A：\(u_{\rm tr}=(\mu r,\omega)\)（**27-A2 を満たす**：\(F_{\rm tr}=f_0+u_{\rm tr}=(0,\omega)\) は \(W=r^2\) を変えない）。走行コスト \(3r^2\)、割引 \(\rho=1\)、空未満の層は走行コスト 1（`Theorem26_RingModel` と同じ値・目標）。

主結果 `operational_ignorance`：
- **(27.6)(27.10)**：無明（輪の外）⇔ Lyapunov 残差の下降率が正
- **(27.10)**：無明 ⇔ 行（実アクチュエータの正の寄与 \(-\langle\nabla W,G(u_0-u_{\rm tr})\rangle>0\)）（a.e.）
- **(27.8)**：無明のとき制御差のノルムは正

### 0.2 このファイルが証明していないこと

- **モデル化の注意（ファイルのコメントそのまま）**：`Feedback ⊤` は Borel Markov 全体と同値（`policyEquiv`）である必要があるが、任意のフィードバックの閉ループは解けないので、**許容方策を一点 \(\pi^0\) に制限**し（`admissible π := π=π0`）、軌道は \(\pi\) に依らず \(\pi^0\) の流れとします（無選択の特殊モデルの一般化）。基準入力 \(u_{\rm tr}\) は 27-A の定義どおり独立に固定する入力で、許容性は要求されません。
- したがって、**任意の Borel フィードバックへの拡張は未証明**です（今後の課題。トップの `README.md` を参照）。
- 特殊モデル（輪、無選択）への適用で、一般の定理27の代替ではありません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理27の一般定理（操作的無明の同値）の適用（`examples/theorem26_27_dynamic_quiescence.py`）
>
> 状態 \(x=(r,\varphi)\in E_2=\mathrm{EuclideanSpace}\ \mathbb R\ (\mathrm{Fin}\,2)\)、制御 \(u\in E_2\)、アクチュエータ \(G=\mathrm{id}\)、自然ドリフト \(f_0(x)=(-\mu r,0)\)、指定方策 \(\pi^0(t,x)=u_0=(-\kappa r,\omega)\)（\(\mu=\kappa=1/2\)、\(\omega=3/2\)）、閉ループ \(\dot r=-r\)、\(\dot\varphi=3/2\)。基準入力 A：\(u_{\rm tr}=(\mu r,\omega)\)（27-A2 を満たす：\(F_{\rm tr}=f_0+u_{\rm tr}=(0,\omega)\) は \(W=r^2\) を変えない）。走行コスト \(3r^2\)、割引 \(\rho=1\)、空未満の層は走行コスト 1（`Theorem26_RingModel` と同じ値・目標）。
>
> **モデル化の注意：** `Feedback ⊤` は Borel Markov 全体と同値（`policyEquiv`）である必要があるが、任意のフィードバックの閉ループは解けないので、許容方策を一点 \(\pi^0\) に制限し（`admissible π := π=π0`）、軌道は \(\pi\) に依らず \(\pi^0\) の流れとする（無選択の特殊モデルの一般化）。基準入力 `utr` は 27-A の定義どおり独立に固定する入力で、許容性は要求されない。

### 0.4 節見出しのコメント（日本語訳）

> ## 定理24/26 の共通データ（許容方策を \(\pi^0\) の一点に制限）
>
> ## 定理26 のダイナミクス
>
> ## 定理27の入力（27-A）
>
> ## 27-A の各前提

名前空間は `Tomabechi.Examples.Theorem27Op`（`open Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model MeasureTheory`）。

---

<a id="Tomabechi.Examples.Theorem27Op.E2"></a>

## 定義 `E2`

### 式

$$E_2=\mathbb R^2\ (\text{ユークリッド})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

状態と制御の空間（内積・完備性を持つ 2 次元ユークリッド空間）。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.e0"></a>

## 定義 `e0`

### 式

$$e_0=(1,0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

第 0 基底ベクトル（半径方向）。

### 証明の概略

1. `EuclideanSpace.single 0 1`。

----

<a id="Tomabechi.Examples.Theorem27Op.e1"></a>

## 定義 `e1`

### 式

$$e_1=(0,1)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

第 1 基底ベクトル（位相方向）。

### 証明の概略

1. `EuclideanSpace.single 1 1`。

----

<a id="Tomabechi.Examples.Theorem27Op.mu"></a>

## 定義 `mu`

### 式

$$\mu=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

自然ドリフトの強さ \(\mu\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.kap"></a>

## 定義 `kap`

### 式

$$\kappa=\tfrac12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

指定入力の半径方向の強さ \(\kappa\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.omg"></a>

## 定義 `omg`

### 式

$$\omega=\tfrac32$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

位相速度 \(\omega\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.e0_apply0"></a>

## 定理 `e0_apply0`

### 式

$$e_0(0)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

基底ベクトルの成分（計算補題）。

### 証明の概略

1. `simp [e0]`。

----

<a id="Tomabechi.Examples.Theorem27Op.e0_apply1"></a>

## 定理 `e0_apply1`

### 式

$$e_0(1)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同上。

### 証明の概略

1. `simp [e0]`。

----

<a id="Tomabechi.Examples.Theorem27Op.e1_apply0"></a>

## 定理 `e1_apply0`

### 式

$$e_1(0)=0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同上。

### 証明の概略

1. `simp [e1]`。

----

<a id="Tomabechi.Examples.Theorem27Op.e1_apply1"></a>

## 定理 `e1_apply1`

### 式

$$e_1(1)=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

同上。

### 証明の概略

1. `simp [e1]`。

----

<a id="Tomabechi.Examples.Theorem27Op.flowE"></a>

## 定義 `flowE`

### 式

$$x(s)=r_0e^{T-s}\,e_0+\bigl(\varphi_0+\omega(s-T)\bigr)\,e_1$$

### Lean のコメント（日本語訳）

> 閉ループの流れ \((re^{T-s},\varphi+\omega(s-T))\)。

### 定義の説明

閉ループ \(\dot r=-(\mu+\kappa)r=-r\)、\(\dot\varphi=\omega\) の解。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.flowE_0"></a>

## 定理 `flowE_0`

### 式

$$x(s)_0=r_0e^{T-s}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの第 0 成分。

### 証明の概略

1. `flowE` の定義と `e0_apply0`・`e1_apply0`。

----

<a id="Tomabechi.Examples.Theorem27Op.flowE_1"></a>

## 定理 `flowE_1`

### 式

$$x(s)_1=\varphi_0+\omega(s-T)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

流れの第 1 成分。

### 証明の概略

1. `flowE` の定義と `e0_apply1`・`e1_apply1`。

----

<a id="Tomabechi.Examples.Theorem27Op.value3"></a>

## 定義 `value3`

### 式

$$J^\ast(x,T)=r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

価値（位相に依らない）。

### 証明の概略

1. 定義：`value (x 0) T`。

----

<a id="Tomabechi.Examples.Theorem27Op.value3_eq"></a>

## 定理 `value3_eq`

### 式

$$J^\ast(x,T)=x_0^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`value_eq_sq` の 2 次元版。

### 証明の概略

1. `value_eq_sq`。

----

<a id="Tomabechi.Examples.Theorem27Op.ringE"></a>

## 定義 `ringE`

### 式

$$\mathcal N_\top(T)=\{x\mid J^\ast=0\}$$

### Lean のコメント（日本語訳）

> 零価値目標 \(\{r=0\}\)（輪）。

### 定義の説明

零価値の目標集合：輪。

### 証明の概略

1. 定義：`theorem26ZeroValueTarget Set.univ value3 T`。

----

<a id="Tomabechi.Examples.Theorem27Op.ringE_eq"></a>

## 定理 `ringE_eq`

### 式

$$\mathcal N_\top(T)=\{x\mid x_0=0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標が「\(r=0\)」であること。

### 証明の概略

1. `value3_eq` で \(r^2=0\iff r=0\)。

----

<a id="Tomabechi.Examples.Theorem27Op.ringE_closed"></a>

## 定理 `ringE_closed`

### 式

$$\mathcal N_\top\ \text{は閉}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

輪が閉集合。

### 証明の概略

1. `ringE_eq` と座標関数の連続性。

----

<a id="Tomabechi.Examples.Theorem27Op.infDist_ringE"></a>

## 定理 `infDist_ringE`

### 式

$$\mathrm{dist}(x,\mathcal N)=|r|$$

### Lean のコメント（日本語訳）

> \(\mathrm{dist}(x,\text{輪})=|r|\)（\(L^2\) 距離でも）。

### 補題の説明

ユークリッド距離でも、輪までの距離は \(|r|\)（最近点は位相が同じで \(r=0\) の点）。

### 証明の概略

1. 上から：輪の点 \(x-x_0e_0\)（第 0 成分が 0）までの距離が \(|x_0|\)（`Metric.infDist_le_dist_of_mem`、\(\|e_0\|=1\)）。
2. 下から：輪の任意の点 \(q\)（\(q_0=0\)）との距離は \(\ge|x_0-q_0|=|x_0|\)（`Metric.le_infDist`）。

----

<a id="Tomabechi.Examples.Theorem27Op.infDist_ringE_sq"></a>

## 定理 `infDist_ringE_sq`

### 式

$$\mathrm{dist}(x,\mathcal N)^2=r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上の二乗版。

### 証明の概略

1. `infDist_ringE` の二乗。

----

<a id="Tomabechi.Examples.Theorem27Op.RState"></a>

## 定義 `RState`

### 式

$$\text{false}\mapsto\text{Unit},\ \text{true}\mapsto E_2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの状態の型。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.RFeedback"></a>

## 定義 `RFeedback`

### 式

$$\text{false}\mapsto\text{PUnit},\ \text{true}\mapsto\Pi_{\ge0}(E_2,E_2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとのフィードバックの型。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.pi0Action"></a>

## 定義 `pi0Action`

### 式

$$\pi^0(t,x)=(-\kappa r)\,e_0+\omega\,e_1$$

### Lean のコメント（日本語訳）

> 指定方策 \(\pi^0(t,x)=u_0=(-\kappa r,\omega)\)。

### 定義の説明

**指定された方策**：半径方向に \(-\kappa r\)、位相方向に \(\omega\)。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopBorel"></a>

## インスタンス `rTopBorel`

### 式

$$\text{BorelSpace}([0,\infty)\times E_2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

時間と状態の積空間が Borel であることのインスタンス（ローカル）。

### 証明の概略

1. 積の `BorelSpace`。

----

<a id="Tomabechi.Examples.Theorem27Op.pi0"></a>

## 定義 `pi0`

### 式

$$\pi^0\in\Pi_{\ge0}(E_2,E_2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

指定方策を、非負時間の Borel マルコフ・フィードバックとして与える。

### 証明の概略

1. 作用は `pi0Action`、可測性は `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTraj"></a>

## 定義 `rTraj`

### 式

$$\text{false}:x,\quad\text{true}:\mathrm{flowE}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの軌道（上位は \(\pi\) に依らず `flowE`）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.rCost"></a>

## 定義 `rCost`

### 式

$$\text{false}:1,\quad\text{true}:3r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの走る費用。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.rOpt"></a>

## 定義 `rOpt`

### 式

$$\text{false}:J_{\rm low}(T),\quad\text{true}:r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適値。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.rPolicy"></a>

## 定義 `rPolicy`

### 式

$$\text{最適政策}=\pi^0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適政策（上位は \(\pi^0\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem27Op.rAdm"></a>

## 定義 `rAdm`

### 式

$$\mathrm{adm}(\pi)\iff\pi=\pi^0$$

### Lean のコメント（日本語訳）

> 許容方策は \(\pi^0\) のみ（無選択の特殊化）。

### 定義の説明

許容方策を指定方策 1 つに**制限**する定義です（ファイル冒頭の「モデル化の注意」）。

### 証明の概略

1. 場合分けで定義（上位は `π = pi0`）。

----

<a id="Tomabechi.Examples.Theorem27Op.cost_flowE"></a>

## 定理 `cost_flowE`

### 式

$$\ell(x(s)_0)=\ell(\mathrm{flow}(x_0,T,s))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

走る費用が半径成分だけで決まること。

### 証明の概略

1. `flowE_0`。

----

<a id="Tomabechi.Examples.Theorem27Op.top_lintegral"></a>

## 定理 `top_lintegral`

### 式

$$\mathrm{ofReal}(J^\ast(x,T))=\int^-\mathrm{ofReal}\bigl(w\cdot\ell(x(s)_0)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

価値の下積分表示。

### 証明の概略

1. `Theorem24_26_Model` の `source_top_lintegral_eq` に帰着（`cost_flowE`）。

----

<a id="Tomabechi.Examples.Theorem27Op.rData"></a>

## 定義 `rData`

### 式

$$\mathcal D=(\text{layers},\text{traj},\ell,\text{adm},V^*,\pi^*)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem24NonnegativeTimeData` の、このモデルでのインスタンス（許容方策を \(\pi^0\) に制限）。

### 証明の概略

1. 各フィールドを割り当てる（71 行の構成）。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopPseudo"></a>

## インスタンス `rTopPseudo`

### 式

$$d=\text{ユークリッド距離}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の擬距離（`E2` のもの）を `RState ⊤` に引き継ぐインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopNormed"></a>

## インスタンス `rTopNormed`

### 式

$$\text{ノルム}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層のノルム付き加法群のインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopInner"></a>

## インスタンス `rTopInner`

### 式

$$\text{内積}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の内積空間のインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopComplete"></a>

## インスタンス `rTopComplete`

### 式

$$\text{完備}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の完備性のインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopSMul"></a>

## インスタンス `rTopSMul`

### 式

$$\mathbb R\ \text{のスカラー倍が連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層でスカラー倍が連続であることのインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopMeas"></a>

## インスタンス `rTopMeas`

### 式

$$\text{可測空間}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の可測空間のインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.rTopBorelS"></a>

## インスタンス `rTopBorelS`

### 式

$$\text{BorelSpace}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層が Borel であることのインスタンス。

### 証明の概略

1. `inferInstanceAs`。

----

<a id="Tomabechi.Examples.Theorem27Op.W3"></a>

## 定義 `W3`

### 式

$$W(y,t)=y_0^2$$

### Lean のコメント（日本語訳）

> Lyapunov 関数を \(W(y)=r^2\) とする。

### 定義の説明

Lyapunov 関数（半径方向のズレの二乗）。

### 証明の概略

1. 定義：`lyapunov (y 0) t`。

----

<a id="Tomabechi.Examples.Theorem27Op.W3_along"></a>

## 定理 `W3_along`

### 式

$$W\bigl(\mathrm{flowE}(x,T,s),s\bigr)=W_{\rm along}(x_0,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道に沿った \(W\) が 1 次元モデルの `WAlong` に一致。

### 証明の概略

1. `funext` と `flowE_0`。

----

<a id="Tomabechi.Examples.Theorem27Op.target_eq"></a>

## 定理 `target_eq`

### 式

$$N_\top(\mathcal D)=\mathrm{ringE}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`rData` から作った零価値目標が `ringE` に一致。

### 証明の概略

1. 定義を展開し `rfl`。

----

<a id="Tomabechi.Examples.Theorem27Op.rDyn"></a>

## 定義 `rDyn`

### 式

$$\mathcal E=(W,\lambda,c_1,c_2,\text{target},\text{alive},\text{feedback})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem26NonnegativeTimeDynamics` の、このモデルでのインスタンス（制御空間は `E2`）。

### 証明の概略

1. `target_eq`・`ringE_closed`・`infDist_ringE_sq`・`W3_along` などをフィールドごとに割り当てる。

----

<a id="Tomabechi.Examples.Theorem27Op.driftE"></a>

## 定義 `driftE`

### 式

$$f_0(t)=-\mu\,r(t)\,e_0$$

### Lean のコメント（日本語訳）

> 自然ドリフト \(f_0=(-\mu r,0)\)（軌道上）。

### 定義の説明

軌道に沿った自然ドリフト。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.utrE"></a>

## 定義 `utrE`

### 式

$$u_{\rm tr}(t)=\mu\,r(t)\,e_0+\omega\,e_1$$

### Lean のコメント（日本語訳）

> 基準入力 A：\(u_{\rm tr}=(\mu r,\omega)\)（27-A2 を満たす）。

### 定義の説明

自然ドリフトを打ち消す基準入力。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.u0E"></a>

## 定義 `u0E`

### 式

$$u_0(t)=-\kappa\,r(t)\,e_0+\omega\,e_1$$

### Lean のコメント（日本語訳）

> 指定入力 \(u_0=(-\kappa r,\omega)\)。

### 定義の説明

軌道上での指定入力。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.gradWE"></a>

## 定義 `gradWE`

### 式

$$\nabla W=2r\,e_0$$

### Lean のコメント（日本語訳）

> 時刻 \(t\) の \(W\) の（状態部分の）勾配 \(2re_0\)。

### 定義の説明

\(W=r^2\) の勾配。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.dWE"></a>

## 定義 `dWE`

### 式

$$\mathrm dW(t)(a,z)=2r\,z_0$$

### Lean のコメント（日本語訳）

> 全微分 \(\mathrm dW_t(a,z)=2rz_0\)。

### 定義の説明

\(W\) の時間・状態についての全微分（時間成分は 0）。

### 証明の概略

1. 定義のみ（連続線形写像として構成）。

----

<a id="Tomabechi.Examples.Theorem27Op.dWE_apply"></a>

## 定理 `dWE_apply`

### 式

$$\mathrm dW(t)(a,z)=2\,r(t)\,z_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

全微分の値の公式。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Examples.Theorem27Op.GE"></a>

## 定義 `GE`

### 式

$$G=\mathrm{id}$$

### Lean のコメント（日本語訳）

> アクチュエータ \(G=\mathrm{id}\)。

### 定義の説明

入力がそのまま状態に作用する恒等写像。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem27Op.mu_add_kap"></a>

## 定理 `mu_add_kap`

### 式

$$\mu+\kappa=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(\mu+\kappa=1\)（閉ループの減衰率が 1 になる）。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem27Op.hasDerivAt_flowE"></a>

## 定理 `hasDerivAt_flowE`

### 式

$$\dot x(t)=f_0(t)+G\,u_0(t)$$

### Lean のコメント（日本語訳）

> 閉ループ軌道の微分：\(\dot r=-(\mu+\kappa)r=-r\)、\(\dot\varphi=\omega\)。

### 補題の説明

**軌道が閉ループ ODE（27-A の力学）を解く**こと：\(\dot x=f_0+Gu_0\)。

### 証明の概略

1. 半径成分：`flow_hasDerivAt`（\(\frac{d}{ds}r_0e^{T-s}=-r\)）、位相成分：\(\frac{d}{ds}(\varphi_0+\omega(s-T))=\omega\)。
2. `flowE` は \(r\,e_0+\varphi\,e_1\) の形なので、スカラー倍の微分（`HasDerivAt.smul_const`）で和をとる。
3. 右辺 \(f_0+Gu_0=(-\mu r-\kappa r,\omega)\) との一致を、成分ごとに \(\mu+\kappa=1\)（`mu`・`kap` の値）で確認（`ext`）。

----

<a id="Tomabechi.Examples.Theorem27Op.inner_gradWE"></a>

## 定理 `inner_gradWE`

### 式

$$\langle\nabla W,z\rangle=2\,r(t)\,z_0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

勾配との内積の公式。

### 証明の概略

1. `inner_vec` 型の計算（成分で内積を展開）。

----

<a id="Tomabechi.Examples.Theorem27Op.stateGrad"></a>

## 定理 `stateGrad`

### 式

$$\mathrm dW(t)(0,z)=\langle\nabla W,z\rangle$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**27-A の状態勾配の条件**：全微分の状態部分が勾配との内積で表せる。

### 証明の概略

1. `dWE_apply` と `inner_gradWE`。

----

<a id="Tomabechi.Examples.Theorem27Op.reference_cancellation"></a>

## 定理 `reference_cancellation`

### 式

$$\mathrm dW(t)(1,0)+\langle\nabla W,f_0+Gu_{\rm tr}\rangle=0$$

### Lean のコメント（日本語訳）

> 基準閉ループ \(F_{\rm tr}=f_0+Gu_{\rm tr}=(0,\omega)\) は \(W\) を変えない（27-A2）。

### 補題の説明

**27-A2（参照ループの相殺）の成立**：時間成分は 0、勾配との内積は \(2r\cdot(-\mu r+\mu r)=0\)。

### 証明の概略

1. `dWE_apply`（\(a=1,z=0\) で 0）と `inner_gradWE`、\(f_0+u_{\rm tr}=(0,\omega)\) の第 0 成分が 0。

----

<a id="Tomabechi.Examples.Theorem27Op.flowE_semigroup"></a>

## 定理 `flowE_semigroup`

### 式

$$\mathrm{flowE}\bigl(\mathrm{flowE}(y,a,s),s,t\bigr)=\mathrm{flowE}(y,a,t)$$

### Lean のコメント（日本語訳）

> 同じ \(x\) から出る別時刻の再始動の恒等式。

### 補題の説明

**再始動の恒等式**（定理27のアダプタが要求）。

### 証明の概略

1. 座標ごとに指数法則 \(e^{a-s}e^{s-t}=e^{a-t}\) と位相の加法性。

----

<a id="Tomabechi.Examples.Theorem27Op.u0E_eq_action"></a>

## 定理 `u0E_eq_action`

### 式

$$t\ge0\Rightarrow u_0(t)=\pi^0\bigl(t,x(t)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**実入力が指定方策の作用**であること（27-A の `hU0Feedback`）。

### 証明の概略

1. 定義の展開（\(r(t)=x(t)_0\) は `flowE_0`）。

----

<a id="Tomabechi.Examples.Theorem27Op.pzs_iff"></a>

## 定理 `pzs_iff`

### 式

$$t\ge0\Rightarrow\bigl(\mathrm{PZS}(y,t)\iff y\in\mathrm{ringE}(t)\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**PZS ⇔ 輪への所属**：永続的な苦ゼロは輪の上にいることと同値。

### 証明の概略

1. `theorem24_to26_from_nonnegativeTimeData`（Theorem24_26）に `rData`・`rDyn` を渡し、結論の PZS ⇔ 零価値目標の成分を取り出す。
2. 生存集合は全体（`rfl`）、零価値目標は `target_eq` で `ringE`。

----

<a id="Tomabechi.Examples.Theorem27Op.hasFDerivAt_W"></a>

## 定理 `hasFDerivAt_W`

### 式

$$W\ \text{は }(t,x(t))\ \text{で Fréchet 微分可能（微分}=\mathrm dW(t))$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**27-A の \(C^1\) 条件**：\(W(y,t)=y_0^2\) の合同 Fréchet 微分が `dWE`。

### 証明の概略

1. \(y\mapsto y_0\) は連続線形、二乗の微分（`HasFDerivAt.pow`）。

----

<a id="Tomabechi.Examples.Theorem27Op.locallyLipschitz_W"></a>

## 定理 `locallyLipschitz_W`

### 式

$$s\mapsto W(x(s),s)\ \text{は }[T,\infty)\text{ 上で局所 Lipschitz}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**27-A の局所 Lipschitz 条件**：軌道に沿った \(W\) が \(C^1\)（\(r_0^2e^{-2(s-T)}\)）なので局所 Lipschitz。

### 証明の概略

1. `W3_along` で `WAlong` に帰着し、`WAlong` は \(C^1\)（`hasDerivAt`）なので局所 Lipschitz。

----

<a id="Tomabechi.Examples.Theorem27Op.operational_ignorance"></a>

## 定理 `operational_ignorance`

### 式

$$\text{(27.6)(27.10) 無明}\iff\mathrm{Des}>0\ \wedge\ \text{(27.10) 無明}\iff\text{行の寄与}>0\ \ (\text{a.e.})\ \wedge\ \text{(27.8) 無明}\Rightarrow\|u_0-u_{\rm tr}\|>0$$

### Lean のコメント（日本語訳）

> 定理27（操作的無明の同値）をこの具体モデルに適用した結論。（定理の主張の中のコメント）(27.6)(27.10)：無明（輪の外）⇔ Lyapunov 残差の下降率が正。(27.10)：無明 ⇔ 行（実アクチュエータの正の寄与 \(-\langle\nabla W,G(u_0-u_{\rm tr})\rangle>0\)）。(27.8)：無明のとき制御差のノルムは正（下界 \(\lambda c_1\mathrm{dist}^2/L_{27}\)）。

### 補題の説明

**定理27の結論を輪のモデルで取り出した**もの：(27.6)(27.10) 無明（輪の外）⇔ 残差の下降率が正、(27.10) 無明 ⇔ 行（実アクチュエータの正の寄与）が正（a.e.）、(27.8) 無明のとき制御差のノルムが正。

### 証明の概略

1. 一般定理 `theorem24_26_data_to_theorem27_operational_ignorance_iff_descent_and_action_ae`（`Theorem24_26_27`）を直接呼ぶ（27A 版や `Theorem27PathActuatorData` は使わない）。
2. 距離・位相の同一性 `hMetric`・`hControlTopology` は `rfl`、データは `rData`・`rDyn`（生存集合は全体 `Set.univ`）。
3. 再始動は `flowE_semigroup`、ODE は `hasDerivAt_flowE`、状態勾配は `stateGrad`、参照相殺は `reference_cancellation`、局所 Lipschitz は `locallyLipschitz_W`、Fréchet 微分は `hasFDerivAt_W`、入力が方策の作用であることは `u0E_eq_action`。
4. 随伴の評価の定数は \(L_{27}=2|r_0|+1>0\) を取り、無明時の \(|\langle\nabla W,Gv\rangle|\le L_{27}\|v\|\) を示す。
5. PZS ⇔ 輪は `pzs_iff` で言い換えて、一般定理の 3 つの結論を取り出す。

----

<a id="Tomabechi.Examples.Theorem27Op.ignorance_gives_action"></a>

## 定理 `ignorance_gives_action`

### 式

$$x_0\ne0\Rightarrow\forall t,\ x(t)\notin\mathrm{ring}\ \wedge\ \text{a.e. 行の寄与}>0$$

### Lean のコメント（日本語訳）

> 非空虚性：\(r_0\ne0\)（無明の初期点）なら、全時刻で輪の外にあり、したがって行の寄与が正（a.e.）。

### 補題の説明

**結論が空虚でない**ことの確認：初期点が輪の外（\(r_0\ne0\)）なら、軌道は永久に輪の外にあるので、`operational_ignorance` の「無明」側が実際に起こり、行の寄与が正になります。

### 証明の概略

1. \(r(t)=r_0e^{T-t}\ne0\)（指数関数は 0 にならない）なので輪の外。
2. `operational_ignorance` の (27.10) の同値で、行の寄与が a.e. で正。

----


## コメント修正記録

（なし）
