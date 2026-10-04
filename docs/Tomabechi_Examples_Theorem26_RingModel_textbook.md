# Tomabechi/Examples/Theorem26_RingModel.lean 解説

> 対象: [`Tomabechi/Examples/Theorem26_RingModel.lean`](../Tomabechi/Examples/Theorem26_RingModel.lean)（定理26の2次元「輪」モデル（動的寂静）の Lean 根拠）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 空（くう）⊤ | 抽象度の束の最大元。最高抽象度。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| 割引率 \(\rho\) | 将来のコストを \(e^{-\rho t}\) で割り引く率。 |
| 擬距離空間 | 距離の性質をみたす空間（\(d(x,y)=0\) でも \(x\ne y\) を許す）。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 測度・可測 | 長さ・体積・確率を一般化したもの。「測れる」集合・関数。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理26の 2 次元「**輪**」モデル（`examples/theorem26_27_dynamic_quiescence.py` の 26-A）の Lean 根拠です。状態 \(p=(r,\varphi)\in\mathbb R\times\mathbb R\)（半径方向のズレ \(r\) と、輪の上の位相 \(\varphi\)）、閉ループ \(\dot r=-r\)、\(\dot\varphi=3/2\)（Python の \(u_0=(-\lambda r,\omega)\)、\(\lambda=1\)、\(\omega=3/2\)）。最高抽象度の走行コスト \(V_\top=3r^2\)（位相に依らない）、割引 \(\rho=1\)、空未満の層は走行コスト 1。制御空間は 1 点（`Theorem24_26_Model` と同じ**無選択の特殊モデル**）。

- 零残余苦価値集合 \(\mathcal N_\top=\{r=0\}\)（**輪**）、\(J^\ast(r,\varphi)=r^2\)、\(W=r^2\)（\(c_1=c_2=1\)、\(\lambda_W=2\)）、\(\omega(\rho)=\rho^2\)。
- 一般定理 `theorem24_to26_from_nonnegativeTimeData` を適用し、**26-A の全条件と結論**（PZS ⇔ 輪への所属、\(W\) の指数減衰、\(J^\ast\to0\)）を得ます。
- **動的寂静**：輪の上から出発すれば全時刻で輪の上に留まり（\(J^\ast=0\)）、位相は \(\varphi(t)=\varphi_0+\tfrac32(t-T)\) で**動き続けます**（\(\dot r=0\) でも静止しない）。

位相の座標がコストにも \(W\) にも入らないので、距離は sup 距離で \(\mathrm{dist}(p,\mathcal N)=|r|\)。

### 0.2 このファイルが証明していないこと

- **無選択の特殊モデル**です（制御空間が 1 点で、最適性は自明）。任意の Borel フィードバックへの拡張は課題 9 です。
- 定理27（無明起行）の結論は `Theorem27_Operational.lean` が扱います（このファイルは定理26まで）。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理26の 2 次元「輪」モデル（`examples/theorem26_27_dynamic_quiescence.py` の 26-A）
>
> 状態 \(p=(r,\varphi)\in\mathbb R\times\mathbb R\)（半径方向のズレ \(r\) と輪上の位相 \(\varphi\)）、閉ループ \(\dot r=-r\)、\(\dot\varphi=3/2\)（Python の \(u_0=(-\lambda r,\omega)\)、\(\lambda=1\)、\(\omega=3/2\)）。最高抽象度の走行コスト \(V_\top=3r^2\)（位相に依らない）、割引 \(\rho=1\)、空未満の層は走行コスト 1。制御空間は単点（`Theorem24_26_Model` と同じ無選択の特殊モデル）。
>
> * 零残余苦価値集合 \(\mathcal N_\top=\{r=0\}\)（輪）、\(J^\ast(r,\varphi)=r^2\)、\(W=r^2\)（\(c_1=c_2=1\)、\(\lambda_W=2\)）、\(\omega(\rho)=\rho^2\)。
> * 一般定理 `theorem24_to26_from_nonnegativeTimeData` を適用し、26-A の全条件と結論（PZS ⇔ 輪への所属、\(W\) の指数減衰、\(J^\ast\to0\)）を得る。
> * 動的寂静：輪の上から出発すれば全時刻で輪の上に留まり（\(J^\ast=0\)）、位相は \(\varphi(t)=\varphi_0+(3/2)(t-T)\) で動き続ける（\(\dot r=0\) でも静止しない）。
>
> 位相座標がコストにも \(W\) にも入らないので、距離は sup 距離で \(\mathrm{dist}(p,\mathcal N)=|r|\)。

### 0.4 節見出しのコメント（日本語訳）

> ## 定理24/26 の共通データ
>
> ## 定理26 のダイナミクス（輪への指数収束）
>
> ## 定理26の結論（動的寂静）

名前空間は `Tomabechi.Examples.Theorem26Ring`（`open Tomabechi.Theorem24_26 Tomabechi.Theorem24_26_Model MeasureTheory`）。

---

<a id="Tomabechi.Examples.Theorem26Ring.omg"></a>

## 定義 `omg`

### 式

$$\omega=\tfrac32$$

### Lean のコメント（日本語訳）

> 位相速度 \(\omega=3/2\)。

### 定義の説明

輪の上を回る**位相の速さ**です。

### 証明の概略

1. 定義のみ。

----

<a id="Tomabechi.Examples.Theorem26Ring.flow2"></a>

## 定義 `flow2`

### 式

$$r(s)=r_0e^{T-s},\quad\varphi(s)=\varphi_0+\omega(s-T)$$

### Lean のコメント（日本語訳）

> 閉ループの流れ \(r(s)=r_0e^{T-s}\)、\(\varphi(s)=\varphi_0+\omega(s-T)\)。

### 定義の説明

半径方向は指数減衰、位相は一定速度で回転。

### 証明の概略

1. 定義：`(flow p.1 T s, p.2 + omg * (s - T))`（`flow` は `Theorem24_26_Model.flow`）。

----

<a id="Tomabechi.Examples.Theorem26Ring.value2"></a>

## 定義 `value2`

### 式

$$J^\ast(r,\varphi)=r^2$$

### Lean のコメント（日本語訳）

> 価値 \(J^\ast(r,\varphi)=r^2\)（位相に依らない）。

### 定義の説明

最適値は半径方向のズレの二乗。

### 証明の概略

1. 定義：`value p.1 T`。

----

<a id="Tomabechi.Examples.Theorem26Ring.value2_eq"></a>

## 定理 `value2_eq`

### 式

$$J^\ast(p,T)=r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`Theorem24_26_Model.value_eq_sq` の 2 次元版。

### 証明の概略

1. `value_eq_sq p.1 T`。

----

<a id="Tomabechi.Examples.Theorem26Ring.ring"></a>

## 定義 `ring`

### 式

$$\mathcal N_\top(T)=\{p\mid J^\ast(p,T)=0\}$$

### Lean のコメント（日本語訳）

> 零価値目標 \(\{r=0\}\)（輪）。

### 定義の説明

零価値の目標集合：輪（\(r=0\)）。

### 証明の概略

1. 定義：`theorem26ZeroValueTarget Set.univ value2 T`。

----

<a id="Tomabechi.Examples.Theorem26Ring.ring_eq"></a>

## 定理 `ring_eq`

### 式

$$\mathcal N_\top(T)=\{p\mid r=0\}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

目標集合が「\(r=0\)（輪）」であること。

### 証明の概略

1. `value2_eq` で \(r^2=0\iff r=0\)。

----

<a id="Tomabechi.Examples.Theorem26Ring.ring_closed"></a>

## 定理 `ring_closed`

### 式

$$\mathcal N_\top\ \text{は閉}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

輪が閉集合。

### 証明の概略

1. `ring_eq` と、\(r=0\) が連続関数の零点集合であること。

----

<a id="Tomabechi.Examples.Theorem26Ring.infDist_ring"></a>

## 定理 `infDist_ring`

### 式

$$\mathrm{dist}(p,\mathcal N)=|r|$$

### Lean のコメント（日本語訳）

> \(\mathrm{dist}(p,\text{輪})=|r|\)（sup 距離）。

### 補題の説明

輪までの距離は半径方向のズレの絶対値（位相は動かせるので距離に寄与しない）。

### 証明の概略

1. 輪の点 \((0,\varphi)\) への距離は \(\max(|r|,|\varphi-\varphi'|)\) で、\(\varphi'=\varphi\) とすれば \(|r|\)。これが最小。

----

<a id="Tomabechi.Examples.Theorem26Ring.infDist_ring_sq"></a>

## 定理 `infDist_ring_sq`

### 式

$$\mathrm{dist}(p,\mathcal N)^2=r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

上の二乗版。

### 証明の概略

1. `infDist_ring` の両辺を二乗（`sq_abs`）。

----

<a id="Tomabechi.Examples.Theorem26Ring.RState"></a>

## 定義 `RState`

### 式

$$\text{false}\mapsto\text{Unit},\ \text{true}\mapsto\mathbb R\times\mathbb R$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの状態の型（下位は 1 点、上位は \(\mathbb R^2\)）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.RFeedback"></a>

## 定義 `RFeedback`

### 式

$$\text{false}\mapsto\text{PUnit},\ \text{true}\mapsto\Pi_{\ge0}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとのフィードバックの型。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.feedback0"></a>

## 定義 `feedback0`

### 式

$$\pi^0\equiv\ast$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

唯一のフィードバック（制御空間が 1 点）。

### 証明の概略

1. 定数写像。

----

<a id="Tomabechi.Examples.Theorem26Ring.rTrajectory"></a>

## 定義 `rTrajectory`

### 式

$$\text{false}:x,\quad\text{true}:\mathrm{flow2}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの軌道。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.rRunningCost"></a>

## 定義 `rRunningCost`

### 式

$$\text{false}:1,\quad\text{true}:3r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの走る費用。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.rOptimalValue"></a>

## 定義 `rOptimalValue`

### 式

$$\text{false}:J_{\rm low}(T),\quad\text{true}:r^2$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適値。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.rOptimalPolicy"></a>

## 定義 `rOptimalPolicy`

### 式

$$\text{最適政策（唯一）}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの最適政策。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.rAdmissible"></a>

## 定義 `rAdmissible`

### 式

$$\text{すべて許容}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

層ごとの許容性（常に True）。

### 証明の概略

1. 場合分けで定義。

----

<a id="Tomabechi.Examples.Theorem26Ring.top_lintegral_eq"></a>

## 定理 `top_lintegral_eq`

### 式

$$\mathrm{ofReal}(J^\ast(p,T))=\int^-\mathrm{ofReal}\bigl(w\cdot3r(s)^2\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

価値の下積分表示（`Theorem24NonnegativeTimeData` が要求する形）。

### 証明の概略

1. `Theorem24_26_Model` の `source_top_lintegral_eq` の第 1 成分への帰着。

----

<a id="Tomabechi.Examples.Theorem26Ring.rData"></a>

## 定義 `rData`

### 式

$$\mathcal D=(\text{layers},\text{traj},\ell,\text{adm},V^*,\pi^*)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem24NonnegativeTimeData` の、輪モデルでのインスタンス（54 行の構成）。

### 証明の概略

1. 各フィールドを割り当て、条件を `top_lintegral_eq`・`Theorem24_26_Model` の補題で証明。

----

<a id="Tomabechi.Examples.Theorem26Ring.rTopPseudoMetric"></a>

## インスタンス `rTopPseudoMetric`

### 式

$$d=\text{sup 距離}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の状態空間 \(\mathbb R\times\mathbb R\) の擬距離（sup 距離）のインスタンス（ローカル）。

### 証明の概略

1. 積空間の距離を再利用。

----

<a id="Tomabechi.Examples.Theorem26Ring.rTopMeasurableSpace"></a>

## インスタンス `rTopMeasurableSpace`

### 式

$$\text{Borel}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上位層の可測空間のインスタンス。

### 証明の概略

1. 積の Borel を再利用。

----

<a id="Tomabechi.Examples.Theorem26Ring.rTopBorelSpace"></a>

## インスタンス `rTopBorelSpace`

### 式

$$\text{BorelSpace}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

可測構造が Borel であることのインスタンス。

### 証明の概略

1. `Prod.borelSpace`。

----

<a id="Tomabechi.Examples.Theorem26Ring.rTopProductBorelSpace"></a>

## インスタンス `rTopProductBorelSpace`

### 式

$$\text{BorelSpace}([0,\infty)\times\mathbb R^2)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

時間と状態の積空間が Borel であることのインスタンス。

### 証明の概略

1. 積の `BorelSpace`。

----

<a id="Tomabechi.Examples.Theorem26Ring.W2"></a>

## 定義 `W2`

### 式

$$W(r,\varphi,t)=r^2$$

### Lean のコメント（日本語訳）

> Lyapunov 関数を \(W(r,\varphi)=r^2\) とする。

### 定義の説明

Lyapunov 関数（半径方向のズレの二乗）。

### 証明の概略

1. 定義：`lyapunov p.1 t`。

----

<a id="Tomabechi.Examples.Theorem26Ring.W2_along"></a>

## 定理 `W2_along`

### 式

$$W\bigl(\mathrm{flow2}(x,T,s),s\bigr)=W_{\rm along}(x_0,T,s)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

軌道に沿った \(W\) が、1 次元モデルの `WAlong` に一致。

### 証明の概略

1. `rfl`。

----

<a id="Tomabechi.Examples.Theorem26Ring.target_eq"></a>

## 定理 `target_eq`

### 式

$$N_\top(\mathcal D)=\mathrm{ring}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`rData` から定理26の定義で作った零価値目標が `ring` に一致。

### 証明の概略

1. 定義を展開し、`rOptimalValue` の上位層が `value2` であることで `rfl`。

----

<a id="Tomabechi.Examples.Theorem26Ring.rDynamics"></a>

## 定義 `rDynamics`

### 式

$$\mathcal E=(W,\lambda,c_1,c_2,\text{target},\text{alive},\text{feedback})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一般の `Theorem26NonnegativeTimeDynamics` の、輪モデルでのインスタンス（84 行の構成）。\(W=r^2\)、\(\lambda=2\)、\(c_1=c_2=1\)、目標 = 輪、alive は全体。

### 証明の概略

1. `target_eq`・`ring_closed`・`infDist_ring_sq`・`W2_along`・`Theorem24_26_Model.WAlong_hasDerivAt` などをフィールドごとに割り当てる。

----

<a id="Tomabechi.Examples.Theorem26Ring.ring_theorem26"></a>

## 定理 `ring_theorem26`

### 式

$$\text{(i) 下位で零苦不能 (ii) PZS}\iff x\in\mathrm{ring}\ \ \text{(iii) 指数減衰}\ \ \text{(iv) }J^\ast\to0$$

### Lean のコメント（日本語訳）

> （定理の主張の中のコメント）空未満の層では零苦不能（\(J^\ast_a>0\)、PZS 不成立）。最高抽象度：PZS ⇔ 輪への所属。(26.2)：\(W\) と輪への距離の指数減衰。\(J^\ast\to0\)。

### 補題の説明

**輪モデルでの定理26の全結論**です：(i) 空未満の層では \(J^\ast_a>0\)（PZS 不成立）、(ii) 最高抽象度では PZS ⇔ 輪への所属、(iii) \(W\) と輪への距離の指数減衰、(iv) \(J^\ast\to0\)。

### 証明の概略

1. 一般定理 `theorem24_to26_from_nonnegativeTimeData` に `rData`・`rDynamics` を渡し、結論の 6 成分を取り出す。
2. 下位層の零苦不能は第 1 成分、PZS ⇔ 目標は第 2 成分（生存集合は全体、目標は `target_eq` で `ring`）。
3. 指数減衰は第 3 成分の \(W=r^2\) と距離の評価（\(\sqrt{r^2}=|r|\)、`Real.sqrt_sq_eq_abs`）に書き換え、\(J^\ast\to0\) は第 4 成分（30 行）。

----

<a id="Tomabechi.Examples.Theorem26Ring.dynamic_quiescence"></a>

## 定理 `dynamic_quiescence`

### 式

$$x\in\mathrm{ring}(T)\Rightarrow\forall s\ge T,\ \mathrm{flow2}(x,T,s)\in\mathrm{ring}(s)\ \wedge\ J^\ast=0\ \wedge\ \varphi(s)=\varphi_0+\tfrac32(s-T)$$

### Lean のコメント（日本語訳）

> 動的寂静：輪の上から出発すれば、全時刻で輪の上（\(J^\ast=0\)）に留まり、位相は動き続ける。

### 補題の説明

**動的寂静**：苦が 0 のまま（輪の上）、位相は一定速度で回り続けます。

### 証明の概略

1. \(r_0=0\) なら \(r(s)=0\)（`flow` の定義）で輪の上、\(J^\ast=r^2=0\)。
2. 位相は `flow2` の定義どおり \(\varphi_0+\frac32(s-T)\)。

----

<a id="Tomabechi.Examples.Theorem26Ring.phase_keeps_moving"></a>

## 定理 `phase_keeps_moving`

### 式

$$T<s\Rightarrow\varphi(s)\ne\varphi(T)$$

### Lean のコメント（日本語訳）

> 位相は静止しない：輪の上でも異なる時刻で状態は異なる（\(\varphi(s)\ne\varphi(T)\)）。

### 補題の説明

**寂静でも運動は止まらない**：\(\omega>0\) なので位相は時間とともに変化します。

### 証明の概略

1. \(\varphi(s)-\varphi(T)=\frac32(s-T)>0\)。

----


## コメント修正記録

（なし）
