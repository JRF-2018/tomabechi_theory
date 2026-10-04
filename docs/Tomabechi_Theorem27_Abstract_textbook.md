# Tomabechi/Theorem27/Abstract.lean 解説

> 対象: [`Tomabechi/Theorem27/Abstract.lean`](../Tomabechi/Theorem27/Abstract.lean)（定理27：型付き状態と無明分類の抽象核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 残差 \(\Phi\) | 目標からの「はみ出し量」。TCZ の中では 0、外では正（たとえば \([V_0-\theta]_+\)）。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 一切皆苦（定理24） | 空未満では評価を永久に零にできない、という構造的な非充足性。 |
| 涅槃寂静（定理26） | 最高抽象度で零残余苦の集合に所属した状態。静止ではなく動的な安定。 |
| 無明起行（定理27） | 寂静に未達のとき、実アクチュエータによる志向的な作用（行）が正になる、という数理。 |
| PZS | 「ある許容方策が \(V=0\) をほとんど至る所で永久に保つ」ことを表す命題。 |
| 最適残余価値 \(J^*\) | 割引無限地平の最適コスト \(\min\int e^{-\rho(t-T)}V\,dt\)。 |
| a.e.（ほとんど至る所） | 測度 0 の点（たとえば有限個）を除いてすべて、という意味。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| Markov 核 | 入力に応じて確率分布を返す写像（確率的な出力）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理27（無明起行：無明があると「行」（意図的な行為）が起こる）**の、**型つきの状態と「無明」の分類**に関する抽象的な核です。

- **操作的無明**（(27.1)）：「永続的な苦ゼロ（PZS）にできないこと」。型つきの状態と開始時刻で、PZS が**成り立たない**こと。
- **分類**（(27.2)）：最上位 \(\top\) より**下の抽象度**の状態は**すべて操作的無明**（定理24）。最上位では、無明 ⇔ **零残差の目標の外**にいること（定理26）。
- **残差 \(W\)**（Lyapunov 型）：目標の外では残差が**正**（(27.3)）、そこで残差が**下降する**（(27.6)(27.10)）。

### 0.2 構成

| 節 | 宣言 |
| --- | --- |
| 型つき状態と無明 | `TypedState27`, `pzsOnTypedState27`, `operationalIgnorance27`, `operationalIgnorance27_classification`, `theorem27_classification_of_condition24A`, `feedbackPZS_failure_iff_outside_theorem26_target` |
| 目標の外での残差の下降 | `residual_descent_of_outside_closed_target`, `outside_target_iff_positive_descent`, `ae_*` |
| 零残差の目標 | `zeroResidualTarget`, `isClosed_*`, `residual_eq_zero_*`, `residual_positive_iff_*` |
| (27.3)（最上位） | `positive_ignorance_residual_iff_operationalIgnorance27_top` |

### 0.3 このファイルが証明していないこと

- 定理24・26の同値（下位では PZS 不可、最上位では PZS ⇔ 目標）は、**継承した条件**として入力します（条件 24-A・26-A も同様）。
- 無明の思想的な解釈（仏教の「無明」）と、ここでの**操作的定義**（PZS の失敗）を同一視してはいけません。形式化されているのは数理的な述語だけです。
- 残差の下降の評価は、条件 26-A（距離との 2 次の比較・Lyapunov 減衰）の仮定のもとでの条件付きの結論です。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> 定理27の、型つきの状態と無明の分類に関する、抽象的な核。

名前空間は `Tomabechi.Theorem27`。`open _root_.Tomabechi.Theorem24_26`。

---

<a id="Tomabechi.Theorem27.TypedState27"></a>

## 定義 `TypedState27`

### 式

$$\text{TypedState}=\Bigl(\sum_{a<\top}\text{State}_a\Bigr)\ \sqcup\ \text{(alive 領域の状態)}$$

### Lean のコメント（日本語訳）

> (27.2) の、型つきの状態の領域：下位のすべての抽象度が、それぞれ自身の状態の型をもち、最上位は、生存する領域の状態の型に制限される。

### 定義の説明

状態を「どの抽象度の状態か」で型づけた直和です。\(\top\) 未満では各抽象度の状態、\(\top\) では生存する状態だけ。

### 証明の概略

1. 定義：`Sum`（`Σ a < ⊤, State a` と `alive`）。

----

<a id="Tomabechi.Theorem27.pzsOnTypedState27"></a>

## 定義 `pzsOnTypedState27`

### 式

$$\text{PZS}(s,T)=\begin{cases}\text{PZS}_a(x,T)&(s=(a,x),a<\top)\\\text{PZS}_\top(x,T)&(s\ \text{最上位})\end{cases}$$

### Lean のコメント（日本語訳）

> 型つきの直和の上の、永続的な零の苦の述語。\(\top\) より下では定理24から、最上位では定理26から継承される。

### 定義の説明

型つきの状態 \(s\) と時刻 \(T\) について、対応する抽象度の PZS を返す述語です。

### 証明の概略

1. 定義：直和の場合分け。

----

<a id="Tomabechi.Theorem27.operationalIgnorance27"></a>

## 定義 `operationalIgnorance27`

### 式

$$\text{Ign}(s,T):\equiv\neg\,\text{PZS}(s,T)$$

### Lean のコメント（日本語訳）

> 定義 (27.1)：操作的な無明は、型つきの状態と初期時刻での、永続的な零の苦の失敗である。

### 定義の説明

**操作的無明**：その状態から、永続的に苦ゼロにする方策が（その抽象度では）ない、ということ。

### 証明の概略

1. 定義：`¬ PZS s T`。

----

<a id="Tomabechi.Theorem27.operationalIgnorance27_classification"></a>

## 定理 `operationalIgnorance27_classification`

### 式

$$\text{下位の状態は全て無明}\ \wedge\ \text{最上位では無明}\Leftrightarrow x\notin N_{\text{top}}$$

### Lean のコメント（日本語訳）

> 分類 (27.2)：継承した定理24/26の同値を条件として、下位のすべての状態は操作的に無明であり、最上位では、無明は、零残差の目標からの除外と、ちょうど同値である。

### 補題の説明

**(27.2)**：\(\top\) より下の抽象度では、状態は必ず無明（苦ゼロにはなれない）。\(\top\) では、無明 ⇔ 寂静の集合 \(N_{\text{top}}\) の外。

### 証明の概略

1. `match s with` で下位／最上位に場合分け。下位は定理24（`¬PZS`）、最上位は定理26（PZS ⇔ 目標）から。

----

<a id="Tomabechi.Theorem27.theorem27_classification_of_condition24A"></a>

## 定理 `theorem27_classification_of_condition24A`

### 式

$$\text{24-A（全ての下位水準・初期の組）}\ \Longrightarrow\ (27.2)$$

### Lean のコメント（日本語訳）

> (27.2) を、すべての下位の水準と、すべての初期の組での、条件 24-A から、下位の抽象度の枝を導く形で述べる。最上位の PZS/目標の同値は、なお定理26が供給し、下位の方策・状態・将来の測度のモデルは、抽象度に依存してよい。

### 補題の説明

上の分類の、下位の枝を**条件 24-A から導く**版です（`theorem24_no_feedbackPZS_of_condition24A`）。

### 証明の概略

1. 下位の各水準で `theorem24_no_feedbackPZS_of_condition24A`、最上位は仮定された定理26の同値。`operationalIgnorance27_classification` を適用。

----

<a id="Tomabechi.Theorem27.feedbackPZS_failure_iff_outside_theorem26_target"></a>

## 定理 `feedbackPZS_failure_iff_outside_theorem26_target`

### 式

$$\forall t:\ \neg\,\text{FeedbackPZS}(x(t),t)\ \Longleftrightarrow\ x(t)\notin N_{\text{top}}(t)$$

### Lean のコメント（日本語訳）

> 式 (27.2) の最上位の枝を、軌道に沿って点ごとに、PZS と \(J^\*\) の実際のフィードバックの流れの定義から述べる。単一の Markov フィードバックを、すべての初期の組で使う。その再始動の整合性が、\((x(t),t)\) からのコストを、\(x\) の将来の区間と同一視する。

### 補題の説明

軌道 \(x(t)\) の各時刻で、「PZS でない」⇔「寂静の集合の外」。単一のフィードバックを使い続けるので、途中の時刻から見たコストが軌道の将来部分に一致する（再始動の整合性）という仮定を使います。

### 証明の概略

1. `feedbackPZS_iff_mem_theorem26ZeroValueTarget`（Theorem24_26）を、各時刻 \((x(t),t)\) に適用。

----

<a id="Tomabechi.Theorem27.residual_descent_of_outside_closed_target"></a>

## 補題 `residual_descent_of_outside_closed_target`

### 式

$$x\notin N\ (\text{閉・非空}),\ c_1d(x,N)^2\le W,\ \text{decay}\Rightarrow\ \text{decayRate}\cdot c_1\cdot d(x,N)^2\le\text{descentRate}\ \wedge\ \text{descentRate}>0$$

### Lean のコメント（日本語訳）

> Lyapunov の下側の評価と、厳密な減衰の仮定のもとで、空でない閉の零残差の集合の外の、すべての点は、厳密に正の残差の下降率をもち、その集合までの 2 乗距離で、定量的に下から抑えられる。これは、式 (27.6) の距離空間の形であり、条件 26-A の対応する仮定のもとでの、条件付きの結論である。

### 補題の説明

**(27.6)**：目標の外にいる限り、残差 \(W\) は**正の速さで下降**します（速さは距離の 2 乗に比例）。

### 証明の概略

1. 下降率 \(=\) decayRate × \(W\)（Lyapunov 減衰）、\(W\ge c_1d^2\)（下側の評価）から。目標が閉・非空なので \(d(x,N)>0\)（\(x\notin N\)）。

----

<a id="Tomabechi.Theorem27.outside_target_iff_positive_descent"></a>

## 補題 `outside_target_iff_positive_descent`

### 式

$$x\notin N\ \Longleftrightarrow\ \text{descentRate}>0$$

### Lean のコメント（日本語訳）

> (27.10) の最初の同値の、点ごとの形。逆の含意は、不変な目標の上での、零の下降の性質を使う。論文では、それは、前向きの不変性と、その目標の上での \(W=0\) から従う。

### 補題の説明

**目標の外 ⇔ 残差が正の速さで下降**（(27.10)）。

### 証明の概略

1. （→）上の補題。（←）目標上では下降率が 0（不変性と \(W=0\)）の対偶。

----

<a id="Tomabechi.Theorem27.ae_residual_descent_of_outside_closed_target"></a>

## 補題 `ae_residual_descent_of_outside_closed_target`

### 式

$$\forall^{\text{a.e.}}t:\ \text{decayRate}\,c_1\,d(x(t),N(t))^2\le\text{descentRate}(t)\ \wedge\ \text{descentRate}(t)>0\quad(x(t)\notin N(t))$$

### Lean のコメント（日本語訳）

> (27.6) の、ほとんど至るところの、時間に依存する形。零残差の目標は、時間とともに変わってよい。条件 26-A が、それぞれの関連する時刻での、閉性・非空性・距離の比較・Lyapunov の減衰を供給する。

### 補題の説明

時刻ごとに目標が変わる場合の、ほとんど至るところ版です。

### 証明の概略

1. 各時刻で `residual_descent_of_outside_closed_target`。

----

<a id="Tomabechi.Theorem27.ae_outside_target_iff_positive_descent"></a>

## 補題 `ae_outside_target_iff_positive_descent`

### 式

$$\forall^{\text{a.e.}}t:\ x(t)\notin N(t)\ \Longleftrightarrow\ \text{descentRate}(t)>0$$

### Lean のコメント（日本語訳）

> (27.10) の最初の同値の、ほとんど至るところの、時間に依存する形。逆の含意は、不変な目標の上での、零の下降を使う。

### 補題の説明

(27.10) の a.e. 版です。

### 証明の概略

1. `outside_target_iff_positive_descent` を a.e. の各時刻で。

----

<a id="Tomabechi.Theorem27.zeroResidualTarget"></a>

## 定義 `zeroResidualTarget`

### 式

$$N(t)=\{x\in\text{alive}\mid W(t,x)=0\}$$

### Lean のコメント（日本語訳）

> 定理27の論文で使う、零残差の目標：生存領域と、時間に依存する Lyapunov の残差の零集合の、共通部分。

### 定義の説明

残差 \(W\) が 0 の生存状態の集合です。

### 証明の概略

1. 定義：`{x ∈ alive | W (t, x) = 0}`。

----

<a id="Tomabechi.Theorem27.isClosed_zeroResidualTarget"></a>

## 補題 `isClosed_zeroResidualTarget`

### 式

$$\text{alive 閉},\ W(t,\cdot)\ \text{連続}\ \Longrightarrow\ N(t)\ \text{閉}$$

### Lean のコメント（日本語訳）

> 生存領域が閉で、残差が状態について連続なら、零残差の目標は閉である（26-A で使われる）。

### 補題の説明

閉集合と、連続関数の零点集合の共通部分は閉です。

### 証明の概略

1. `IsClosed.inter` と `isClosed_eq`（連続関数の零点）。

----

<a id="Tomabechi.Theorem27.residual_eq_zero_of_mem_zeroResidualTarget"></a>

## 補題 `residual_eq_zero_of_mem_zeroResidualTarget`

### 式

$$x\in N(t)\ \Longrightarrow\ W(t,x)=0$$

### Lean のコメント（日本語訳）

> 零残差の目標への所属は、零の Lyapunov 残差を伴う。

### 補題の説明

定義そのものです。

### 証明の概略

1. 定義の展開。

----

<a id="Tomabechi.Theorem27.residual_eq_zero_iff_mem_zeroResidualTarget"></a>

## 補題 `residual_eq_zero_iff_mem_zeroResidualTarget`

### 式

$$d(x,N)^2\le W\ \Longrightarrow\ \bigl(W=0\ \Longleftrightarrow\ x\in N\bigr)\quad(\text{alive 上})$$

### Lean のコメント（日本語訳）

> 生存領域の上で、26-A の下側の距離の評価が、零の Lyapunov 残差を、零残差の目標への所属と同値にする。

### 補題の説明

距離の下界 \(d^2\le W\) があれば、\(W=0\) なら \(d=0\)、目標が閉なので目標に属します。

### 証明の概略

1. \(W=0\Rightarrow d(x,N)=0\)、閉集合なので \(x\in N\)（`IsClosed.mem_iff_infDist_zero`）。

----

<a id="Tomabechi.Theorem27.residual_positive_iff_outside_zeroResidualTarget"></a>

## 補題 `residual_positive_iff_outside_zeroResidualTarget`

### 式

$$0<W\ \Longleftrightarrow\ x\notin N\quad(\text{alive 上})$$

### Lean のコメント（日本語訳）

> 生存する状態の上で、同じ評価と閉の目標は、操作的な無明を、残差の厳密な正値として特徴づける。

### 補題の説明

残差が正 ⇔ 目標の外（＝無明）です。

### 証明の概略

1. `W ≥ 0`（非負）と上の補題の対偶。

----

<a id="Tomabechi.Theorem27.residual_eq_zero_iff_mem_closed_target"></a>

## 補題 `residual_eq_zero_iff_mem_closed_target`

### 式

$$\text{(26.A) 両側の評価}\ \Longrightarrow\ \bigl(W=0\ \Longleftrightarrow\ x\in N\bigr)$$

### Lean のコメント（日本語訳）

> 完全な両側の距離の評価 (26.A) は、Lyapunov の残差の零集合を、閉の目標そのものによって特徴づける。これは、目標が (26.1) の零の最適値の集合として、独立に定義されるときに適用される。

### 補題の説明

目標が別に（零の最適値の集合として）定義されている場合の、残差の零集合の特徴づけです。

### 証明の概略

1. 下側の評価 \(c_1d^2\le W\) で \(W=0\Rightarrow x\in N\)、上側の評価 \(W\le c_2d^2\) で \(x\in N\Rightarrow W=0\)。

----

<a id="Tomabechi.Theorem27.residual_positive_iff_not_mem_closed_target"></a>

## 補題 `residual_positive_iff_not_mem_closed_target`

### 式

$$0<W\ \Longleftrightarrow\ x\notin N\quad(\text{両側評価・閉})$$

### Lean のコメント（日本語訳）

> 両側の条件 (26.A) と目標の閉性は、生存する状態の上で、正の Lyapunov の残差を、その目標の外にあることと同一視する。

### 補題の説明

正の残差 ⇔ 目標の外。

### 証明の概略

1. `residual_eq_zero_iff_mem_closed_target` と \(W\ge0\)。

----

<a id="Tomabechi.Theorem27.residual_eq_zero_on_theorem26_target"></a>

## 補題 `residual_eq_zero_on_theorem26_target`

### 式

$$x\in N_{\text{top}}(t)\ \Longrightarrow\ W(t,x)=0$$

### Lean のコメント（日本語訳）

> 26-A の距離のサンドイッチの両側が、(26.1) の \(N_{\text{top}}\) として使う、零の最適値の集合の上で、Lyapunov の残差を零にする。

### 補題の説明

\(N\) の上では \(d=0\) なので、\(0\le W\le c_2\cdot0=0\)。

### 証明の概略

1. 上側の評価 \(W\le c_2d^2=0\) と非負性。

----

<a id="Tomabechi.Theorem27.positive_ignorance_residual_iff_operationalIgnorance27_top"></a>

## 定理 `positive_ignorance_residual_iff_operationalIgnorance27_top`

### 式

$$0<W(t,x)\ \Longleftrightarrow\ \text{operationalIgnorance27}\ (x,t)\quad(\text{最上位・alive})$$

### Lean のコメント（日本語訳）

> 最も高い抽象度での式 (27.3)：生存領域の内側で、正の Lyapunov の無明の残差は、操作的な無明と同値である。定理26の PZS の特徴づけと、26-A の下側の距離の評価を仮定する。

### 補題の説明

**(27.3)**：最上位では、**残差が正 ⇔ 操作的無明**。無明を残差（連続な量）で測れる、ということです。

### 証明の概略

1. `residual_positive_iff_not_mem_closed_target`（残差 > 0 ⇔ 目標の外）と、定理26の分類（無明 ⇔ 目標の外）をつなぐ。

----


## コメント修正記録

（なし）
