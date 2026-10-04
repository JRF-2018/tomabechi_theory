# theorem1_example.lean 解説

> 対象: [`theorem1_example.lean`](../theorem1_example.lean)（定理1の線形の具体例（1次元・指数収束））。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| Lyapunov 関数 | 時間とともに単調に減る量。収束の証明に使う。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| フィードバック（方策） | 状態と時刻から制御値を決める規則 \(u=\pi(t,x)\)。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| Tendsto | 関数の極限を表す Lean の述語 `Filter.Tendsto`。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| `sorry` | 証明が未完であることを示す Lean の記号。本プロジェクトでは残さない方針。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

**定理1の線形の具体例**です（JRF 提供）。1 次元の状態 \(x\)、評価関数 \(V(x)=\tfrac12x^2\)、制御方策 \(\pi_c(x)=-\lambda x\)、軌道 \(x(t)=x_0e^{-\lambda t}\) で、TCZ（\(V\le\theta\) の集合）への距離が \(C\,e^{-\lambda t}\) で**指数的に減る**ことを、`sorry` なしで完全に証明します。定義が論文の記法（\(\pi_c\)・TCZ・dist）どおりに明示された、完成度の高いバージョンです。

### 0.2 構成

| 節 | 宣言 |
| --- | --- |
| 1. 基本定義 | `x_traj`, `V`, `pi_c`, `TCZ`, `ExponentiallyConvergesToTCZ` |
| 2. 解の検証 | `x_traj_is_sol`（\(\dot x=\pi_c(x)\)）, `x_traj_init`（\(x(0)=x_0\)） |
| 3. \(V\) の性質 | `V_pos_def`（正定値）, `V_exp_decay`（軌道に沿って指数減衰） |
| 4. 結論 | `convergence_to_TCZ`（TCZ への指数収束の完全証明） |

### 0.3 このファイルが証明していないこと（重要）

- これは**特殊な例**です。**一般の定理1**（任意の力学・任意の \(V\)）の証明ではありません。**線形の 1 次元系**（\(\dot x=-\lambda x\)）で、**軌道が明示的に解ける**ケースです。
- 有限ホライズンの最適制御から \(\pi_c\) が導かれる、ということは扱いません（\(\pi_c\) は最初から与える）。
- 一般の定理1（Lyapunov 関数の指数減衰から TCZ への距離の指数減衰）は `Theorem1.lean` にあります。この例が一般定理の仮定を満たすことは `Theorem1_Model.lean` で確認します。

### 0.4 ファイルのコメントについて

このファイルにはファイル冒頭のコメントはなく、各定義の前の通常コメント（`--`）が番号つきの見出しになっています。各項目の「Lean のコメント」にその日本語訳（もとから日本語）を示します。名前空間はなく、`open Real` だけです。

---

<a id="x_traj"></a>

## 定義 `x_traj`

### 式

$$x(t)=x_0\,e^{-\lambda t}$$

### Lean のコメント（日本語訳）

> 1. 基本定義
> 力学系：\(x\) の時間発展 \(x(t)=x_0\cdot\exp(-\lambda t)\)

### 定義の説明

初期値 \(x_0\) から出発し、指数的に原点へ近づく軌道です。

### 証明の概略

1. 定義：`x0 * Real.exp (-(lam * t))`。

----

<a id="V"></a>

## 定義 `V`

### 式

$$V(x)=\tfrac12x^2$$

### Lean のコメント（日本語訳）

> 評価関数 \(V(x)=0.5\cdot x^2\)

### 定義の説明

原点が最小の 2 次関数（谷）です。

### 証明の概略

1. 定義：`0.5 * x^2`。

----

<a id="pi_c"></a>

## 定義 `pi_c`

### 式

$$\pi_c(x)=-\lambda x$$

### Lean のコメント（日本語訳）

> 制御方策 \(\pi_c(t,x):=-\lambda x\)

### 定義の説明

原点へ向かう線形のフィードバック制御です。

### 証明の概略

1. 定義：`-(lam * x)`。

----

<a id="TCZ"></a>

## 定義 `TCZ`

### 式

$$\mathrm{TCZ}_\theta=\{x\mid V(x)\le\theta\}$$

### Lean のコメント（日本語訳）

> TCZ（Target Constraint Zone）：\(V(x)\le\theta\) を満たす集合

### 定義の説明

目標領域です。\(\theta\ge0\) なら原点を含みます。

### 証明の概略

1. 定義：`{x | V x ≤ theta}`。

----

<a id="ExponentiallyConvergesToTCZ"></a>

## 定義 `ExponentiallyConvergesToTCZ`

### 式

$$0<\lambda\ \wedge\ \exists C>0,\ \forall t\ge0,\ \operatorname{dist}(x(t),\mathrm{TCZ})\le C\,e^{-\lambda t}$$

### Lean のコメント（日本語訳）

> 定量的な収束（TCZ への距離の指数減衰）の定義

### 定義の説明

**速度つきの収束**の定義：TCZ への距離が \(C e^{-\lambda t}\) で抑えられます（`Filter.Tendsto` ではなく、定量的な形）。

### 証明の概略

1. 定義：命題。

----

<a id="x_traj_is_sol"></a>

## 補題 `x_traj_is_sol`

### 式

$$\dot x(t)=\pi_c(x(t))$$

### Lean のコメント（日本語訳）

> 2. \(\pi_c\) と `x_traj` の解の関係の代入による検証（\(\dot x=\pi_c(x)\) であることの証明）

### 補題の説明

`x_traj` が微分方程式 \(\dot x=-\lambda x\) の解であることの確認です。

### 証明の概略

1. `HasDerivAt` の指数関数と定数倍の微分（`Real.hasDerivAt_exp`、連鎖律）。

----

<a id="x_traj_init"></a>

## 補題 `x_traj_init`

### 式

$$x(0)=x_0$$

### Lean のコメント（日本語訳）

> 初期値の条件 \(x(0)=x_0\) の検証

### 補題の説明

\(t=0\) で \(x_0\) です。

### 証明の概略

1. `Real.exp_zero` で簡約。

----

<a id="V_pos_def"></a>

## 補題 `V_pos_def`

### 式

$$V(x)\ge0\ \wedge\ (V(x)=0\Leftrightarrow x=0)$$

### Lean のコメント（日本語訳）

> 3. \(V\) が条件に合うことを証明
> 条件1：\(V\) は正定値

### 補題の説明

\(V\) は正定値（原点でだけ 0）です。

### 証明の概略

1. \(\tfrac12x^2\ge0\)、\(=0\) ⇔ \(x=0\)（`nlinarith`／`sq_eq_zero_iff`）。

----

<a id="V_exp_decay"></a>

## 補題 `V_exp_decay`

### 式

$$V(x(t))=V(x_0)\,e^{-2\lambda t}$$

### Lean のコメント（日本語訳）

> 条件2：軌道に沿って \(V\) が指数的に減衰する

### 補題の説明

軌道に沿って \(V\) は速さ \(2\lambda\) で指数的に減ります（\(x^2\) なので指数が 2 倍）。

### 証明の概略

1. \((e^{-\lambda t})^2=e^{-2\lambda t}\)（`Real.exp_nat_mul`）と代数計算（`ring`）。

----

<a id="convergence_to_TCZ"></a>

## 定理 `convergence_to_TCZ`

### 式

$$\theta\ge0\ \Longrightarrow\ \operatorname{dist}(x(t),\mathrm{TCZ}_\theta)\le(|x_0|+1)\,e^{-\lambda t}\quad(t\ge0)$$

### Lean のコメント（日本語訳）

> 4. 具体例を代入した `convergence_to_TCZ` の完全証明
> （証明中のコメント：`h_upper` および `nlinarith` も \(-(\lambda t)\) に統一）

### 補題の説明

この例の主結論です。\(\theta\ge0\)（TCZ が原点を含む）のとき、軌道の TCZ への距離は \((|x_0|+1)e^{-\lambda t}\) で抑えられます（定数 \(C=|x_0|+1\)）。**\(\theta\) について一般**（\(\theta=0\) だけではない）です。

### 証明の概略

1. 原点は TCZ に属す（\(V(0)=0\le\theta\)）。
2. TCZ への距離 \(\le\) 原点までの距離 \(=|x_0|e^{-\lambda t}\)（`Metric.infDist_le_dist_of_mem`）。
3. \(|x_0|e^{-\lambda t}\le(|x_0|+1)e^{-\lambda t}\)（`nlinarith`）。

----


## コメント修正記録

（なし）
