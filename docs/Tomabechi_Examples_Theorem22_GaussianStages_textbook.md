# Tomabechi/Examples/Theorem22_GaussianStages.lean 解説

> 対象: [`Tomabechi/Examples/Theorem22_GaussianStages.lean`](../Tomabechi/Examples/Theorem22_GaussianStages.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| コンパクト | 無限個の点列が必ず収束部分列をもつような「閉じた有界」な空間。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
| Mathlib | Lean の数学ライブラリ。 |
| Euler 法 | 微分方程式 \(\dot x=F(x)\) を、小さな刻み \(h\) で \(x_{k+1}=x_k+hF(x_k)\) と更新して近似する数値解法。このプロジェクトの Python 例が使う。Lean が証明するのは刻み 0 の極限（連続時間）の側。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理22（LUB の階段と段階切替）の Python 例 `examples/theorem22_lub_staircase.py` は、抽象度の段が上がるたびに目標の中心を動かし、各段で**ガウス型の谷**に沿って状態を流す、という数値例です。この `.lean` は、その**有限ガウスモデル**を、実際に**切替軌道（段ごとの ODE 解を時間順につないだ連続な軌道）**として構成し、定理22の段階条件を満たすことを証明します。

設定（Python と同じ）：谷は \(W(x)=-2\exp\!\bigl(-(x-c)^2/(2\sigma^2)\bigr)\)（\(\sigma=3/2\)）、勾配流 \(\dot x=-W'(x)\)。各段の長さは 12 秒、局所強凸の半径は \(5/4\)（この球の中では曲率 \(W''\ge1/8\)）。中心列は

- **ケース A**：\(1,2,3,4,4,4,\dots\)（1 ずつ動いて、以後 4 に固定）。
- **ケース C**：\(1,1,2,2,2,\dots\)（中心が動かない切替も含む）。
- **ケース B**：中心 6 の谷だけを見る（初期値 0 は半径 \(5/4\) の局所球の外）。

証明の流れは次のとおりです。

1. **段の仕様**：半径 \(5/4\)・曲率下界 \(1/8\) の局所ガウス谷を、一般の段仕様 `StageValleySpec` に接続する（`gaussianStage`）。そのために、ガウス谷の曲率評価（`ddwell_lower_on_quarter_ball`）、エネルギー評価（`gaussian_dwell_energy_lower`）、部分準位が距離の球になること（`gaussian_well_le_iff_abs_le`）を示す。
2. **段内の挙動**：段内の ODE 解は部分準位の中で一意で（`gaussianStage_orbit_unique`）、中心からの二乗距離は単調に減り、重み付き二乗距離 \(e^{T}(x-c)^2\) は増えない（`…_weighted_square_nonincreasing`）。したがって距離は \(|x_0-c|\,e^{-T/2}\) で減衰する（`gaussianStage_distance_decay`、(22.4) に当たる指数評価、率 \(1/2\)）。
3. **12 秒後の誤差**：初期誤差が \(9/8\) 以下なら、12 秒後の誤差は \(1/8\) 以下（`gaussianStage_endpoint_error_12`）。(22.5) の待ち時間条件 \(2\log9\le12\) もスカラー版で確認する（`gaussian_python_wait_12`、`runs_actual_endpoint_error_via_22_5`）。
4. **段のつなぎ**：中心移動が 1 以下なら、前段の終点（誤差 \(\le1/8\)）は次段の局所球（半径 \(5/4\)）の中に入る（\(1/8+1=9/8<5/4\)）ので、次の段の初期値として使える。段を再帰的に作る `gaussianStageRuns`、時刻の漸化式 \(t_{n+1}=t_n+12\)、接合軌道 `runsTrajectory`（`stitchedStageOrbit`）を構成し、各段内で段の ODE を満たし連続につながることを証明する（`runs_stage_agreement`）。
5. **ケース A・C**：具体的な中心列について、すべての段で 12 秒後の誤差が \(1/8\) 以内（`caseA_actual_stage_endpoint`、`caseC_actual_stage_endpoint`）。
6. **ケース B**：初期値 0 から中心 6 へ向かう大域解が存在し、有限時間で中心に到達せず、\([0,1]\) では速度が \(1/24\) 以下なので、12 秒後も中心 6 から距離 5 より遠く（\(x(12)<1\)）、次の段の中心 8 の局所球（半径 \(5/4\)）の**外**にある（`exists_caseB_actual_switch_outside_next_ball`）。局所強凸の谷に入っていないので、次の段の評価は適用できない、という「条件が破れる場合の例」。

### 0.2 このファイルが証明していないこと

- **Python の Euler 離散列と数値出力は証明の対象外**です。証明したのは連続時間の ODE 解の接合軌道です。
- **有限ガウスの具体モデル**（指定した \(A=2\)、\(\sigma=3/2\)、半径 \(5/4\)、段の長さ 12、中心列 A/C）での結果で、一般の段階条件から任意のモデルを導くものではありません。一般の `StageValleySpec` の側は別ファイル（`Theorem22.lean`、`Dynamics/StageSwitching.lean`）です。
- ケース B は「局所谷の条件が破れた場合に、次の段の評価が使えない」ことの例であって、原文の定理22の反例ではありません。
- 23-B の一般核への接続（切替軌道から平均場表示を作るなど）は含みません。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理22の有限ガウス階段：実軌道
>
> Python の A/C の中心列を保ち、半径 5/4 の局所ガウス谷を `StageValleySpec` に接続する。

### 0.4 節見出しのコメント（日本語訳）

> 実軌道の局所評価

名前空間は `Tomabechi.Examples.Theorem22GaussianStages`（`open Tomabechi.Theorem22`、`Theorem23`、`Theorem21`、`Tomabechi.Examples.Gaussian`、`Filter`、`Topology`）。ガウス谷の関数 `well`・`dwell`・`ddwell`（\(W,\ W',\ W''\)）は `Tomabechi.Examples.Gaussian` で定義されています：
$$W(x)=-A\,e^{-(x-c)^2/(2\sigma^2)},\quad W'(x)=\tfrac{A(x-c)}{\sigma^2}e^{-(x-c)^2/(2\sigma^2)},\quad W''(x)=\tfrac{A}{\sigma^2}\Bigl(1-\tfrac{(x-c)^2}{\sigma^2}\Bigr)e^{-(x-c)^2/(2\sigma^2)}.$$
ここでは \(A=2\)、\(\sigma=3/2\)（\(A/\sigma^2=8/9\)）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.ddwell_lower_on_quarter_ball"></a>

## 補題 `ddwell_lower_on_quarter_ball`

### 式

$$|x-c|\le\tfrac54\ \Rightarrow\ W''(x)\ge\tfrac18$$

### Lean のコメント（日本語訳）

> 半径 5/4 の局所球では、ガウス谷の曲率は一様に 1/8 以上。

### 補題の説明

谷の底（中心 \(c\)）から \(5/4\) 以内では、谷が**強凸**（曲率が下から一様に正）です。段階の一般条件が要求する「局所強凸」の定数 \(1/8\) がこれで決まります。

### 証明の概略

1. \(W''=\frac89\bigl(1-\frac{(x-c)^2}{9/4}\bigr)e^{-(x-c)^2/(9/2)}\)。
2. \((x-c)^2\le25/16\) より、第 1 因子 \(\ge1-\frac{25/16}{9/4}=\frac{11}{36}\)。
3. 指数部は \(\le\frac{25}{72}\) なので \(e^{-(\cdot)}\ge1-\frac{25}{72}=\frac{47}{72}\)（\(e^y\ge1+y\)）。
4. \(\frac89\cdot\frac{11}{36}\cdot\frac{47}{72}\ge\frac18\)（数値計算）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussian_dwell_energy_lower"></a>

## 補題 `gaussian_dwell_energy_lower`

### 式

$$|x-c|\le\tfrac54\ \Rightarrow\ (x-c)\,W'(x)\ge\tfrac12(x-c)^2$$

### Lean のコメント（日本語訳）

> ガウス勾配は半径 5/4 内で、中心からのずれに少なくとも 1/2 の線形係数を持つ。

### 補題の説明

谷の中では勾配が中心に向かって十分強い、という評価です。これで二乗距離 \((x-c)^2\) の減少率が決まります。

### 証明の概略

1. \(W'(x)=\frac89(x-c)e^{-(\cdot)}\)、指数部 \(\le25/72\)、\(e^{-(\cdot)}\ge47/72\)。
2. 係数 \(\frac89e^{-(\cdot)}\ge\frac89\cdot\frac{47}{72}\ge\frac12\)。
3. \((x-c)W'=\frac89(x-c)^2e^{-(\cdot)}\ge\frac12(x-c)^2\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussian_well_le_iff_abs_le"></a>

## 補題 `gaussian_well_le_iff_abs_le`

### 式

$$W(x)\le W(x_0)\iff|x-c|\le|x_0-c|$$

### Lean のコメント（日本語訳）

> ガウス谷のエネルギー部分準位は中心からの距離で記述できる。

### 補題の説明

ガウス谷 \(W\) の部分準位集合 \(\{W\le W(x_0)\}\) は、中心 \(c\) からの距離が \(|x_0-c|\) 以下の閉区間です（ガウス関数が中心からの距離について単調なので）。段の「初期部分準位」を閉球で表すために使います。

### 証明の概略

1. \(W(x)\le W(x_0)\iff e^{-(x_0-c)^2/(9/2)}\le e^{-(x-c)^2/(9/2)}\)（\(-A<0\)）。
2. 指数関数の単調性で \((x-c)^2\le(x_0-c)^2\)。
3. これは \(|x-c|\le|x_0-c|\)（`sq_le_sq`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage"></a>

## 定義 `gaussianStage`

### 式

$$\text{center}=c,\ \text{radius}=\tfrac54,\ \text{curvature}=\tfrac18,\ \text{sublevel}=\bar B(c,|x_0-c|),\ \text{ODE}:\ \dot x=-W'(x)$$

### Lean のコメント（日本語訳）

> 半径 5/4・曲率 1/8 の局所ガウス段階を、初期部分準位の障壁つきで作る。

### 定義の説明

ガウス谷の 1 段を、一般の段仕様 `StageValleySpec`（Theorem22）に当てはめたものです。中心 \(c\)、局所球の半径 \(5/4\)、曲率下界 \(1/8\)、移動度は恒等、背景ポテンシャルは 0、臨場感ポテンシャルは \(-W\)、**初期部分準位は閉球 \(\bar B(c,|x_0-c|)\)**（初期値が局所球の内部 \(|x_0-c|<5/4\) にあることが条件）。構造体の各フィールド（C² 性、勾配の表示、Hessian の下界・上界、中心での停留、部分準位の障壁など）は、この具体的なガウス谷について 1 つずつ証明で埋めています。

### 証明の概略

1. `well` の微分（`hasDerivAt_well`）・2 階微分（`hasDerivAt_dwell`）で勾配・Hessian の表示を作る。
2. 曲率条件は `ddwell_lower_on_quarter_ball`。
3. 部分準位が閉球 \(\bar B(c,|x_0-c|)\) に等しいことは `gaussian_well_le_iff_abs_le`。その閉包が開球 \(B(c,5/4)\) に入る（障壁条件）ことは、\(|x_0-c|<5/4\) から。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_orbit_ode"></a>

## 補題 `gaussianStage_orbit_ode`

### 式

$$t\ge\text{start}\ \Rightarrow\ \dot x(t)=-W'(x(t))$$

### Lean のコメント（日本語訳）

> 選択したガウス谷軌道は、開始時刻以後にスカラーのガウス ODE を満たす。

### 補題の説明

一般の段の証人（`StageValleyWitness`、局所解の存在・軌道・部分準位への滞在をまとめたもの）が与える軌道は、この具体モデルではスカラーの ODE \(\dot x=-W'(x)\) を満たします。

### 証明の概略

1. 証人の前向き ODE（`orbit_ode_forward`）を、`gaussianStage` の定義（移動度は恒等、実効勾配は \(W'\)）で書き直す。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_orbit_unique"></a>

## 補題 `gaussianStage_orbit_unique`

### 式

$$\text{別の解 }y\ (y(\text{start})=x_0,\ y\in\text{部分準位},\ \dot y=-W'(y))\ \Rightarrow\ y=x\ (t\ge\text{start})$$

### Lean のコメント（日本語訳）

> 同じ初期値から始まり、同じ部分準位を保って同じ ODE を満たす解は一致する。

### 補題の説明

段内の ODE 解の**一意性**。局所強凸の領域では、勾配が（局所）リプシッツなので解は一意です。

### 証明の概略

1. 一般の段の証人の一意性（`orbit_unique`）に帰着。
2. ODE の式を `gaussianStage` の実効勾配の形に直す。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_squared_error_antitone"></a>

## 補題 `gaussianStage_squared_error_antitone`

### 式

$$t\mapsto(x(t)-c)^2\ \text{は}\ [\text{start},\text{start}+T]\ \text{で単調非増加}$$

### Lean のコメント（日本語訳）

> ガウス段階では、中心からの二乗距離が段の時間とともに単調に減る。

### 補題の説明

軌道は中心に近づく一方で、離れることはありません。

### 証明の概略

1. \((x-c)^2\) の導関数は \(2(x-c)\cdot(-W')\)。
2. 軌道は部分準位（\(|x-c|\le|x_0-c|<5/4\)）の中にあるので、`gaussian_dwell_energy_lower` から \((x-c)W'\ge\frac12(x-c)^2\ge0\)、導関数 \(\le0\)。
3. 導関数が非正なので反単調（`antitoneOn_of_deriv_nonpos`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_weighted_square_nonincreasing"></a>

## 補題 `gaussianStage_weighted_square_nonincreasing`

### 式

$$e^{T}\bigl(x(\text{start}+T)-c\bigr)^2\le(x_0-c)^2$$

### Lean のコメント（日本語訳）

> ガウス固有の半径評価により、重み付き二乗距離は減少する。

### 補題の説明

\(q(t)=e^{t-\text{start}}(x(t)-c)^2\) が減少する、つまり距離の二乗が \(e^{-t}\) 以上の速さで減る、ということです。

### 証明の概略

1. \(q'=e^{t-s}\bigl((x-c)^2-2(x-c)W'(x)\bigr)\)。
2. エネルギー評価 \((x-c)W'\ge\frac12(x-c)^2\) から \(q'\le0\)。
3. \(q\) は反単調なので \(q(\text{start}+T)\le q(\text{start})=(x_0-c)^2\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_endpoint_error_12"></a>

## 補題 `gaussianStage_endpoint_error_12`

### 式

$$|x_0-c|\le\tfrac98\ \Rightarrow\ |x(\text{start}+12)-c|\le\tfrac18$$

### Lean のコメント（日本語訳）

> 許容される初期誤差が 9/8 以下なら、12 秒後の誤差は 1/8 以下になる。この時間は Python の段階切替で使う長さである。

### 補題の説明

段の長さ 12 秒で、誤差が \(9/8\) から \(1/8\) へ縮みます。\(e^{12}\ge81\) なので \(e^{12}\cdot\mathrm{err}^2\le(9/8)^2=81/64\) より \(\mathrm{err}^2\le1/64\)。

### 証明の概略

1. `gaussianStage_weighted_square_nonincreasing`（\(T=12\)）：\(e^{12}\,\mathrm{err}^2\le(x_0-c)^2\le81/64\)。
2. \(e^{4}\ge5\)（\(e^y\ge1+y\)）より \(e^{12}\ge125\ge81\)。
3. \(81\,\mathrm{err}^2\le81/64\)、\(\mathrm{err}\le1/8\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.GaussianStageRun"></a>

## 構造体 `GaussianStageRun`

### 式

$$\text{(center }c,\ \text{initial }x_0,\ \text{start }t_0,\ |x_0-c|\le\tfrac98,\ |x_0-c|<\tfrac54,\ \text{witness)}$$

### Lean のコメント（日本語訳）

> ガウス階段の一段と、前後の段をつなぐための実軌道データ。

### 定義の説明

1 つの段について、中心・初期値・開始時刻・初期誤差の評価（\(\le9/8\)、局所球内 \(<5/4\)）と、`gaussianStage` 仕様に対する証人（ODE 解）をまとめた構造体です。

### 証明の概略

構造体の定義のみ（各フィールドは、段の構成時に補題で埋める）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.firstGaussianStageRun"></a>

## 定義 `firstGaussianStageRun`

### 式

$$\text{初期値 }0,\ \text{開始時刻 }0,\ |0-c|\le\tfrac98$$

### Lean のコメント（日本語訳）

> 状態 0 から始まる最初の段を作る。

### 定義の説明

最初の段は初期状態 0、開始時刻 0 から始め、中心 \(c\) との距離 \(\le9/8\) を仮定します。その初期値は局所球 \(5/4\) の内部です。

### 証明の概略

1. \(9/8<5/4\) なので \(|0-c|<5/4\)。
2. 一般の `chooseStageValley` で、この段仕様の証人を（選択公理で）1 つ選ぶ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.nextGaussianStageRun"></a>

## 定義 `nextGaussianStageRun`

### 式

$$x_0'=x(t_0+12),\ \ c'=\text{次の中心},\ \ |c-c'|\le1\ \Rightarrow\ |x_0'-c'|\le\tfrac98<\tfrac54$$

### Lean のコメント（日本語訳）

> 次の段を追加する。前段の終点誤差 1/8 以下と中心移動量 1 以下から、次段の初期状態が中心から半径 5/4 以内にあることを保証する。

### 定義の説明

**段のつなぎの核心**。前段の 12 秒後の終点 \(x(t_0+12)\) を次段の初期値に使います。前段の終点誤差 \(\le1/8\) と中心の移動 \(\le1\) から、新しい中心との距離は \(\le1/8+1=9/8<5/4\)。つまり次の段の初期値は、次の谷の局所強凸の球の内部に入るので、次の段が同じ手順で作れます。

### 証明の概略

1. 前段の `gaussianStage_endpoint_error_12` で \(|x_0'-c|\le1/8\)。
2. 三角不等式で \(|x_0'-c'|\le|x_0'-c|+|c-c'|\le\frac18+1=\frac98\)。
3. \(9/8<5/4\) で局所条件。`chooseStageValley` で次の段の証人を選ぶ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStage_distance_decay"></a>

## 補題 `gaussianStage_distance_decay`

### 式

$$\mathrm{dist}\bigl(x(\text{start}+T),c\bigr)\le|x_0-c|\,e^{-T/2}$$

### Lean のコメント（日本語訳）

> 段軌道のガウス固有の強い評価を示す。この評価で (22.4) を確認し、続いてスカラーの待ち時間条件 (22.5) を適用できる。

### 補題の説明

段内で、中心への距離が**率 \(1/2\) の指数減衰**をすることの形式化。定理22の (22.4)（段内の指数評価）に当たります。

### 証明の概略

1. 重み付き二乗距離 \(e^{T}(x-c)^2\le(x_0-c)^2\)。
2. 両辺を \(e^{T}\) で割り平方根を取る（\(\bigl(e^{-T/2}\bigr)^2=e^{-T}\)）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRunsAux"></a>

## 定義 `gaussianStageRunsAux`

### 式

$$\text{run}_0=\text{first},\quad\text{run}_{n+1}=\text{next}(\text{run}_n,\ \text{target}_{n+1})$$

### Lean のコメント（日本語訳）

> 切替ごとの中心移動が 1 以下なら、実際の段データを再帰的に作る。各段の実軌道終点を次段の初期値に使い、別に選んだ状態を代入しない。

### 定義の説明

中心列 `target`（最初の中心との距離 \(\le9/8\)、隣り合う中心の差 \(\le1\)）が与えられたとき、段を 0 段目から順に作る再帰的な定義です。**各段の初期値は前段の実際の終点**で、勝手な点を代入していません。戻り値は「中心が `target n` に等しい段」の部分型。

### 証明の概略

1. 0 段目は `firstGaussianStageRun`。
2. \(n+1\) 段目は、\(n\) 段目の中心が `target n` で `|target n - target (n+1)| ≤ 1` から、`nextGaussianStageRun`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRuns"></a>

## 定義 `gaussianStageRuns`

### 式

$$\text{runs}(n)=(\text{gaussianStageRunsAux}\ n).\mathrm{val}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

上の再帰の値だけを取り出した段列 \(n\mapsto\)（\(n\) 番目の段）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRuns_center"></a>

## 補題 `gaussianStageRuns_center`

### 式

$$\text{runs}(n).\text{center}=\text{target}(n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n\) 番目の段の中心が、指定した中心列の \(n\) 項目であること。

### 証明の概略

1. 部分型の性質（`property`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRunTime"></a>

## 定義 `gaussianStageRunTime`

### 式

$$t_n=\text{runs}(n).\text{start}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(n\) 番目の段の開始時刻。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRuns_time_recurrence"></a>

## 補題 `gaussianStageRuns_time_recurrence`

### 式

$$t_{n+1}=t_n+12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の開始時刻は 12 秒ずつ進みます（\(t_0=0\) から \(12n\)）。

### 証明の概略

1. `nextGaussianStageRun` の定義（開始時刻 = 前段の開始時刻 + 12）を展開して `simp`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetA"></a>

## 定義 `targetA`

### 式

$$\text{target}_A(n)=\min(n+1,4)=1,2,3,4,4,\dots$$

### Lean のコメント（日本語訳）

> A の目標中心列。1,2,3,4 と進み、その後は 4 で一定にする。

### 定義の説明

Python のケース A の中心列。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetA_first"></a>

## 補題 `targetA_first`

### 式

$$|0-\text{target}_A(0)|\le\tfrac98$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最初の中心 1 は初期値 0 から距離 1 \(\le9/8\)。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetA_step"></a>

## 補題 `targetA_step`

### 式

$$|\text{target}_A(n)-\text{target}_A(n+1)|\le1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

隣り合う中心の差は 0 または 1。

### 証明の概略

1. \(n\le2\) とそれ以降で場合分けして `norm_num`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetC"></a>

## 定義 `targetC`

### 式

$$\text{target}_C(n)=\begin{cases}1&n<2\\2&n\ge2\end{cases}$$

### Lean のコメント（日本語訳）

> C の目標中心列。1,1,2 と進み、その後は 2 で一定にする。

### 定義の説明

Python のケース C の中心列。最初の 2 段は同じ中心です（中心が動かない切替）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetC_first"></a>

## 補題 `targetC_first`

### 式

$$|0-\text{target}_C(0)|\le\tfrac98$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

最初の中心 1 は距離 1。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetC_step"></a>

## 補題 `targetC_step`

### 式

$$|\text{target}_C(n)-\text{target}_C(n+1)|\le1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

隣り合う中心の差は 0 または 1。

### 証明の概略

1. \(n+1<2\) か否かで場合分けして `norm_num`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsA"></a>

## 定義 `runsA`

### 式

$$\text{runsA}=\text{gaussianStageRuns}(\text{target}_A,\ \cdots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース A の段列。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsC"></a>

## 定義 `runsC`

### 式

$$\text{runsC}=\text{gaussianStageRuns}(\text{target}_C,\ \cdots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース C の段列。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsA_centers"></a>

## 補題 `runsA_centers`

### 式

$$\text{runsA}(n).\text{center}=\text{target}_A(n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

A の \(n\) 段目の中心。

### 証明の概略

1. `gaussianStageRuns_center`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsC_centers"></a>

## 補題 `runsC_centers`

### 式

$$\text{runsC}(n).\text{center}=\text{target}_C(n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C の \(n\) 段目の中心。

### 証明の概略

1. `gaussianStageRuns_center`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsA_endpoint_error"></a>

## 補題 `runsA_endpoint_error`

### 式

$$|x_n(\text{start}_n+12)-c_n|\le\tfrac18\quad(\text{ケース A, 各 }n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

A のどの段も、12 秒後の誤差は \(1/8\) 以内。

### 証明の概略

1. 各段の初期誤差の評価（\(\le9/8\)）から `gaussianStage_endpoint_error_12`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsC_endpoint_error"></a>

## 補題 `runsC_endpoint_error`

### 式

$$|x_n(\text{start}_n+12)-c_n|\le\tfrac18\quad(\text{ケース C, 各 }n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

C も同様。

### 証明の概略

1. 各段の初期誤差の評価から `gaussianStage_endpoint_error_12`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsStages"></a>

## 定義 `runsStages`

### 式

$$\text{stage}_n=\text{gaussianStage}(c_n,x_{0,n},t_n,\cdots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段列 `runs` から、一般の段仕様 `StageValleySpec` の列を取り出したもの。接合軌道の一般構成（`stitchedStageOrbit`）への入力です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsWitnesses"></a>

## 定義 `runsWitnesses`

### 式

$$\text{witness}_n:\ \text{StageValleyWitness}(\text{stage}_n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の ODE 解（証人）の列。

### 証明の概略

定義のみ（`runs` の `witness` フィールド）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRunDuration"></a>

## 定義 `gaussianStageRunDuration`

### 式

$$d_n=12$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の長さは常に 12 秒。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRunDuration_pos"></a>

## 補題 `gaussianStageRunDuration_pos`

### 式

$$d_n>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の長さは正。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRunDuration_diverges"></a>

## 補題 `gaussianStageRunDuration_diverges`

### 式

$$\forall B\ \exists n:\ B<\sum_{k<n}d_k$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の長さの総和は無限大に発散する（切替時刻が有限時刻に集積しない、つまり Zeno 的でない）こと。これで、**すべての時刻**がどれかの段に属します。

### 証明の概略

1. \(n>B/12\) を取り、\(\sum_{k<n}12=12n>B\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsActive"></a>

## 定義 `runsActive`

### 式

$$\text{active}(t)=\text{時刻 }t\text{ に使われている段の番号}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各時刻 \(t\) が、どの段の時間区間 \([t_n,t_n+12)\) に入るかを返す関数。切替時刻が強い単調増加で無限に発散すること（`switching_times_unbounded`）を使って、一般構成 `canonicalSwitchStageIndex` で作ります。

### 証明の概略

定義のみ（`switching_times_unbounded` と `canonicalSwitchStageIndex`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsTrajectory"></a>

## 定義 `runsTrajectory`

### 式

$$x(t)=\text{witness}_{\text{active}(t)}.\text{orbit}(t)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

**接合軌道**：時刻 \(t\) では、そのとき使われている段の証人の軌道を採用します。

### 証明の概略

定義のみ（`stitchedStageOrbit`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsStage_start"></a>

## 補題 `runsStage_start`

### 式

$$\text{stage}_n.\text{startTime}=t_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段仕様の開始時刻が、段の開始時刻と一致すること。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussianStageRuns_transition"></a>

## 補題 `gaussianStageRuns_transition`

### 式

$$\text{runs}(n+1).\text{initial}=x_n(t_n+12)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期値は前の段の 12 秒後の終点。段が**連続につながる**ことの定義上の根拠です。

### 証明の概略

1. `nextGaussianStageRun` の定義の展開（`simp`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runsStage_transition"></a>

## 補題 `runsStage_transition`

### 式

$$\text{stage}_{n+1}.\text{initial}=\text{witness}_n.\text{orbit}(t_n+d_n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`gaussianStageRuns_transition` を、一般構成が要求する形（段の長さ \(d_n=12\) を使った形）で述べたもの。

### 証明の概略

1. `gaussianStageRuns_transition` と \(d_n=12\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runs_stage_agreement"></a>

## 補題 `runs_stage_agreement`

### 式

$$\begin{aligned}&x=\text{witness}_n.\text{orbit}\ \text{on}\ [t_n,t_n+12],\ x\ \text{連続},\\&x(t)\in\bar B(c_n,5/4)\ (t\in[t_n,t_n+12)),\\&\dot x=-\text{mobility}\cdot\nabla V_n\ \text{（右微分）}\end{aligned}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

接合軌道は、各段の時間区間で**その段の証人軌道に一致**し、閉区間でも連続（段の境目でも切れない）で、局所球に留まり、その段の ODE を（右微分の意味で）満たします。ガウス階段の接合軌道の基本的な健全性の証明です。

### 証明の概略

1. `switching_times_unbounded` と `canonicalSwitchStageIndex_eq_on_dwell` で、区間 \([t_n,t_n+12)\) の上では使われる段が \(n\)、終点 \(t_n+12\) では \(n+1\) であることを示す。
2. 終点では、次段の初期値が前段の終点（`runsStage_transition`）なので、値が一致して連続。
3. ODE と局所球への滞在は、各段の証人の性質から。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runs_actual_exponential_decay"></a>

## 補題 `runs_actual_exponential_decay`

### 式

$$0\le T\le12\ \Rightarrow\ \mathrm{dist}\bigl(x(t_n+T),c_n\bigr)\le|x_{0,n}-c_n|\,e^{-T/2}$$

### Lean のコメント（日本語訳）

> 接合した各ガウス段は、実際の段初期誤差を係数とする指数評価 (22.4) を収束率 1/2 で満たす。

### 補題の説明

段内の指数評価 `gaussianStage_distance_decay` を、**接合軌道**（`runsTrajectory`）について述べ直したもの。実際の初期誤差を係数とする (22.4) です。

### 証明の概略

1. 接合軌道は段の時間区間で証人の軌道と一致する（`runs_stage_agreement`）。
2. `gaussianStage_distance_decay` を適用。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.gaussian_python_wait_12"></a>

## 補題 `gaussian_python_wait_12`

### 式

$$\max\bigl(0,\ 2\log9\bigr)\le12$$

### Lean のコメント（日本語訳）

> \(C=9/8\)、\(\varepsilon=1/8\)、収束率 1/2 の場合に、Python の段時間 \(T=12\) がスカラーの対数型待ち時間条件 (22.5) を満たす。

### 補題の説明

(22.5) の待ち時間条件は \(T\ge\frac1\rho\log\frac{C}{\varepsilon}\)（\(\rho=\frac12\)、\(C/\varepsilon=9\)）。\(\frac1\rho\log9=2\log9\approx4.4\) で、段の長さ 12 はこれを満たします。

### 証明の概略

1. \(e^3\ge4\)（\(e^y\ge1+y\)）より \(e^6\ge16\ge9\)。
2. よって \(\log9\le6\)、\(2\log9\le12\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.runs_actual_endpoint_error_via_22_5"></a>

## 補題 `runs_actual_endpoint_error_via_22_5`

### 式

$$\mathrm{dist}\bigl(x(t_n+12),c_n\bigr)\le\tfrac18$$

### Lean のコメント（日本語訳）

> ガウスの鋭い評価 (22.4) に待ち時間条件 (22.5) を適用する。Python の段時間 12 秒後、実際の切替軌道の終点誤差は 1/8 以内になる。

### 補題の説明

一般の「(22.4) と (22.5) から段末誤差 \(\le\varepsilon\)」という補題（`exponential_distance_reaches_error_after_dwell`）を、ここの具体量（\(C=9/8\)、\(\varepsilon=1/8\)、\(\rho=1/2\)、\(M=1\)）に適用して、同じ結論を**別の経路**で得ています（`gaussianStage_endpoint_error_12` は直接評価）。

### 証明の概略

1. 一般補題の前提：数値条件（`norm_num`）、待ち時間条件（`gaussian_python_wait_12`）、(22.4)（`runs_actual_exponential_decay` に \(T=12\)、初期誤差 \(\le9/8\)）。
2. 指数の係数 \(e^{-6}\) を掛けて整理。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetA_python_prefix"></a>

## 補題 `targetA_python_prefix`

### 式

$$\text{target}_A=(1,2,3,4,4,\dots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心列 A の先頭 5 項が Python のものと一致する確認。

### 証明の概略

1. `norm_num [targetA]`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.targetC_python_prefix"></a>

## 補題 `targetC_python_prefix`

### 式

$$\text{target}_C=(1,1,2,2,\dots)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心列 C の先頭 4 項が Python のものと一致する確認。

### 証明の概略

1. `norm_num [targetC]`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseBField"></a>

## 定義 `caseBField`

### 式

$$F_B(x)=-W'(x)\quad(A=2,\ \sigma=\tfrac32,\ c=6)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

ケース B のベクトル場：中心 6 の谷の勾配流。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseA_actual_stage_endpoint"></a>

## 補題 `caseA_actual_stage_endpoint`

### 式

$$\mathrm{dist}\bigl(x_A(t_n+12),\ c_n\bigr)\le\tfrac18\quad(\forall n)$$

### Lean のコメント（日本語訳）

> Python のケース A にある 4 つの増加する中心を、実際の連続接合軌道で表す。各段は段内 ODE を満たし、12 秒後に指定した終点誤差 1/8 以内へ入る。

### 補題の説明

**ケース A の主結論**：Python が数値で示した「A は中心が 1,2,3,4 と動いても、各段の終わりには誤差が小さい」を、**連続時間の実際の接合軌道**について証明します。

### 証明の概略

1. `runs_actual_endpoint_error_via_22_5` に `targetA_first`、`targetA_step` を与える。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseC_actual_stage_endpoint"></a>

## 補題 `caseC_actual_stage_endpoint`

### 式

$$\mathrm{dist}\bigl(x_C(t_n+12),\ c_n\bigr)\le\tfrac18\quad(\forall n)$$

### Lean のコメント（日本語訳）

> Python のケース C では中心が変わらない段も含めて、同じ接合軌道構成と終点誤差評価を使う。中心移動が 0 の切替も扱う。

### 補題の説明

**ケース C の主結論**。中心が動かない切替（最初の 2 段）も含みます。

### 証明の概略

1. `runs_actual_endpoint_error_via_22_5` に `targetC_first`、`targetC_step` を与える。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.exists_caseB_actual_flow"></a>

## 補題 `exists_caseB_actual_flow`

### 式

$$\exists\,x,\varepsilon>0:\ x(0)=0,\ x(t)\in\bar B(6,6)\ (t\ge0),\ \dot x=-W'(x)\ \text{on}\ (-\varepsilon,\infty)$$

### Lean のコメント（日本語訳）

> B のベクトル場は全域で滑らかである。初期状態を含むコンパクトなエネルギー部分準位集合を使い、初期値が次段の局所強凸球の外にあっても前向きのグローバル解が存在することを示す。

### 補題の説明

ケース B（初期値 0 が中心 6 の局所強凸球の**外**）でも、ODE の大域的な前向き解が存在します。局所球の外なので強凸性は使えませんが、ガウス谷のエネルギー \(W\) が流れに沿って減ることから、軌道はコンパクトな閉球 \(\bar B(6,6)\) の中にとどまり、爆発しません。

### 証明の概略

1. ベクトル場 \(F_B\) は全域で \(C^1\)（`fun_prop`）。
2. 部分準位 \(K=\bar B(6,6)\)（\(=\{W\le W(0)\}\)）はコンパクトで、前向き不変（\(W\) が流れに沿って非増加、`gaussian_well_le_iff_abs_le`）。
3. 上流の一般定理 `exists_global_forward_trajectory_of_compact_forward_invariant_set` を適用。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseB_speed_bound_on_unit_interval"></a>

## 補題 `caseB_speed_bound_on_unit_interval`

### 式

$$0\le x\le1\ \Rightarrow\ |F_B(x)|\le\tfrac1{24}$$

### Lean のコメント（日本語訳）

> ガウス谷の尾部では、状態が [0,1] にあるときの B 段の速度は 1/24 以下。

### 補題の説明

中心 6 から 5 以上離れた谷の尾部では、ガウス関数が小さく、勾配（速度）はごく小さい。B の軌道が「谷に入るまで時間がかかる」ことの定量的な根拠です。

### 証明の概略

1. \(|x-6|\ge5\)。
2. \(|F_B|=\frac89|x-6|e^{-(x-6)^2/(9/2)}\)。\(|x-6|\le6\)、指数部の引数は \(\ge\frac{25}{9/2}=\frac{50}{9}\) なので \(e^{-50/9}\le\frac1{128}\)（\(e^{5/18}\ge\frac{23}{18}\) の 20 乗が \(\ge128\)）。
3. したがって \(|F_B|\le\frac89\cdot6\cdot\frac1{128}=\frac1{24}\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseBField_c1_on_large_ball"></a>

## 補題 `caseBField_c1_on_large_ball`

### 式

$$F_B\ \text{は}\ \bar B(6,7)\ \text{で}\ C^1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一意性の定理（局所リプシッツ）を使うための正則性。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseB_orbit_never_hits_center"></a>

## 補題 `caseB_orbit_never_hits_center`

### 式

$$\forall t\ge0:\ x(t)\ne6$$

### Lean のコメント（日本語訳）

> B 軌道が有限時刻で平衡点に到達したと仮定すると、逆向きの ODE 一意性からそれ以前の解も定数になってしまう。

### 補題の説明

軌道は中心 6（平衡点）に**有限時間では到達しません**。もし到達したら、時間を反転して「ずっと 6」の解と一致するはずで、初期値 \(0\ne6\) に矛盾します。

### 証明の概略

1. \(t=0\) なら \(x(0)=0\ne6\)。
2. \(t>0\) で \(x(t)=6\) と仮定する。\(F_B\) は \(\bar B(6,7)\) で \(C^1\)（`caseBField_c1_on_large_ball`）なので局所リプシッツ定数 \(L\) がある（`exists_lipschitz_constant_on_closedBall_of_contDiffAt`）。
3. Mathlib の ODE の一意性 `ODE_solution_unique_of_mem_Icc_left`（右端 \(t\) で一致する 2 つの解は区間 \([0,t]\) 全体で一致する）を、軌道と定数解 \(6\)（\(F_B(6)=0\) なので解）に適用。
4. すると \(x(0)=6\) となり、\(x(0)=0\) に矛盾。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseB_orbit_lt_center"></a>

## 補題 `caseB_orbit_lt_center`

### 式

$$t\ge0\ \Rightarrow\ x(t)<6$$

### Lean のコメント（日本語訳）

> B 軌道は任意の有限な前向き時刻で平衡点より左側にある。

### 補題の説明

軌道は中心を越えず、常に左側にいます。越えるには、連続性から中心を通る必要があり、それは前の補題で排除されています。

### 証明の概略

1. 「中心に到達しない」（仮定 `hnever`、`caseB_orbit_never_hits_center` で得られる）を仮定として受け取る。
2. \(x(t)\ge6\) なら、\(x(0)=0<6\le x(t)\) なので中間値の定理で \(x(s)=6\) となる \(s\in[0,t]\) があり、`hnever` に矛盾。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseBField_pos_of_lt_center"></a>

## 補題 `caseBField_pos_of_lt_center`

### 式

$$x<6\ \Rightarrow\ F_B(x)>0$$

### Lean のコメント（日本語訳）

> 平衡点より左では、B 段のベクトル場は右向きである。

### 補題の説明

中心の左では、流れは常に右向き（中心に向かう）。

### 証明の概略

1. \(F_B(x)=-\frac89(x-6)e^{(\cdot)}\)、\(x-6<0\)、指数関数は正。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseB_orbit_monotoneOn"></a>

## 補題 `caseB_orbit_monotoneOn`

### 式

$$x\ \text{は}\ [0,T]\ \text{で単調増加}$$

### Lean のコメント（日本語訳）

> B 軌道は平衡点の左側にとどまり、そこでベクトル場が正なので、任意の有限区間で単調増加する。

### 補題の説明

B の軌道は左から右へ単調に動きます。

### 証明の概略

1. 軌道は常に \(x<6\)（`caseB_orbit_lt_center`）で、そこでは導関数 \(F_B>0\)。
2. 導関数が正なら単調（`monotoneOn_of_deriv_nonneg`）。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.caseB_orbit_outside_target_at_12"></a>

## 補題 `caseB_orbit_outside_target_at_12`

### 式

$$\mathrm{dist}\bigl(x(12),6\bigr)>5$$

### Lean のコメント（日本語訳）

> B 軌道は時刻 12 までに中心 6 から距離 5 以内へ入らない。[0,1] での尾部速度が 1/24 以下であるため、距離 1 を進むにも 12 秒より長い時間が必要となる。

### 補題の説明

\(x(12)<1\)（まだ 1 に達していない）ことを示します。\([0,1]\) の間は速度が \(\le1/24\) なので、距離 1 を進むのに \(\ge24\) 秒かかります。

### 証明の概略

1. 軌道は単調増加（`caseB_orbit_monotoneOn`）。
2. \(x(12)\ge1\) と仮定して矛盾を導く：中間値の定理で \(x(s)=1\) となる \(s\le12\) を取る。\([0,s]\) では \(0\le x\le1\) なので速度 \(\le1/24\)。変位 1 には \(s\ge24\) が必要だが \(s\le12\)。
3. よって \(x(12)<1\)。\(x(12)<6\) と合わせて \(6-x(12)>5\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.exists_caseB_actual_switch_outside_next_ball"></a>

## 補題 `exists_caseB_actual_switch_outside_next_ball`

### 式

$$\exists\,x:\ x(0)=0,\ \mathrm{dist}\bigl(x(12),8\bigr)>\tfrac54$$

### Lean のコメント（日本語訳）

> B の最初の段の実軌道は、次の中心 8 の局所球に入らない。中心 6 へ向かう最初の段を 12 秒動かしても終点は 1 未満なので、次の中心 8 から 7 より大きく離れている。

### 補題の説明

**ケース B の主結論**。最初の段（中心 6）を 12 秒流しても \(x(12)<1\) で、次の中心 8 から \(7\) 以上離れています。次の段の局所強凸の球（半径 \(5/4\)）に入らないので、次の段に局所評価を適用する条件が破れています。

### 証明の概略

1. `exists_caseB_actual_flow` の軌道を取る。`caseB_orbit_never_hits_center`、`caseB_orbit_outside_target_at_12`、`caseB_orbit_lt_center` を使う。
2. \(x(12)<1\) から \(\mathrm{dist}(x(12),8)=8-x(12)>7>5/4\)。

----

<a id="Tomabechi.Examples.Theorem22GaussianStages.exists_caseB_actual_switch_outside_next_ball_with_ode"></a>

## 補題 `exists_caseB_actual_switch_outside_next_ball_with_ode`

### 式

$$\exists\,x,\varepsilon>0:\ x(0)=0,\ \mathrm{dist}(x(12),8)>\tfrac54,\ \dot x=-W'(x)\ \text{on}\ (-\varepsilon,\infty)$$

### Lean のコメント（日本語訳）

> 初期値 0 から中心 6 へ向かう実際のガウス勾配流が、12 秒後にも次中心 8 の局所球の外にあることを、ODE と同じ軌道について結論する。

### 補題の説明

上の主結論を、その軌道が**本当にガウス勾配流の ODE 解である**ことを型に保持した形にしたもの（監査用）。

### 証明の概略

1. 前の補題と同じ議論に、ODE（`hflow`）を結論へ添える。

----

## コメント修正記録

（なし。この `.lean` のコメントは、本書執筆時点の宣言と食い違っていないことを確認した。）
