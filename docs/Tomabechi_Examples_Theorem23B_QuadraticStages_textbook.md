# Tomabechi/Examples/Theorem23B_QuadraticStages.lean 解説

> 対象: [`Tomabechi/Examples/Theorem23B_QuadraticStages.lean`](../Tomabechi/Examples/Theorem23B_QuadraticStages.lean)。全ての定義・構造体・補題・定理を、ファイルに現れる順に書き出す。各項目は「式 → Lean のコメント（日本語訳）→ 補題（定義）の説明 → 証明の概略」の順。式は読みやすさを優先した近似で、厳密な型は `.lean` を参照。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 抽象度 | 世界の記述の「高さ」。物理層が最小、「空」が最大（完備束の元）。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| 連続微分可能（\(C^1\), \(C^2\)） | 導関数（2階導関数）が存在して連続。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 勾配流 | 勾配の逆向きに動く微分方程式 \(\dot x=-A\nabla V\)。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| 束（lattice） | 2 元の上界・下界（結び \(\vee\)・交わり \(\wedge\)）がある順序集合。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（諸行無常）の **条件 23-B**（目標領域 TCZ が段ごとに変わり、隣り合う段の TCZ が一致しない）の一般核 `theorem22_stage_specs_and_switches_give_condition23B_core`（`Dynamics/StageSwitching.lean`）は、「LUB 列と段の仕様と切替の条件」を入力として受け取ります。この `.lean` は、**一次元の平行移動二次谷**という最も簡単な具体モデルについて、**一般核の入力をすべて**証明して、一般核を実際に適用します。

モデル：段 \(n=0,1,2,\dots\) の谷は \(V_n(x)=\frac12(x-n)^2\)（中心 \(n\)、曲率 1）、勾配流 \(\dot x=-(x-n)\)。各段の長さは 10、開始時刻は \(t_n=10n\)、最初の初期値は \(-1\)。段 \(n\) の軌道は閉形式
$$x(t)=c+(x_0-c)e^{-(t-t_n)}\qquad(c=n)$$
（凍結軌道）で、初期誤差が率 1 で指数減衰します。次の段の初期値は、前段の 10 秒後の終点です。

証明する入力は次のとおりです。

1. **段の仕様**：二次谷を段仕様 `StageValleySpec` に接続する（`quadraticStage`）。閉形式の軌道がこの仕様の ODE 解であること、一般の段の証人（`chooseStageValley`）が選ぶ軌道と一致すること、唯一の最小点が中心であること、減衰率 \(=1\)、減衰振幅 \(=|x_0-c|\) を示す。
2. **LUB 列と忠実表象**：段の中心に対応する抽象度の列 \(u_n=v_n=n\in\mathrm{WithTop}\,\mathbb N\) が、\(u_{n+1}=u_n\sqcup v_{n+1}\)（段ごとの更新）、\(u_n<\top\)、\(v_{n+1}\not\le u_n\)（毎回厳密に新しい）を満たし、表象 \(\top\mapsto-1,\ n\mapsto n\) が単射であること。
3. **段のつなぎ**：段の初期誤差は常に \(|x_0-c|\le11/10\)（\(e^{-10}\le1/11\) による）。各段の初期値は前の中心 \(n-1\) 以下で、半径は 1 より大きい。切替の時刻は \(t_{n+1}=t_n+10\)、段の長さは正で、時刻は無限大に発散する。
4. **待ち時間条件**：\(\theta=1/4\)、\(\varepsilon=1/8\) とし、(22.5) の待ち時間 \(\max(0,\frac1\rho\log\frac{C}{\varepsilon})\)（減衰率 \(\rho=1\)、振幅 \(C\le11/10\)）が段の長さ 10 以下（\(\log(8.8)<10\)）。
5. **段間の隙間と線分**：隣り合う最小点の距離 \(=1\)、しきい値条件 \(\theta=\frac14<\frac12\cdot1^2\)（\(\frac12=\) 曲率/2 × 距離²）、隣り合う最小点の間の線分が次の段の半径 \(>1\) の局所球に入る。
6. **一般核の適用**：以上を `theorem22_stage_specs_and_switches_give_condition23B_core` に渡す（`quadraticStages_give_condition23B_core`）。

これにより、このモデルで「各段の TCZ は閉集合、隣り合う段の TCZ は一致しない、切替はあらゆる有限時刻より後にも起こる」などの 23-B の結論が得られます。

### 0.2 このファイルが証明していないこと

- **一次元の平行移動二次谷という、非常に特殊な具体モデル**です。Python の例（`examples/theorem23_impermanence.py`）の 23-B そのものの再現ではなく、「一般核の入力をすべて満たすモデルが存在する」ことの構成例です。
- 一般の問題（任意のポテンシャル・次元・段列）で一般核の入力が成り立つことは示しません。
- 一般の LUB 束や、定理22の他の具体モデル（ガウス谷）との接続は別ファイルです。

### 0.3 ファイル冒頭のコメント（日本語訳）

> # 定理23-B：平行移動二次谷の全入力
>
> ここでは一変数の二次谷を使い、段階中心・厳密な凍結軌道・有限の正の待ち時間を具体化する。

名前空間は `Tomabechi.Examples.Theorem23B`（`open Filter`、`Topology`）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStage"></a>

## 定義 `quadraticStage`

### 式

$$\text{center}=c,\ \text{radius}=|x_0-c|+1,\ \text{gain}=\text{presenceGain}=\text{curvature}=1,\ \text{presence}(x)=-\tfrac12(x-c)^2,\ \text{sublevel}=\bar B(c,|x_0-c|)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

一次元の二次谷 \(V(x)=\frac12(x-c)^2\)（\(=-\)presence）を、一般の段仕様 `StageValleySpec` に当てはめたものです。移動度は恒等、背景ポテンシャルは 0、曲率 1、**局所球の半径は \(|x_0-c|+1\)**（初期値を含む球より少し大きい）、初期部分準位は \(\bar B(c,|x_0-c|)\)。仕様のフィールド（C² 性、勾配・Hessian の表示、停留点、障壁条件、部分準位が \(\{V\le V(x_0)\}\) に等しいことなど）は、具体的な二次式について 1 つずつ証明しています。

### 証明の概略

1. presence \(=-\frac12(x-c)^2\)、勾配 \(-(x-c)\)、Hessian \(=-\mathrm{id}\) を、微分の計算（`HasFDerivAt`）で確認。
2. 曲率条件（\(\mathrm{gain}\cdot\mathrm{presenceGain}\cdot\mathrm{curvature}-\mathrm{backgroundCurvature}=1>0\)）は `norm_num`。
3. 部分準位が閉球 \(\bar B(c,|x_0-c|)\) に等しいこと（\(\frac12(x-c)^2\le\frac12(x_0-c)^2\iff|x-c|\le|x_0-c|\)）。その閉包が半径 \(|x_0-c|+1\) の開球に入る（障壁条件）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit"></a>

## 定義 `quadraticFrozenOrbit`

### 式

$$x(t)=c+(x_0-c)\,e^{-(t-\text{start})}$$

### Lean のコメント（日本語訳）

> 二次谷の厳密な凍結軌道：初期誤差が指数率 1 で減衰する。

### 定義の説明

\(\dot x=-(x-c)\) の厳密解。「凍結」は、段の中心を固定して（その段の間は谷が動かないとして）流すという意味です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.continuous_quadraticFrozenOrbit"></a>

## 補題 `continuous_quadraticFrozenOrbit`

### 式

$$t\mapsto x(t)\ \text{は連続}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉形式の軌道は連続。

### 証明の概略

1. `fun_prop`。

----

<a id="Tomabechi.Examples.Theorem23B.hasDerivAt_quadraticFrozenOrbit"></a>

## 補題 `hasDerivAt_quadraticFrozenOrbit`

### 式

$$\dot x(t)=-(x(t)-c)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

閉形式の軌道が \(\dot x=-(x-c)\) を満たす。

### 証明の概略

1. \(e^{-(t-s)}\) の微分は \(-e^{-(t-s)}\)（合成関数の微分）。
2. 定数倍と定数加算を重ね、\(x-c=(x_0-c)e^{-(t-s)}\) で整理。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_distance_formula"></a>

## 補題 `quadraticFrozenOrbit_distance_formula`

### 式

$$\mathrm{dist}\bigl(x(t),c\bigr)=|x_0-c|\,e^{-(t-\text{start})}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

中心との距離の厳密な式（等式）。指数減衰の率が正確に 1 であることを示します。

### 証明の概略

1. \(x(t)-c=(x_0-c)e^{-(t-s)}\) で絶対値を取る（\(e^{(\cdot)}>0\)）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_initial_and_in_sublevel"></a>

## 補題 `quadraticFrozenOrbit_initial_and_in_sublevel`

### 式

$$x(\text{start})=x_0\ \wedge\ x(t)\in\bar B(c,|x_0-c|)\quad(t\ge\text{start})$$

### Lean のコメント（日本語訳）

> 閉形式の軌道は初期時刻で指定した初期値を取り、全ての後時刻で初期 sublevel 内に留まる。

### 補題の説明

軌道が指定の初期値から始まり、以後ずっと初期の部分準位集合の中にいる。ODE の一意性（部分準位内での）を使うための前提です。

### 証明の概略

1. \(t=\text{start}\) で \(e^0=1\)。
2. \(t\ge\text{start}\) では \(e^{-(t-s)}\le1\) なので \(\mathrm{dist}(x(t),c)\le|x_0-c|\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_solves_stage"></a>

## 補題 `quadraticFrozenOrbit_solves_stage`

### 式

$$\dot x(t)=-\nabla V_{\text{stage}}(x(t))$$

### Lean のコメント（日本語訳）

> 指定した閉形式軌道は二次谷の ODE を解く。

### 補題の説明

`hasDerivAt_quadraticFrozenOrbit` を、段仕様 `quadraticStage` の「実効勾配」`stageEffectiveGradient` を使った形に書き直したもの。

### 証明の概略

1. 実効勾配の定義（移動度 = 恒等、勾配 \(=x-c\)）を展開して `hasDerivAt_quadraticFrozenOrbit`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFrozenOrbit_eq_witness_orbit"></a>

## 補題 `quadraticFrozenOrbit_eq_witness_orbit`

### 式

$$x(t)=\text{（一般の段の証人が選ぶ軌道）}(t)\quad(t\ge\text{start})$$

### Lean のコメント（日本語訳）

> 一般の段階証人が選ぶ軌道は、ここで与えた厳密解と一致する。

### 補題の説明

一般の段構成（選択公理で選ぶ `chooseStageValley`）が返す軌道が、ここで書き下した閉形式の軌道と**同じもの**であること。これで、一般核の入力にある抽象的な軌道を、具体式で扱えるようになります。

### 証明の概略

1. 閉形式軌道は、初期値（`…_initial_and_in_sublevel`）・部分準位への滞在・ODE（`…_solves_stage`）の 3 条件を満たす。
2. 一般の段の証人の軌道の**一意性**（`orbit_unique`）を適用。

----

<a id="Tomabechi.Examples.Theorem23B.chooseQuadraticStage_minimizer"></a>

## 補題 `chooseQuadraticStage_minimizer`

### 式

$$\text{（証人が選ぶ唯一の最小点）}=c$$

### Lean のコメント（日本語訳）

> 二次谷の定理22の証人が選ぶ唯一の最小点は、指定した谷の中心である。

### 補題の説明

一般の段の証人は「部分準位内の唯一の最小点」を持ちます。二次谷ではそれが中心 \(c\)。

### 証明の概略

1. 中心が最小点の条件（停留・部分準位内）を満たす。
2. 証人の最小点の一意性（`minimizer_unique`）から、証人の最小点 \(=c\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticNext"></a>

## 定義 `quadraticNext`

### 式

$$\text{quadraticNext}(n,x,t)=\text{quadraticStage}(n+1,\ x,\ t)$$

### Lean のコメント（日本語訳）

> 二次谷の一意最小点を中心として読む。

### 定義の説明

\(n\) 段目から \(n+1\) 段目へ移るときの次の段の仕様：中心は \(n+1\)、初期値 \(x\)、開始時刻 \(t\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticNext_initial"></a>

## 補題 `quadraticNext_initial`

### 式

$$(\text{quadraticNext}\,n\,x\,t).\text{initial}=x$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期値が指定どおりであること。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticNext_start"></a>

## 補題 `quadraticNext_start`

### 式

$$(\text{quadraticNext}\,n\,x\,t).\text{startTime}=t$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻が指定どおりであること。

### 証明の概略

1. 定義から `rfl`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticFirst"></a>

## 定義 `quadraticFirst`

### 式

$$\text{quadraticFirst}=\text{quadraticStage}(0,\ -1,\ 0)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

最初の段：中心 0、初期値 \(-1\)、開始時刻 0。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticDuration"></a>

## 定義 `quadraticDuration`

### 式

$$d_n=10$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の長さは 10。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticTime"></a>

## 定義 `quadraticTime`

### 式

$$t_n=10n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(n\) 段目の開始時刻。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages"></a>

## 定義 `quadraticStages`

### 式

$$\text{stage}_0=\text{first},\ \text{stage}_{n+1}=\text{next}(n,\ x_n(t_n+10),\ t_{n+1})$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

段の列。一般構成 `endpointCompatibleStageSequence`（Theorem23）で、**各段の初期値を前段の実際の終点にして**つなぎます。

### 証明の概略

定義のみ（`endpointCompatibleStageSequence`）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_center"></a>

## 補題 `quadraticStages_center`

### 式

$$\text{stage}_n.\text{center}=n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n\) 段目の中心は \(n\)。

### 証明の概略

1. 帰納法（次の段の中心は \(n+1\)）、`quadraticNext` の定義。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_shape"></a>

## 補題 `quadraticStages_shape`

### 式

$$\text{stage}_n=\text{quadraticStage}(n,\ \text{initial}_n,\ \text{start}_n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

どの段も `quadraticStage` の形をしている（中心 \(n\)）。以後の補題で `quadraticStage` についての結果を使えるようにします。

### 証明の概略

1. \(n=0\) は `quadraticFirst` の定義、\(n+1\) は `quadraticNext` の定義。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStage_decayRate"></a>

## 補題 `quadraticStage_decayRate`

### 式

$$\text{decayRate}=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般の証人が返す段の**減衰率**（(22.4) の指数 \(\rho\)）は 1。

### 証明の概略

1. 証人の減衰率の定義（\(\sqrt{\text{曲率}\ldots}\) 型の式）を展開し、gain=presenceGain=curvature=1、背景曲率 0 から 1 に。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStage_decayAmplitude"></a>

## 補題 `quadraticStage_decayAmplitude`

### 式

$$\text{decayAmplitude}=|x_0-c|$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

一般の証人が返す**減衰振幅**（(22.4) の係数 \(C\)）は初期誤差 \(|x_0-c|\)。厳密解の式 \(\mathrm{dist}=|x_0-c|e^{-t}\) と整合します。

### 証明の概略

1. 振幅の定義（実効ポテンシャルの差の平方根）を展開すると \(\sqrt{(x_0-c)^2}=|x_0-c|\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticU"></a>

## 定義 `quadraticU`

### 式

$$u_n=n\in\mathrm{WithTop}\,\mathbb N$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象度の束（ここでは \(\mathrm{WithTop}\,\mathbb N=\mathbb N\cup\{\top\}\)、数の大小の順序）での、\(n\) 段目までの LUB（最小上界）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticV"></a>

## 定義 `quadraticV`

### 式

$$v_n=n\in\mathrm{WithTop}\,\mathbb N$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

\(n\) 段目で新たに加わる世界。ここでは \(u_n\) と同じ値です。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticRepresentation"></a>

## 定義 `quadraticRepresentation`

### 式

$$\top\mapsto-1,\quad n\mapsto n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

抽象度の束の元 → 状態空間 \(\mathbb R\) への表象。\(\top\)（最上位）は \(-1\) に写し、自然数はそのまま。段の中心を束の元と結びつけます。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticRepresentation_injective"></a>

## 補題 `quadraticRepresentation_injective`

### 式

$$\text{表象は単射}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

表象が**忠実**（異なる元は異なる実数に写る）であること。これで、束で隣り合う段が異なる中心になる（`stages n` の中心が異なる）ことが従います。

### 証明の概略

1. 場合分け：\(\top\) と \(\top\) は自明。\(\top\) と自然数 \(b\) では \(b=-1\) となり \(b\ge0\) に矛盾。自然数どうしは `exact_mod_cast`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticU_update"></a>

## 補題 `quadraticU_update`

### 式

$$u_{n+1}=u_n\sqcup v_{n+1}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

LUB の更新則：新しい世界を加えると、最小上界は古い上界と新しい世界の上界になる。\(n+1=\max(n,n+1)\)。

### 証明の概略

1. \(\sqcup=\max\) と `Nat.cast_succ` で `simp`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticU_below_top"></a>

## 補題 `quadraticU_below_top`

### 式

$$u_n<\top$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

LUB は常に最上位 \(\top\) より真に下（空に達しない）。

### 証明の概略

1. 自然数は \(\top\) より小さい（`WithTop.coe_lt_top`）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticV_new"></a>

## 補題 `quadraticV_new`

### 式

$$\neg\,(v_{n+1}\le u_n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

新しい世界 \(v_{n+1}=n+1\) は、これまでの LUB \(u_n=n\) の下にない（毎回、厳密に新しい情報が加わる）。

### 証明の概略

1. \(n+1\le n\) は偽（`Nat.cast_le`）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_start"></a>

## 補題 `quadraticStages_start`

### 式

$$\text{stage}_n.\text{startTime}=t_n=10n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の開始時刻が `quadraticTime` と一致する。

### 証明の概略

1. 一般補題 `endpointCompatibleStageSequence_startTime`（Theorem23）に、最初の段の開始時刻 \(0=t_0\) を与える。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_transition"></a>

## 補題 `quadraticStages_transition`

### 式

$$\text{stage}_{n+1}.\text{initial}=\text{witness}_n.\text{orbit}(t_n+10)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

次の段の初期値が、前の段の 10 秒後の終点であること。

### 証明の概略

1. `endpointCompatibleStageSequence` の定義から。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticTime_recurrence"></a>

## 補題 `quadraticTime_recurrence`

### 式

$$t_{n+1}=t_n+d_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻の漸化式。

### 証明の概略

1. \(10(n+1)=10n+10\)（`ring`）。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticDuration_positive"></a>

## 補題 `quadraticDuration_positive`

### 式

$$d_n>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の長さは正。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticTime_unbounded"></a>

## 補題 `quadraticTime_unbounded`

### 式

$$\forall B\ \exists n:\ B<\sum_{k<n}d_k$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の長さの総和が無限大に発散する（切替が有限時刻に集積しない）。

### 証明の概略

1. \(n>B/10\) を取り、\(\sum_{k<n}10=10n>B\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticTime_tendsto_unbounded"></a>

## 補題 `quadraticTime_tendsto_unbounded`

### 式

$$\forall B\ \exists n:\ B<t_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

開始時刻 \(t_n=10n\) が上に有界でない。

### 証明の概略

1. \(n>B/10\) を取る。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticEndpoint_distance_bound"></a>

## 補題 `quadraticEndpoint_distance_bound`

### 式

$$|x-c|\le\tfrac{11}{10}\ \Rightarrow\ \bigl|c+(x-c)e^{-10}-(c+1)\bigr|\le\tfrac{11}{10}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

段の 10 秒後の終点は、初期値 \(x\) から \(e^{-10}\) の割合だけ中心 \(c\) に近づいた点 \(c+(x-c)e^{-10}\)。この点の**次の中心** \(c+1\) からの距離も \(\le11/10\)。つまり初期誤差の評価 \(\le11/10\) が次の段へ引き継がれます（誤差の不変式）。

### 証明の概略

1. \(e^{10}\ge11\)（\(e^y\ge1+y\)）より \(e^{-10}\le\frac1{11}\)。
2. 三角不等式 \(\le|x-c|e^{-10}+1\le\frac{11}{10}\cdot\frac1{11}+1=\frac{11}{10}\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_initial_distance_bound"></a>

## 補題 `quadraticStages_initial_distance_bound`

### 式

$$\forall n:\ |\text{initial}_n-n|\le\tfrac{11}{10}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

各段の初期誤差の上界 \(11/10\)（これが減衰振幅の上界になる）。

### 証明の概略

1. 帰納法。\(n=0\)：初期値 \(-1\)、\(|-1-0|=1\le\frac{11}{10}\)。
2. \(n+1\)：前段の終点（閉形式、\(t=t_n+10\)）に `quadraticEndpoint_distance_bound` を適用。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_initial_le_previous_center"></a>

## 補題 `quadraticStages_initial_le_previous_center`

### 式

$$\forall n:\ \text{initial}_n\le n-1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n\) 段目の初期値は、前の中心 \(n-1\) 以下。軌道は常に前の中心より左側から始まります。これで局所球の半径が 1 より大きいことが言えます。

### 証明の概略

1. 帰納法。\(n=0\)：\(-1\le-1\)。
2. 次の段の初期値は前段の終点 \(n+(x_0-n)e^{-10}\)。\(x_0-n\le-1\)（帰納法の仮定）で第 2 項は \(\le0\) なので \(\le n=(n+1)-1\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_radius_gt_one"></a>

## 補題 `quadraticStages_radius_gt_one`

### 式

$$\text{radius}_n>1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

局所球の半径は \(|x_0-c|+1\)。初期値が前の中心以下なので \(|x_0-c|\ge1\)、半径は \(>1\) です。隣り合う中心の距離 1 の線分がこの球に入ることに使います。

### 証明の概略

1. `quadraticStages_initial_le_previous_center` から \(|x_0-n|=n-x_0\ge1\)。
2. 半径 \(=|x_0-n|+1\ge2>1\)。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_decayAmplitude_bound"></a>

## 補題 `quadraticStages_decayAmplitude_bound`

### 式

$$\text{decayAmplitude}_n\le\tfrac{11}{10}$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

減衰振幅（一般の証人の (22.4) の係数 \(C\)）が \(11/10\) 以下。

### 証明の概略

1. 振幅 \(=|x_0-n|\)（`quadraticStage_decayAmplitude`）、`quadraticStages_initial_distance_bound`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_decayRate"></a>

## 補題 `quadraticStages_decayRate`

### 式

$$\text{decayRate}_n=1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

減衰率はすべての段で 1。

### 証明の概略

1. `quadraticStage_decayRate`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticTheta"></a>

## 定義 `quadraticTheta`

### 式

$$\theta_n=\tfrac14$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

TCZ のしきい値 \(\theta_n\)（段の評価がこれ以下の領域が目標領域）。すべての段で \(1/4\)。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticEpsilon"></a>

## 定義 `quadraticEpsilon`

### 式

$$\varepsilon_n=\tfrac18$$

### Lean のコメント（日本語訳）

（コメントなし）

### 定義の説明

各段の許容誤差（(22.5) の \(\varepsilon\)）。

### 証明の概略

定義のみ。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticEpsilon_positive"></a>

## 補題 `quadraticEpsilon_positive`

### 式

$$\varepsilon_n>0$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

許容誤差が正。

### 証明の概略

1. `norm_num`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_wait_bound"></a>

## 補題 `quadraticStages_wait_bound`

### 式

$$\max\Bigl(0,\ \tfrac1\rho\log\tfrac{C_n}{\varepsilon_n}\Bigr)\le d_n=10$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

**(22.5) の待ち時間条件**。段の長さ 10 は、誤差を \(\varepsilon=1/8\) まで下げるのに必要な時間 \(\frac1\rho\log\frac C\varepsilon\)（\(\rho=1\)、\(C\le11/10\)、\(\log\frac{11/10}{1/8}=\log8.8\approx2.2\)）以上です。

### 証明の概略

1. \(\rho=1\)（`quadraticStages_decayRate`）、\(C\le\frac{11}{10}\)（`quadraticStages_decayAmplitude_bound`）。
2. \(\frac C\varepsilon\le\frac{11/10}{1/8}\le11\le e^{10}\)（\(e^y\ge1+y\)）。
3. \(C>0\) なら \(\log\) の評価で \(\le10\)、\(C=0\) なら 0。`max` を処理。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_minimizer"></a>

## 補題 `quadraticStages_minimizer`

### 式

$$\text{（証人の最小点）}_n=n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

\(n\) 段目の最小点は中心 \(n\)。

### 証明の概略

1. `quadraticStages_shape` と `chooseQuadraticStage_minimizer`。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_segment_in_next_ball"></a>

## 補題 `quadraticStages_segment_in_next_ball`

### 式

$$[x^*_n,\,x^*_{n+1}]=[n,n+1]\subset\bar B\bigl(n+1,\ \text{radius}_{n+1}\bigr)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

隣り合う最小点を結ぶ線分 \([n,n+1]\) が、次の段の局所強凸球に入ること。（次の段の局所評価が、線分上で使えることを保証します。）

### 証明の概略

1. 線分 \(=[n,n+1]\)（`segment_eq_Icc`）、各点は次の中心 \(n+1\) から距離 \(\le1\)。
2. 次の段の半径は \(|x_0-(n+1)|+1\ge1\)（`quadraticStages_shape` で `quadraticStage` の形にして `simp`）なので球に入る。

----

<a id="Tomabechi.Examples.Theorem23B.quadraticStages_give_condition23B_core"></a>

## 定義 `quadraticStages_give_condition23B_core`

### 式

$$\text{一般核 }\texttt{theorem22\_stage\_specs\_and\_switches\_give\_condition23B\_core}\ \text{の結論}$$

### Lean のコメント（日本語訳）

> 二次谷列の全入力を、定理23-B の一般切替核へ渡す。

### 定義の説明

**このファイルの主結果**。上で用意した入力——LUB 列と忠実表象、段の仕様、しきい値の隙間条件（\(\theta=\frac14<\frac{1\cdot1\cdot1-0}{2}\cdot1^2=\frac12\)）、線分の条件、時刻の漸化式・単調増加・発散、待ち時間条件——を一般核に渡して、23-B の結論（各段の TCZ は閉集合、隣り合う TCZ は一致しない、LUB が厳密に増える、時刻が無限大に発散するなど）を得ます。これは `def` として宣言されていますが、中身は命題の証明項です。

### 証明の概略

1. 一般核の入力を順に与える。
2. 中心と LUB の対応は `quadraticStages_center` と `quadraticRepresentation` の定義。隙間条件は `quadraticStages_minimizer` と `norm_num`（\(\frac14<\frac12\)）。その他は上の補題。

----

## コメント修正記録

（なし。この `.lean` のコメントは、本書執筆時点の宣言と食い違っていないことを確認した。）
