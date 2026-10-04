# Tomabechi/Dynamics/StageSwitching.lean 解説

> 対象: [`Tomabechi/Dynamics/StageSwitching.lean`](../Tomabechi/Dynamics/StageSwitching.lean)（定理23のTCZ・段階切替・非再帰の核）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閉到達可能 TCZ | 制御で実際に到達できる範囲（到達可能集合の閉包 \(K\)）に制限した TCZ \(=K\cap\{V_0\le\theta\}\)。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 閉ループ | 状態を見て制御を決める（フィードバック）ときの、制御を代入した後の状態の動き。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| リプシッツ連続 | \(\lvert f(x)-f(y)\rvert\le L\lvert x-y\rvert\) をみたす関数。傾きが有界。 |
| Fréchet 微分 | 多変数関数の（線形近似としての）微分。勾配や Hessian の定義に使う。 |
| 勾配 \(\nabla V\) | 関数の最も増える方向を向くベクトル。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| フィルター（Filter） | 「十分近くで」「十分大きな \(t\) で」という極限の言い方を一般化した Lean の道具。 |
| HasDerivAt | `HasDerivAt f f' x`: \(f\) が点 \(x\) で微分可能で、微分が \(f'\)。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| エントロピー \(H\) | 不確かさの量 \(-\sum p\log p\)。 |
| 単射 | 異なる入力が異なる出力に写る（情報を失わない）。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（無常）の**段階的な部分**を扱うファイルです。定理22の谷（各段階で凍結した軌道の収束先）を材料にして、次を示します。

1. **TCZ**（目標集合）は、段階ごとに**閉集合**で、**空でなく**、隣り合う段階では**異なる**（固定されない）。
2. **LUB** の列は、条件 23-B のもとで**毎段厳密に上昇**する。
3. **切替の時刻**は**有界でない**（無限に切り替わる。有限の時間で永久に終わらない：Zeno 性がない）。
4. 実際の**切替軌道**は、各段階の待ち時間の区間で、凍結した谷の軌道と**一致**し、切替の時点で誤差 \(\varepsilon_n\) 以内に入る。
5. 以上を、定理22の段階仕様（`StageValleySpec`）・平均場の段階入力から構成した軌道に対して、**エンドツーエンド**で述べる。

### 0.2 構成

| 節 | 宣言 | 内容 |
| --- | --- | --- |
| 第二法則 | `entropy_production_integral_nonnegative` | 生成率の非負性 ⇒ 積分の非負性 |
| TCZ | `stageTCZ`, `isClosed_*`, `limit_in_closed_reachable_*`, `chosen_valley_*`, `all_chosen_*`, `theorem22_stage_specs_give_nonfixed_TCZs` | 段階の TCZ の定義・閉性・最小点の所属・隣接 TCZ の不一致 |
| 非再帰・順序 | `complete_state_never_repeats`, `every_new_stage_strictly_higher`, `adjacent_stage_minimizers_distinct`, `no_finite_stage_tcz_fixation`, `stage_tcz_changes_*` | 条件 23-B の各部分 |
| 切替時刻 | `switching_times_unbounded`, `infinitely_many_switches_*`, `every_finite_time_in_some_dwell` | 非 Zeno 性 |
| 切替軌道の同定 | `stagewise_frozen_orbits_agree` 〜 `all_stage_switches_*` | 実軌道と凍結軌道が一致する |
| 標準的な段階番号・継ぎ合わせ | `canonicalSwitchStageIndex*`, `endpointCompatibleStageSequence*`, `stitchedStageOrbit`, `stitched_stage_orbits_*`, `canonical_stitched_*`, `endpoint_compatible_stage_factory_*` | 軌道を凍結軌道から**構成**する |
| まとめ | `condition23B_*`, `theorem23_conditionB_stagewise_conclusions`, `canonicalStageTrajectory`, `theorem22_stage_specs_and_switches_give_condition23B_core`, `meanField_*` | 定理23の段階的な結論のまとめ |

### 0.3 条件 23-A / 23-B

- **条件 23-A**：持続的な厳密散逸（`EntropyBalance.lean` で扱う）。
- **条件 23-B**：LUB 列が毎段**厳密に**上がる（各段階に既存の LUB に含まれない新情報がある）、隣り合う最小点が異なる（閾値のギャップ条件）、切替の待ち時間が正で総和が発散する、など。

### 0.4 このファイルが証明していないこと

- 論文のとおり、**すべての有限段階が最大元 \(\top\) より下にある**（`hbelowTop`）ことは**仮定**です。結合の厳密な上昇だけからは出ません。
- **切替状態が次段階の吸引域に入ること**（`hinitial` と `hdecay`）、**待ち時間の総和の発散**、**段階間の線分の包含**、**強凸性の差の閾値**は、**明示的な仮定**です。局所 Hessian のデータだけからは導きません。
- 一般の定理22の段階仕様の**解析的な妥当性**（Hessian 評価・強凸性など）は構成の義務として呼び出し側に残ります（`next` の各仕様）。
- 非再帰（`complete_state_never_repeats`）は、完全状態が一価のエントロピーを持つという前提の上のものです（`EntropyBalance.lean` を参照）。

### 0.5 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理23の TCZ・段階切替・非再帰の核**
>
> 旧 `Theorem23.lean` の、TCZ の閉性・非固定性、完全状態の非再帰、段階切替と条件 23-B を配置する。公開名前空間と宣言名を保ち、定量的な滞在時間・指数の速さ・切替条件は変更しない。

（もとのコメントが日本語なのでそのまま写しています。）名前空間は `Tomabechi.Theorem23`。`open Filter`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem23.entropy_production_integral_nonnegative"></a>

## 補題 `entropy_production_integral_nonnegative`

### 式

$$\Pi\ge0\ \text{on}\ [a,b]\ \Longrightarrow\ \int_a^b\Pi\,dt\ge0$$

### Lean のコメント（日本語訳）

> 第二法則の符号の節：生存区間全体でエントロピー生成が非負なら、その区間での総生成は非負である。可積分性の前提は明示的である：点ごとの非負性だけでは、実数値の積分はよく定義されないからである。
> 日本語の要約：区間上で総生成率が非負なら、その積分も非負である。

### 補題の説明

非負関数の積分は非負、という基本的な事実です。

### 証明の概略

1. `intervalIntegral.integral_nonneg`（非負関数の区間積分は非負）を適用（4 行）。

----

<a id="Tomabechi.Theorem23.stageTCZ"></a>

## 定義 `stageTCZ`

### 式

$$\mathrm{TCZ}_n=\text{region}_n\cap\text{reachable}_n\cap\{x\mid V_n(x)-V_n(x^\*_n)\le\theta_n\}$$

### Lean のコメント（日本語訳）

> 段階 \(n\) の閉じた到達可能な TCZ。段階のポテンシャルの、局所最小点からの上の劣水準集合の内側にある、到達可能な部分として定義する。
> 日本語の要約：段階の TCZ を、段階の領域・閉な到達可能集合・最小点からのポテンシャル差の条件の共通部分として定義する。

### 定義の説明

**TCZ（目標集合）**：段階 \(n\) の谷の近傍のうち、(i) 段階の領域内で、(ii) 凍結軌道で到達可能で、(iii) 最小値からのポテンシャルの差が \(\theta_n\) 以下の点の集合です。

### 証明の概略

1. 定義：`{x | x ∈ region n ∧ x ∈ reachable n ∧ potential n x - potential n (xstar n) ≤ theta n}`（4 行）。

----

<a id="Tomabechi.Theorem23.isClosed_stageTCZ"></a>

## 補題 `isClosed_stageTCZ`

### 式

$$\text{region},\text{reachable}\ \text{閉},\ V_n\ \text{連続}\ \Longrightarrow\ \mathrm{TCZ}_n\ \text{閉}$$

### Lean のコメント（日本語訳）

> 到達可能な領域が閉で、段階のポテンシャルが連続なら、論文の定義での段階の TCZ は閉である。
> 日本語の要約：閉領域と閉な到達可能集合、領域上の連続性から、TCZ の閉性を導く。

### 補題の説明

閉集合の共通部分は閉、連続関数の劣水準集合は閉、という組み合わせです。

### 証明の概略

1. `IsClosed.inter` と、連続関数の劣水準集合（`isClosed_le`）で閉性を得る（5 行）。

----

<a id="Tomabechi.Theorem23.isClosed_stageTCZ_of_continuousOn"></a>

## 補題 `isClosed_stageTCZ_of_continuousOn`

### 式

$$V_n\ \text{が region 上で連続}\ \Longrightarrow\ \mathrm{TCZ}_n\ \text{閉}$$

### Lean のコメント（日本語訳）

> 同じ閉性の結論は、閉な段階の領域上の連続性だけを必要とする。これは、正則性が段階のパッケージの一部であり、モデルの状態空間の外では主張されないときに有用である。
> 日本語の要約：全空間での連続性を仮定せず、段階の領域上の連続性だけから TCZ の閉性を示す。

### 補題の説明

上の補題の、連続性の仮定を領域上に弱めた版です。

### 証明の概略

1. 領域上の連続性から、「領域上での劣水準集合」の閉性（`ContinuousOn.preimage_isClosed_of_isClosed`）を得て共通部分をとる（15 行）。

----

<a id="Tomabechi.Theorem23.limit_in_closed_reachable_of_exponential_decay"></a>

## 補題 `limit_in_closed_reachable_of_exponential_decay`

### 式

$$\operatorname{dist}(x(t),x^\*)\le Ce^{-\lambda(t-t_0)}\ \Longrightarrow\ x^\*\in\overline{x([t_0,\infty))}$$

### Lean のコメント（日本語訳）

> 指数収束は、段階の最小点を、凍結した軌道の閉じた到達可能集合の中に置く。これは、論文が直前の最小点を \(\mathrm{TCZ}_n\) に入れるために使う閉包の段階であり、連続時間の軌道を整数のオフセットで標本化することで得られ、閉包には、それで十分である。
> 日本語の要約：指数収束する軌道の極限点が、閉な到達可能集合に含まれることを示す。

### 補題の説明

軌道が最小点に指数収束するなら、最小点は軌道の**閉包**に入ります（軌道上の点列 \(x(t_0+n)\) が最小点に収束するから）。

### 証明の概略

1. \(x(t_0+n)\) と \(x^\*\) の距離は \(Ce^{-\lambda n}\to0\)（`tendsto_exp_atBot` と定数倍）。
2. 収束する点列の極限は閉包に入る（`mem_closure_of_tendsto`、32 行）。

----

<a id="Tomabechi.Theorem23.chosen_valley_minimizer_in_stageTCZ"></a>

## 補題 `chosen_valley_minimizer_in_stageTCZ`

### 式

$$\theta\ge0\ \Longrightarrow\ x^\*\in\mathrm{TCZ}$$

### Lean のコメント（日本語訳）

> 定理22で選ばれた最小点は、その段階の TCZ に属する：定量的な凍結軌道の収束が、それを閉じた到達可能集合に置き、一方、そのポテンシャルの差は 0 で、閾値は非負である。
> 日本語の要約：定理22の谷の最小点が、到達可能な閉包と閾値の条件を満たし、段階の TCZ に属することを示す。

### 補題の説明

谷の最小点 \(x^\*\) は、(i) 領域内（内部の最小点）、(ii) 軌道の閉包に入る（上の補題）、(iii) ポテンシャルの差が 0 \(\le\theta\)、の 3 条件を満たすので、TCZ に属します。

### 証明の概略

1. `limit_in_closed_reachable_of_exponential_decay` と `distance_decay`（StageData）で到達可能性。
2. 領域内（`minimizer_interior`）、ポテンシャルの差は 0 で \(\theta\ge0\)（11 行）。

----

<a id="Tomabechi.Theorem23.chosen_valley_adjacent_stageTCZs_differ"></a>

## 補題 `chosen_valley_adjacent_stageTCZs_differ`

### 式

$$x^\*_n\in U_{n+1}\ \&\ \text{閾値の条件}\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 直前の最小点が次の段階の局所領域にあり、連続する最小点の変位についての論文の閾値が成り立つなら、定理22で構成された谷は、隣り合う TCZ の非固定性に十分である。古い最小点が、それ自身の閉じた到達可能な TCZ に属することは、選ばれた指数収束する軌道から導かれる。
> 日本語の要約：段階間の線分の包含と、曲率のギャップの条件から、隣り合う TCZ の不一致を示す。

### 補題の説明

TCZ が段階ごとに変わる（固定されない）ことを、定理22の谷から示します。古い最小点は古い TCZ にあり、次の段階の強凸性のギャップによって新しい TCZ から外れます。

### 証明の概略

1. 選んだ谷の軌道の距離減衰（`distance_decay`、`decayAmplitude`・`decayRate` と、それらの正値性）から、古い段階の最小点は古い段階の閉到達可能 TCZ に入る（`limit_in_closed_reachable_of_exponential_decay`）。
2. 次の段階のポテンシャルの強凸性（`per_stage_effective_strong_convexity`）と、背景・臨場感の微分表示から、前段の最小点での値が次段の閾値を超えること（ギャップ）を示す。
3. これにより前段の最小点は次段の TCZ に入らず、隣接する TCZ は異なる（120 行）。

----

<a id="Tomabechi.Theorem23.all_chosen_stage_TCZs_closed_and_nonfixed"></a>

## 補題 `all_chosen_stage_TCZs_closed_and_nonfixed`

### 式

$$\forall n:\ \mathrm{TCZ}_n\ \text{閉},\ \ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 定理22の段階のパッケージと、選ばれた谷の軌道は、閉な TCZ を与え、その値は、情報の更新が隣り合うたびに変わる。直前の最小点が次の段階の領域に入ることと、論文の厳密なギャップの閾値は、明示的な仮定のままである。
> 日本語の要約：全段階の TCZ の閉性と、隣り合う段階での不一致をまとめる。

### 補題の説明

全段階について、TCZ の閉性と非固定性を一括して述べます。

### 証明の概略

1. 各 \(n\) で `isClosed_stageTCZ_of_continuousOn` と `chosen_valley_adjacent_stageTCZs_differ` を適用（30 行）。

----

<a id="Tomabechi.Theorem23.all_chosen_stage_TCZs_nonempty"></a>

## 補題 `all_chosen_stage_TCZs_nonempty`

### 式

$$\forall n,\ \mathrm{TCZ}_n\neq\varnothing$$

### Lean のコメント（日本語訳）

> 各段階の谷の最小点は、その凍結軌道の閉包にある。その 0 のポテンシャルの差は、すべての非負の閾値を満たす。したがって、すべての段階の TCZ は空でない。
> 日本語の要約：各段階の最小点が閉な到達可能集合に入ることから、段階の TCZ の非空性を得る。
（もとの注：各段階の谷の最小点は、その凍結軌道の閉到達可能部分に含まれる。閾値が非負なら部分準位の条件も満たすため、各段階の TCZ は空でない。）

### 補題の説明

各段階の最小点が TCZ の元になるので、TCZ は空でありません。

### 証明の概略

1. 選んだ谷の軌道の距離減衰（`distance_decay`）と `limit_in_closed_reachable_of_exponential_decay` から、各段階の最小点がその段階の閉到達可能 TCZ に入る。
2. よって各段階の TCZ は非空（37 行）。

----

<a id="Tomabechi.Theorem23.theorem22_stage_specs_give_nonfixed_TCZs"></a>

## 補題 `theorem22_stage_specs_give_nonfixed_TCZs`

### 式

$$\text{(定理22の段階仕様)}\ \Longrightarrow\ \mathrm{TCZ}_n\ \text{非空・閉・}\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n,\ \ \|x^\*_{n+1}-x^\*_n\|>0$$

### Lean のコメント（日本語訳）

> 定理22で選ばれた段階の軌道を、定理23の「空でない・閉・非固定」の TCZ の結論に結びつける。有限次元での軌道の構成を型クラスで明示し、遷移の線分の条件と厳密なギャップの閾値を仮定する。隣り合う最小点の間の距離の正値性は、閾値から導かれる。
> 日本語の要約：定理22の段階仕様から、TCZ の非空・閉・隣り合う段階での不一致を、全段階で得る。

### 補題の説明

上の 3 つ（非空性・閉性・非固定性）に、隣り合う最小点が異なること（`adjacent_stage_minimizers_distinct`）を加えた総まとめです。

### 証明の概略

1. `chooseAllStageValleys` で全段階の谷の証人を選ぶ。
2. `all_chosen_stage_TCZs_nonempty`（非空）と `all_chosen_stage_TCZs_closed_and_nonfixed`（閉・隣接段で異なる）を組み合わせる（77 行）。

----

<a id="Tomabechi.Theorem23.complete_state_never_repeats"></a>

## 補題 `complete_state_never_repeats`

### 式

$$S(t_2)-S(t_1)=\int\Pi>0\ \Longrightarrow\ \text{state}(t_2)\neq\text{state}(t_1)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

`EntropyBalance.lean` の `complete_state_never_repeats_of_strict_entropy_balance` と同じ内容（積分形の収支＋厳密な正値性 ⇒ 状態は繰り返さない）の、このファイルでの再述です。

### 証明の概略

1. 状態が等しいと、エントロピー差が 0 になり、正の積分と矛盾（9 行）。

----

<a id="Tomabechi.Theorem23.every_new_stage_strictly_higher"></a>

## 補題 `every_new_stage_strictly_higher`

### 式

$$\forall n,\ v_{n+1}\not\le u_n\ \Longrightarrow\ \forall n,\ u_n<u_{n+1}$$

### Lean のコメント（日本語訳）

> 条件 23-B は、各段階が現在の LUB より下にない情報を与えるなら、連続する LUB の更新のすべてを厳密にする。
> 日本語の要約：各段階に既存の LUB に含まれない新情報があるとき、LUB の列が毎段厳密に上昇する。

### 補題の説明

`Theorem22.lean` の `lub_update_is_strict` を全段階に適用します。

### 証明の概略

1. `lub_update_is_strict`（Theorem22）を各 \(n\) に適用（5 行）。

----

<a id="Tomabechi.Theorem23.adjacent_stage_minimizers_distinct"></a>

## 補題 `adjacent_stage_minimizers_distinct`

### 式

$$0\le\theta_{n+1}<\tfrac{c_{n+1}}2\delta_n^2\ \Longrightarrow\ x^\*_n\neq x^\*_{n+1}$$

### Lean のコメント（日本語訳）

> 正の劣水準のギャップの閾値は、隣り合う段階の最小点が異なることを強制する：もしそれらの距離が 0 なら、非負の閾値の厳密な上界が不可能になる。これは、述べられた閾値から、条件 23-B の、連続する最小点の分離の節を確かめる。
> 日本語の要約：閾値のギャップの条件から、隣り合う段階の最小点が異なることを導く。

### 補題の説明

\(x^\*_n=x^\*_{n+1}\) なら距離 \(\delta_n=0\)、すると \(\theta_{n+1}<0\) となって \(\theta_{n+1}\ge0\) に矛盾します。

### 証明の概略

1. 背理法：等しいと仮定して \(\delta_n=0\)。閾値の不等式が \(\theta_{n+1}<0\) になり矛盾（9 行）。

----

<a id="Tomabechi.Theorem23.no_finite_stage_tcz_fixation"></a>

## 補題 `no_finite_stage_tcz_fixation`

### 式

$$\forall n,\ x^\*_n\in\mathrm{tcz}_n\ \wedge\ x^\*_n\notin\mathrm{tcz}_{n+1}\ \Longrightarrow\ \forall n,\ \mathrm{tcz}_{n+1}\neq\mathrm{tcz}_n$$

### Lean のコメント（日本語訳）

> 条件 23-B の段階のギャップの議論は、有限の段階での TCZ の固定を排除する。仮定は、古い最小点が古い到達可能性の TCZ にあることと、次の段階のポテンシャルのギャップが、その劣水準の閾値を超えることを明示的に述べる。定理22は、具体的なモデルで後者の前提を果たすのに使う強凸性の評価を与える。
> 日本語の要約：古い最小点が古い TCZ に属し、次の段階の TCZ に属さない条件から、隣り合う TCZ の不一致を示す。

### 補題の説明

`Theorem22.lean` の `stage_tcz_changes`（集合の不一致）を全段階にまとめた補題です。

### 証明の概略

1. 各 \(n\) で `stage_tcz_changes`（Theorem22）を適用（5 行）。

----

<a id="Tomabechi.Theorem23.stage_tcz_changes_of_strong_convexity_gap"></a>

## 補題 `stage_tcz_changes_of_strong_convexity_gap`

### 式

$$x^\*_n\in\text{reachable}_n,\ \ \tfrac{c_{n+1}}2\delta_n^2\le V_{n+1}(x^\*_n)-V_{n+1}(x^\*_{n+1}),\ \theta_{n+1}<\tfrac{c_{n+1}}{2}\delta_n^2\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 論文の強凸性のギャップと劣水準の閾値は、古い最小点が、古い閉な到達可能集合にあるなら、古い TCZ には属するが、次のものには属さないことを示す。これは、式 (23.2) への具体的な橋である。ギャップの前提は、2 つの最小点を結ぶ線分に沿って、次の段階の強凸性の不等式を適用した結果である。それを導くのに必要な幾何的な仮定は、呼び出し側で記録される。
> 日本語の要約：古い最小点の古い到達可能性と、次の段階の強凸性のギャップから、TCZ の不一致を示す。

### 補題の説明

古い最小点は、(i) 古い領域内、(ii) 古い到達可能集合内、(iii) ポテンシャルの差が 0 \(\le\theta_n\) なので古い TCZ に属し、新しい TCZ ではギャップが閾値を超えるので属さない。したがって 2 つの TCZ は異なります。

### 証明の概略

1. 前段の最小点が前段の TCZ に属すること（3 条件）を確認する。
2. ギャップと閾値の仮定から、次段の TCZ には属さないことを示す。
3. `stage_tcz_changes`（Theorem22）で、2 つの TCZ が異なると結論する（34 行）。

----

<a id="Tomabechi.Theorem23.stage_tcz_changes_of_strong_convexity"></a>

## 補題 `stage_tcz_changes_of_strong_convexity`

### 式

$$\text{次段の強凸性}\ +\ \text{停留}\ \Longrightarrow\ \text{ギャップ（導出）}\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> ギャップそのものを仮定する代わりに、定理21の一階の強凸性の不等式から段階のギャップを導く。次の段階の最小点は停留していなければならず、両方の最小点が次の局所領域に入っていなければならない。したがって、強凸性が必要とする線分の幾何は明示的である。古い最小点の、古い到達可能な TCZ への所属は、論文の到達可能性の条件のままである。
> 日本語の要約：次の段階の強凸性と最小点の停留条件から、ポテンシャルの差の下界を導き、旧最小点の到達可能性と合わせて TCZ の不一致を示す。

### 補題の説明

上の補題のギャップの仮定を、**強凸性の支持不等式**から導く版です：次の段階の最小点 \(x^\*_{n+1}\) で勾配が 0 なので、\(V_{n+1}(x^\*_n)-V_{n+1}(x^\*_{n+1})\ge\frac c2\|x^\*_n-x^\*_{n+1}\|^2\)。

### 証明の概略

1. 強凸性の定義（`StronglyConvexOn`）を \((x^\*_{n+1},x^\*_n)\) に使い、停留性（勾配 0）でギャップの下界を得る。
2. `stage_tcz_changes_of_strong_convexity_gap` を適用（10 行）。

----

<a id="Tomabechi.Theorem23.stage_tcz_changes_of_hessian_lower_bound"></a>

## 補題 `stage_tcz_changes_of_hessian_lower_bound`

### 式

$$\text{領域が凸},\ \text{Hessian}\ \succeq c\ \Longrightarrow\ \text{強凸性}\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 段階ごとの TCZ の分離は、定理22で使う局所 Hessian の下界から直接導ける。領域の凸性は、2 つの最小点を結ぶ線分が領域に留まることを保証する。Fréchet 微分と Hessian の仮定が、ポテンシャルのギャップに使う強凸性の不等式を与える。
> 日本語の要約：領域上の Hessian の下界と線分の包含から、強凸性のギャップを導いて、TCZ の不一致を得る。

### 補題の説明

Hessian の下界から強凸性（`stronglyConvexOn_of_hessian_lower_bound`、StrongConvexity）を導き、直前の補題に帰着します。

### 証明の概略

1. `stronglyConvexOn_of_hessian_lower_bound` で強凸性。
2. `stage_tcz_changes_of_strong_convexity` を適用（12 行）。

----

<a id="Tomabechi.Theorem23.stage_tcz_changes_of_theorem22_gain_threshold"></a>

## 補題 `stage_tcz_changes_of_theorem22_gain_threshold`

### 式

$$\text{定理22の閾値}\ +\ \text{Hessian の 2 つの境界}\ \Longrightarrow\ \text{強凸な谷}\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 定理23の段階ごとの部分への、論文のパラメータの橋。定理22のゲインの閾値と 2 つの Hessian の境界は、すべての段階で、実効的に強凸な谷を作る。古い最小点の凍結軌道による到達可能性、次の段階の劣水準の閾値、点ごとの段階の幾何が、隣り合う閉な TCZ の非固定性を与える。到達可能性と指数的な軌道の評価は、ゲインの閾値だけからは出ないので、明示的な入力のままである。
> 日本語の要約：定理22の閾値・Hessian の条件から、強凸な谷を導き、定理23の TCZ の分離に接続する。

### 補題の説明

段階の強凸性を、定理22の `per_stage_effective_strong_convexity`（ゲイン閾値と Hessian 境界）から得て、TCZ の不一致に接続します。

### 証明の概略

1. `all_stages_effective_strong_convexity`（Theorem22）で各段階の有効ポテンシャルの強凸性（強さ \(\kappa pm-\beta\)）を得る。
2. `limit_in_closed_reachable_of_exponential_decay` で前段の最小点が前段の TCZ に属すことを示す。
3. `stage_tcz_changes_of_strong_convexity`（強凸性とギャップによる TCZ の不一致）を適用する（78 行）。

----

<a id="Tomabechi.Theorem23.stage_tcz_changes_of_strong_convexity_and_decay"></a>

## 補題 `stage_tcz_changes_of_strong_convexity_and_decay`

### 式

$$\operatorname{dist}(x_k(t),x^\*_k)\le C_ke^{-\lambda_k(t-t_k)}\ \Longrightarrow\ x^\*_n\in\text{reachable}_n\ \Longrightarrow\ \text{TCZ の不一致}$$

### Lean のコメント（日本語訳）

> TCZ の分離の定理の、直前の段階の到達可能性の前提は、その指数収束の評価から導かれる。ここでの到達可能集合は、切替の状態から出発する凍結した段階の軌道の閉包であり、論文の \(K_n\) の構成に合う。次の領域上の強凸性、線分の包含、閾値のギャップは、明示的なままである。
> 日本語の要約：指数減衰から、古い最小点の閉な到達可能性を得て、次の段階の強凸性のギャップを適用する。

### 補題の説明

到達可能性（古い最小点が古い軌道の閉包にあること）を、**指数収束**（`limit_in_closed_reachable_of_exponential_decay`）から得ます。

### 証明の概略

1. `limit_in_closed_reachable_of_exponential_decay` で到達可能性。
2. `stage_tcz_changes_of_strong_convexity` を適用（15 行）。

----

<a id="Tomabechi.Theorem23.switching_times_unbounded"></a>

## 補題 `switching_times_unbounded`

### 式

$$\text{duration}_n>0,\ \ t_{n+1}=t_n+\text{duration}_n,\ \ \textstyle\sum\text{duration}=\infty\ \Longrightarrow\ \forall B,\exists n,\ B<t_n\ \wedge\ t\ \text{厳密増加}$$

### Lean のコメント（日本語訳）

> 非 Zeno の切替の時刻は発散する。したがって、無限個の段階が、有限の物理時間ですべて完了することはできない。
> 日本語の要約：正の各待ち時間と、総和の発散から、切替時刻が厳密に増加して非有界になることを示す。

### 補題の説明

切替時刻 \(t_n=t_0+\sum_{k<n}\text{duration}_k\) は、総和の発散により非有界で、各待ち時間が正なので厳密に増加します。

### 証明の概略

1. \(t_n=t_0+\sum_{k<n}d_k\)（帰納法）。
2. 発散の仮定で \(\sum_{k<n}d_k>B-t_0\) となる \(n\)。各項が正なので厳密増加（18 行）。

----

<a id="Tomabechi.Theorem23.infinitely_many_switches_after_every_finite_time"></a>

## 補題 `infinitely_many_switches_after_every_finite_time`

### 式

$$\forall T,\forall K,\ \exists n\ge K,\ T<t_n$$

### Lean のコメント（日本語訳）

> 任意の有限時間より後にも、任意の段階の番号より後にも、切替が起こる。したがって、有限時間の物理時刻が、無限の運転の永久の終了時刻になることはありえない。
> 日本語の要約：任意の有限時刻・任意の段階の番号より後にも切替時刻があり、有限時刻での永久終了を排除する。

### 補題の説明

切替時刻が厳密に増加して非有界なので、任意の時刻・任意の段階番号より後にも切替があります。

### 証明の概略

1. `switching_times_unbounded` で非有界・厳密増加。厳密増加から `StrictMono`。
2. \(\max(T,t_K)\) を超える \(n\) をとると、単調性より \(n\ge K\)（12 行）。

----

<a id="Tomabechi.Theorem23.every_finite_time_in_some_dwell"></a>

## 補題 `every_finite_time_in_some_dwell`

### 式

$$t_0\le t\ \Longrightarrow\ \exists n,\ t\in[t_n,\,t_n+\text{duration}_n)$$

### Lean のコメント（日本語訳）

> 切替時刻の列が漸化式に従い、非有界であるとき、最初の切替より後のすべての有限時刻は、ある段階の半開の待ち時間の区間に属する。切替の瞬間は次の段階に割り当てられる。
> 日本語の要約：時刻の漸化式と切替時刻の非有界性から、開始後の各有限時刻が、いずれかの半開の待ち時間の区間に入ることを示す。

### 補題の説明

時間軸 \([t_0,\infty)\) が、半開区間 \([t_n,t_{n+1})\) で隙間なく分割されることの確認です。

### 証明の概略

1. \(t<t_k\) となる最小の \(k\)（`Nat.find`）をとる。\(k>0\)（\(t\ge t_0\) だから）。
2. \(n=k-1\) とすると \(t_n\le t<t_{n+1}=t_n+\text{duration}_n\)（26 行）。

----

<a id="Tomabechi.Theorem23.stagewise_frozen_orbits_agree"></a>

## 補題 `stagewise_frozen_orbits_agree`

### 式

$$\text{actual}(t_n)=\text{frozen}_n(t_n),\ \text{同じ ODE}\ \Longrightarrow\ \text{actual}=\text{frozen}_n\ \text{on}\ [t_n,t_n+d_n]$$

### Lean のコメント（日本語訳）

> 有限の各待ち時間の区間で、切替軌道は、両方が同じ切替状態から同じ有限次元の閉ループ ODE を解くとき、対応する凍結した段階の軌道と一致する。場の正則性、閉球への包含、待ち時間での連続性、右片側の微分は、段階ごとに公開されている。一致は、片側の ODE の一意性の API から従い、切替をまたぐ微分可能性は要らない。
> 日本語の要約：有限次元の \(C^1\) の場に対する一意性を使って、同じ初期値の実軌道と凍結軌道を、待ち時間の区間で同定する。

### 補題の説明

`Theorem22.lean` の `switched_orbits_agree_on_closed_interval_of_right_derivative` を全段階に適用した補題です。

### 証明の概略

1. 各 \(n\) で、\(C^1\) 場のリプシッツ定数（`exists_lipschitz_constant_on_closedBall_of_contDiffAt`）を得て、右微分版の一意性（Theorem22）を適用（12 行）。

----

<a id="Tomabechi.Theorem23.switched_orbit_agrees_with_stage_valley_witness"></a>

## 補題 `switched_orbit_agrees_with_stage_valley_witness`

### 式

$$\text{actual}(t_0)=w.\text{orbit}(t_0)\ \Longrightarrow\ \text{actual}=w.\text{orbit}\ \text{on}\ [t_0,t_0+T]$$

### Lean のコメント（日本語訳）

> 構成された定理22の段階の証人は、実際の切替の状態がその指定された初期状態であるとき、1 つの待ち時間の区間で、実際の切替軌道と一致する。凍結軌道の局所的な Lipschitz の一意性の定数は、段階の仕様の \(C^1\) の場から導かれる。その前向きの ODE、閉球への包含、初期の連続性、初期値は、大域的な谷の証人から来る。実際の切替軌道の区間での解、包含、閉じた待ち時間の区間での連続性だけが、切替のモデルから与えられる。切替では、実際の軌道は右微分だけを必要とする。
> 日本語の要約：構成済みの `StageValleyWitness` の軌道と切替軌道を、初期値の整合のもとで同定する。

### 補題の説明

1 段階の同定です。凍結軌道の側の性質（ODE・球内・連続性）は証人 `StageValleyWitness` から得ます。

### 証明の概略

1. \(C^1\) 場のリプシッツ定数（`exists_lipschitz_constant_on_closedBall_of_contDiffAt`、`closedLoopC1`）。
2. 凍結軌道の球内（`orbit_in_closedBall`）・前向き ODE（`orbit_ode_forward`）から右微分。
3. `switched_orbits_agree_on_closed_interval_of_right_derivative`（Theorem22）で一致（43 行）。

----

<a id="Tomabechi.Theorem23.all_stage_switches_follow_selected_valleys_before_tolerance"></a>

## 補題 `all_stage_switches_follow_selected_valleys_before_tolerance`

### 式

$$\forall n:\ \text{actual}=w_n.\text{orbit}\ \text{on}\ [t_n,t_n+d_n]\ \wedge\ \operatorname{dist}(\text{actual}(t_n+d_n),x^\*_n)\le\varepsilon_n$$

### Lean のコメント（日本語訳）

> 構成された谷の一意性の議論と、(22.5) の待ち時間の評価を、切替の各段階で適用する。これは、各完全な待ち時間の区間での、選ばれた凍結軌道との一致と、指定された端点の許容誤差の両方を与える。
> 日本語の要約：各段階の軌道の一致と待ち時間の条件を組み合わせて、切替時の誤差の評価を得る。

### 補題の説明

各段階で、上の同定と、待ち時間の評価（`dwell_time_suffices_for_error`、Theorem22）を合わせます。

### 証明の概略

1. `switched_orbit_agrees_with_stage_valley_witness` で一致。
2. `distance_decay`（StageData）と待ち時間の条件 `hwait` から、端点での誤差が \(\varepsilon_n\) 以下（43 行）。

----

<a id="Tomabechi.Theorem23.all_stage_switches_follow_valleys_from_transition_compatibility"></a>

## 補題 `all_stage_switches_follow_valleys_from_transition_compatibility`

### 式

$$\text{初段が整合}\ +\ \text{端点が次段の初期状態}\ \Longrightarrow\ \text{全段階で一致と誤差の評価}$$

### Lean のコメント（日本語訳）

> 切替状態の整合性を、初期の段階からすべての後の段階へ伝える。各切替で、端点が次の段階の指定された初期状態に等しいことと、待ち時間での凍結軌道の一意性が、次の初期条件を確立する。
> 日本語の要約：初段の整合と、切替の端点の状態遷移の条件から、全段階の初期の整合を帰納する。

### 補題の説明

上の補題の「各段階の初期整合」の仮定を、**帰納法**で導きます：段階 \(n\) で実軌道が凍結軌道と一致するので、端点の値が一致し、遷移の条件により次の段階の初期状態に等しくなります。

### 証明の概略

1. 段階 \(n\) の一致（前の補題）から端点の値が一致。
2. 遷移の条件 `htransition` で次の段階の初期状態に一致。帰納法で全段階（23 行）。

----

<a id="Tomabechi.Theorem23.exists_stage_endpoint_after_time"></a>

## 補題 `exists_stage_endpoint_after_time`

### 式

$$\text{time 厳密増加・非有界}\ \Longrightarrow\ \forall t,\ \exists n,\ t<t_{n+1}$$

### Lean のコメント（日本語訳）

> 切替時刻が厳密に増加し非有界なら、すべての実数時刻は、ある段階の端点より前にある。

### 補題の説明

時刻 \(t\) を超える切替時刻が存在します。

### 証明の概略

1. 非有界性から \(t<t_k\) となる \(k\)。\(k=n+1\) の形に直す（8 行）。

----

<a id="Tomabechi.Theorem23.canonicalSwitchStageIndex"></a>

## 定義 `canonicalSwitchStageIndex`

### 式

$$\mathrm{idx}(t)=\min\{n\mid t<t_{n+1}\}$$

### Lean のコメント（日本語訳）

> 各実数時刻を、その後に厳密に来る最初の段階の端点に割り当てる。\([t_n,t_{n+1})\) の時刻については、これはちょうど段階 \(n\) を選ぶ。端点 \(t_{n+1}\) では、段階 \(n+1\) を選ぶ。
> 日本語の要約：切替時刻の列の狭義の単調性と非有界性から、各時刻を含む段階の番号を、最小選択で定義する。

### 定義の説明

時刻 \(t\) で「いま有効な段階」を決める関数です。`Nat.find`（最小の \(n\)）で定義します。

### 証明の概略

1. 定義：`Nat.find (exists_stage_endpoint_after_time ...)`（3 行）。

----

<a id="Tomabechi.Theorem23.canonicalSwitchStageIndex_eq_on_dwell"></a>

## 補題 `canonicalSwitchStageIndex_eq_on_dwell`

### 式

$$t\in[t_n,t_n+d_n)\ \Longrightarrow\ \mathrm{idx}(t)=n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

待ち時間の区間 \([t_n,t_{n+1})\) の中では、有効な段階は \(n\) です。

### 証明の概略

1. \(t<t_{n+1}\) より \(\mathrm{idx}(t)\le n\)（`Nat.find_min'`）。
2. \(\mathrm{idx}(t)<n\) なら \(t\ge t_n\ge t_{\mathrm{idx}+1}\) で矛盾（15 行）。

----

<a id="Tomabechi.Theorem23.canonicalSwitchStageIndex_eq_next_at_endpoint"></a>

## 補題 `canonicalSwitchStageIndex_eq_next_at_endpoint`

### 式

$$\mathrm{idx}(t_{n+1})=n+1$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

切替の瞬間 \(t_{n+1}\) には、**次の**段階 \(n+1\) が有効になります（端点は次の段階に割り当てる規約）。

### 証明の概略

1. 同様に `Nat.find` の最小性を用いる（16 行）。

----

<a id="Tomabechi.Theorem23.endpointCompatibleStageSequence"></a>

## 定義 `endpointCompatibleStageSequence`

### 式

$$\text{stage}_0=\text{first},\quad \text{stage}_{n+1}=\text{next}\bigl(n,\ \text{(前の凍結軌道の端点)},\ t_{n+1}\bigr)$$

### Lean のコメント（日本語訳）

> 次の各段階の仕様を、その初期状態を直前の凍結軌道の端点に設定して構築する。呼び出し側は、その端点の関数として、段階のその他の解析的なデータを与える。そのとき、遷移の等式自体は構成により従う。
> 日本語の要約：前の段階の凍結軌道の終状態を、次の段階の仕様の初期状態に採用し、切替の端点の整合を、構成により保証する。

### 定義の説明

段階の列を**再帰的に構成**する定義です。段階 \(n+1\) の初期状態は、段階 \(n\) の凍結軌道の端点の値になります（遷移の整合性が構成により成り立つ）。

### 証明の概略

1. 再帰による定義：`0 => first`、`n+1 => next n (前の段階の軌道の端点) (time (n+1))`（6 行）。

----

<a id="Tomabechi.Theorem23.endpointCompatibleStageSequence_transition"></a>

## 補題 `endpointCompatibleStageSequence_transition`

### 式

$$\text{stage}_{n+1}.\text{initial}=\text{(stage}_n\text{の凍結軌道)}(t_n+d_n)$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

構成の定義から、次の段階の初期状態は前の段階の軌道の端点になります（`nextInitial` の仮定）。

### 証明の概略

1. 定義の展開と `nextInitial`（3 行）。

----

<a id="Tomabechi.Theorem23.endpointCompatibleStageSequence_startTime"></a>

## 補題 `endpointCompatibleStageSequence_startTime`

### 式

$$\text{stage}_n.\text{startTime}=t_n$$

### Lean のコメント（日本語訳）

（コメントなし）

### 補題の説明

構成された各段階の開始時刻は切替時刻 \(t_n\) です。

### 証明の概略

1. 帰納法：\(n=0\) は `hfirstStart`、\(n+1\) は `nextStartTime`（8 行）。

----

<a id="Tomabechi.Theorem23.stitchedStageOrbit"></a>

## 定義 `stitchedStageOrbit`

### 式

$$x(t)=w_{\mathrm{active}(t)}.\mathrm{orbit}(t)$$

### Lean のコメント（日本語訳）

> 各時刻でどの凍結した段階の軌道が有効かを選んで、切替軌道を区分的に定義する。スケジュールの法則は、有効な番号が、半開の待ち時間の区間で \(n\)、その端点で \(n+1\) に変わることを述べる。上の任意の軌道のインターフェースと違い、この構成は、連続性、右片側の ODE、局所球への滞在を、凍結した証人と端点の整合性から導く。
> 日本語の要約：段階の番号に応じて凍結軌道をつなぎ、切替の互換性から、軌道の連続性・ODE・領域への滞在を導く。

### 定義の説明

段階 \(n\) の待ち時間の間は、段階 \(n\) の凍結軌道を使う、という「継ぎ合わせた」軌道です。実際の切替軌道そのものを**構成**します（任意の軌道を仮定しない）。

### 証明の概略

1. 定義：`witnesses (activeStage t) |>.orbit t`（3 行）。

----

<a id="Tomabechi.Theorem23.stitched_stage_orbits_form_a_switching_solution"></a>

## 補題 `stitched_stage_orbits_form_a_switching_solution`

### 式

$$\text{継ぎ合わせた軌道は連続で、各待ち時間で右微分が ODE を満たし、球内にある}$$

### Lean のコメント（日本語訳）

> 整合したスケジュールは、大域的な凍結軌道の族を、1 つの連続な切替軌道に変える。ODE は、段階の場が固定されている、各半開の待ち時間の区間で主張される。切替では、連続性は、直前の端点と次の初期状態の等式から従う。
> 日本語の要約：待ち時間ごとの段階の番号と、切替の端点の整合性から、切替軌道の各待ち時間での結論を構成する。

### 補題の説明

継ぎ合わせた軌道が、(i) 各待ち時間の閉区間で連続、(ii) 右微分が段階の ODE を満たす、(iii) 球内、を示します。切替点では、前の軌道の端点と次の軌道の初期状態が一致する（整合性）ので連続です。

### 証明の概略

1. 各段階の凍結軌道の連続性（`orbit_ode_forward` から `HasDerivAt.continuousOn`）。
2. 閉区間 \([t_n,t_n+d_n]\) 上で、継ぎ合わせた軌道が段階 \(n\) の軌道と一致する（端点は整合性により）。
3. 一致から連続性・右微分を移す（63 行）。

----

<a id="Tomabechi.Theorem23.stitched_stage_orbits_follow_valleys_before_tolerance"></a>

## 補題 `stitched_stage_orbits_follow_valleys_before_tolerance`

### 式

$$\text{継ぎ合わせた軌道が}\ \text{(22.5)}\ \text{を満たす：一致と誤差の評価}$$

### Lean のコメント（日本語訳）

> 継ぎ合わせた軌道は、定理22の待ち時間の仮定を自動的に満たす。したがって、選ばれた凍結軌道と端点の整合性は、任意の実際の経路がすでに切替 ODE を解いていると仮定せずに、切替軌道の一致と、指定された端点の許容誤差を与える。段階の番号のスケジュールは、`hactive` と `hactiveEndpoint` に明示されたままである。
> 日本語の要約：継ぎ合わせた軌道を、既存の ODE の一意性・待ち時間の定理に接続して、軌道の一致と終端の誤差を導く。

### 補題の説明

上の補題を使って、`all_stage_switches_follow_valleys_from_transition_compatibility` の仮定（実軌道の ODE・連続性）を、継ぎ合わせた軌道に対して**自動的に**満たします。

### 証明の概略

1. `stitched_stage_orbits_form_a_switching_solution` で ODE・連続性・球内。
2. `all_stage_switches_follow_valleys_from_transition_compatibility` を適用（44 行）。

----

<a id="Tomabechi.Theorem23.canonical_stitched_stage_orbits_follow_valleys_before_tolerance"></a>

## 補題 `canonical_stitched_stage_orbits_follow_valleys_before_tolerance`

### 式

$$\text{標準の段階番号}\ \Longrightarrow\ \text{一致と}\ \varepsilon\text{-誤差（スケジュールを仮定しない）}$$

### Lean のコメント（日本語訳）

> 継ぎ合わせた切替軌道は、別に与えられるスケジュールの選択関数を必要としない：正の待ち時間、時刻の漸化式、総待ち時間の発散が、標準的な「最初の将来の端点」の段階の番号を構成する。結果の経路は、(22.5) を満たし、閉じた各待ち時間の区間で各凍結軌道と一致する。
> 日本語の要約：正の待ち時間・時刻の漸化式・総時間の発散から、段階の番号を構成し、切替軌道の一致と待ち時間の誤差を導く。

### 補題の説明

スケジュール（有効な段階の番号）を仮定せず、`canonicalSwitchStageIndex` を使って自動的に決めます。

### 証明の概略

1. `canonicalSwitchStageIndex_eq_on_dwell`、`..._eq_next_at_endpoint` でスケジュールの条件を確認。
2. `stitched_stage_orbits_follow_valleys_before_tolerance` を標準の段階番号で適用（20 行）。

----

<a id="Tomabechi.Theorem23.endpoint_compatible_stage_factory_gives_canonical_switch"></a>

## 補題 `endpoint_compatible_stage_factory_gives_canonical_switch`

### 式

$$\text{段階の工場}\ \text{next}\ \Longrightarrow\ \text{標準の切替軌道が存在し、一致と}\ \varepsilon\text{-誤差}$$

### Lean のコメント（日本語訳）

> 各段階の初期状態を、直前の凍結した端点から選ぶ段階の工場からの、エンドツーエンドの切替の結果。これは、端点で整合する段階の再帰を、標準の切替のスケジュールと組み合わせる。任意の実際の軌道と、遷移の等式の前提は、どちらも除かれる。生成された各 `StageValleySpec` の解析的な妥当性は、`next` についての構成の義務として残る。
> 日本語の要約：端点から次の段階の仕様を再帰的に構成し、その列の凍結軌道を標準的に接続して、待ち時間の一致と終端の誤差を導く。

### 補題の説明

`endpointCompatibleStageSequence`（段階の列の再帰構成）と、`canonical_stitched_stage_orbits_follow_valleys_before_tolerance`（標準の継ぎ合わせ）を組み合わせた、最も構成的な結果です。

### 証明の概略

1. `endpointCompatibleStageSequence_transition`、`endpointCompatibleStageSequence_startTime` で整合性。
2. `canonical_stitched_stage_orbits_follow_valleys_before_tolerance` を適用（23 行）。

----

<a id="Tomabechi.Theorem23.condition23B_lub_and_timing_consequences"></a>

## 補題 `condition23B_lub_and_timing_consequences`

### 式

$$\text{条件 23-B の順序・時刻}\ \Longrightarrow\ (\forall n,\ u_n<\top)\wedge\text{Monotone}\ u\wedge(\forall n,\ u_n<u_{n+1})\wedge\text{time 非有界}\wedge\text{time 厳密増加}$$

### Lean のコメント（日本語訳）

> 条件 23-B の順序と時刻の部分を、定理の段階ごとの帰結にまとめる。前提 `hbelowTop` は意図的に保持している：論文は、すべての有限の段階が \(\top\) より下にあることを明示的に仮定する。結合の厳密な増加だけでは、それは出ない。待ち時間は実数値なので、有限性はその型に組み込まれている。正値性と部分和の発散は、下で述べる。
> 日本語の要約：条件 23-B の、順序の更新・新情報・待ち時間の仮定から、LUB 列と時刻列の結論をまとめる。

### 補題の説明

条件 23-B の順序と時間の部分の結論（LUB の厳密上昇・時刻の非有界・厳密増加）を 1 つにまとめます。`hbelowTop`（各 \(u_n<\top\)）は**仮定**です。

### 証明の概略

1. `lub_stages_monotone`、`every_new_stage_strictly_higher`、`switching_times_unbounded` をまとめる（5 行）。

----

<a id="Tomabechi.Theorem23.theorem23_conditionB_stagewise_conclusions"></a>

## 定理 `theorem23_conditionB_stagewise_conclusions`

### 式

$$\text{LUB 厳密上昇},\ \text{隣接 TCZ の閉・非空・非固定},\ \text{非 Zeno の切替},\ \text{最小点の唯一性},\ \text{切替誤差}\ \varepsilon_n,\ \dots$$

### Lean のコメント（日本語訳）

> 条件 23-B と、定理22が使う明示的な解析データのもとでの、定理23の段階ごとの結論の総合。LUB の厳密な増加、段階の隣り合う対ごとに異なる閉な到達可能 TCZ、非有界で非 Zeno の切替の時刻を証明する。各段階の古い最小点は、指数減衰によって、凍結軌道から到達可能であることが示される。次の段階の強凸性のギャップは、それを次の TCZ から除く。順序の条件 `u n < ⊤`、到達可能性の力学、発散する総待ち時間は、論文のとおり、明示的な仮定のままである。特に、`hinitial` は各切替の状態を次の凍結軌道の初期状態と同一視し、`hdecay` はその軌道がその状態から収束することを要求する。これらは合わせて、局所 Hessian のデータだけから導くのではなく、次の段階の吸引域の条件を符号化する。
> 日本語の要約：定理22の解析条件と条件 23-B のもとで、LUB の上昇・唯一の最小点・切替の誤差・TCZ の非空・閉・非固定をまとめる。

### 補題の説明

定理23の段階的な結論の**総まとめ**です。結論は 12 個の連言：(1) \(u_n<\top\)、(2) \(u_n<u_{n+1}\)、(3)(4) 中心・最小点が隣り合う段階で異なる、(5) 各段階の最小点が領域上の唯一の最小、(6)(7) 切替の整合と誤差 \(\varepsilon_n\)、(8)(9)(10) TCZ の非固定・閉・非空、(11)(12) 時刻の非有界・厳密増加。

### 証明の概略

1. `condition23B_lub_and_timing_consequences`（順序・時刻）。
2. `stage_tcz_changes_of_strong_convexity_and_decay`・`isClosed_stageTCZ_of_continuousOn`（TCZ）。
3. `stationary_point_is_unique_minimum_on_region`（唯一性）、`switched_*`（切替の誤差）などを合わせる（182 行）。

----

<a id="Tomabechi.Theorem23.canonicalStageTrajectory"></a>

## 定義 `canonicalStageTrajectory`

### 式

$$x(t)=w_{\mathrm{idx}(t)}.\mathrm{orbit}(t)$$

### Lean のコメント（日本語訳）

> 段階の仕様と時刻のスケジュールから決まる、標準的な区分的な軌道。各時刻は、最初の将来の切替に割り当てられる。
> 日本語の要約：段階の仕様と切替時刻の列から一意に定まる、標準的な切替軌道。

### 定義の説明

標準的な段階番号（`canonicalSwitchStageIndex`）で継ぎ合わせた軌道 `stitchedStageOrbit` です。

### 証明の概略

1. 定義：`stitchedStageOrbit` に `canonicalSwitchStageIndex` を渡す（8 行）。

----

<a id="Tomabechi.Theorem23.theorem22_stage_specs_and_switches_give_condition23B_core"></a>

## 定理 `theorem22_stage_specs_and_switches_give_condition23B_core`

### 式

$$\text{定理22の段階仕様}\ +\ \text{切替の整合}\ \Longrightarrow\ \text{条件 23-B の核の結論（上と同様）}\ +\ \text{非 Zeno}$$

### Lean のコメント（日本語訳）

> 定理23の解析/TCZ の部分のエンドツーエンドの段階的な橋。定理22がすべての凍結した谷を構成し、定理23が隣り合う TCZ の非固定性と閉性を証明し、遷移の整合性が、実際の切替軌道を待ち時間の区間に沿って、(22.5) の許容誤差とともに伝える。段階の中心は、単射な表現写像で LUB の列に結ばれるので、それらの隣り合う分離は、LUB の厳密な増加から従う。段階のギャップ、線分、端点の状態遷移の整合性は、明示的なままである。切替軌道とその待ち時間の ODE/連続性の条件は、凍結した証人から標準的に構成される。また、切替が、任意の有限時刻とすべての段階の番号より後に起こることを直接述べ、運転の永久の有限時間での停止点を排除する。
> 日本語の要約：忠実な表現で、束の列と段階の中心を結び、定理22の段階仕様と切替の条件から、段階の TCZ と軌道の結論をまとめる。

### 補題の説明

`theorem23_conditionB_stagewise_conclusions` の仮定のうち、切替軌道に関するものを、凍結軌道（`StageValleyWitness`）から構成した軌道 `canonicalStageTrajectory` で置き換えた、より構成的な版です。LUB の列と段階の中心を結ぶ**忠実な表現** `stageRepresentation`（単射）の仮定も加わります。

### 証明の概略

1. `chooseAllStageValleys` で全段階の谷を選び、`all_chosen_stage_TCZs_nonempty`・`all_chosen_stage_TCZs_closed_and_nonfixed` で TCZ の非空・閉・非固定。
2. 切替の軌道を `canonicalStageTrajectory`・`stitchedStageOrbit` で貼り合わせ、`stitched_stage_orbits_form_a_switching_solution` で切替の解になること、`canonicalSwitchStageIndex` の性質で各 dwell 区間・端点での段階の切替を扱う。
3. `all_stage_switches_follow_valleys_from_transition_compatibility` で切替時にも谷に沿うこと、`condition23B_lub_and_timing_consequences` で LUB の上昇と時刻の性質、`switching_times_unbounded`・`every_finite_time_in_some_dwell`・`infinitely_many_switches_after_every_finite_time` で切替時刻が有限時刻に集積しないこと（非 Zeno）を得る。これらをまとめて条件 23-B の核の結論とする（205 行）。

----

<a id="Tomabechi.Theorem23.meanField_stage_specs_and_switches_give_condition23B_core"></a>

## 定義 `meanField_stage_specs_and_switches_give_condition23B_core`

### 式

$$\text{平均場の段階の入力}\ \Longrightarrow\ \text{同じ条件 23-B の核の結論}$$

### Lean のコメント（日本語訳）

> H 段階の平均場の入力についての、同じ条件 23-B の切替の核。すべての段階の谷と凍結軌道は、各平均場の記録を `StageValleySpec` に写して得られる正確な列から選ばれる。すべてのギャップ、表現、遷移、新情報、待ち時間の仮定は、基礎にある定理の明示的な入力のままである。
> 日本語の要約：平均場の段階の記録を、谷の仕様に写した同じ列で、23-B の核を適用する入口。

### 定義の説明

`theorem22_stage_specs_and_switches_give_condition23B_core` の平均場版の入口です。**注意**：宣言は `def` で、戻り値の型が書かれておらず（`:= by exact …` から推論される）、結論は上の定理と同じ連言です。定理というより「定理の別名」として機能します。

### 証明の概略

1. `Tomabechi.Theorem22.meanFieldStageSequence` を使って、`theorem22_stage_specs_and_switches_give_condition23B_core` を適用する（29 行）。

----


## コメント修正記録

- 追加の `.lean` コメント修正はなし。ただし `meanField_stage_specs_and_switches_give_condition23B_core` が、戻り値の型を書かない `def` になっている点は、読者が戸惑うので注記しておく（解説書の当該項目を参照）。
