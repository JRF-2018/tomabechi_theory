# Theorem23_InvariantRegion.lean 解説

> 対象: [`Theorem23_InvariantRegion.lean`](../Theorem23_InvariantRegion.lean)（定理23：不変領域段階列のTCZ接続）。
> すべての定義・補題を、ファイルに現れる順に書き出しています。
> 各項目は「式 → Lean のコメント（日本語訳）→ 説明 → 証明の概略」の順です。
> 式は厳密な Lean の型ではなく、読みやすさを優先した近似です（正確な型は `.lean` を見てください）。

<!-- GLOSSARY:BEGIN -->
### 用語集（この文書で使う用語）

| 用語 | 意味 |
| --- | --- |
| TCZ | 閾値以下の状態の集合 \(\{x\mid V_0(x,t)\le\theta\}\)。評価 \(V_0\) が十分小さい「目標領域」。 |
| 閾値 \(\theta\) | 「十分よい」とみなす評価値の境界。 |
| 指数収束 | \(e^{-ct}\) のような速さで 0 に近づくこと（速さつきの収束）。 |
| 到達可能集合 | 制御に従って動かしたとき、状態がたどり着きうる点の集合。 |
| 前向き不変 | 一度その集合に入ったら、以後ずっと出ない（時間の前向きに不変）。 |
| 臨場感 | 状態への「引力」を作るバイアス。定理4・20・21・22で使う。 |
| 最小上界（LUB） | 与えた元すべてを上から抑える最小の元。結合 \(\vee\)。平均ではない。 |
| Hessian | 2階微分の行列。曲がり具合（凸性）を表す。 |
| 強凸 | \(\nabla^2V\succeq cI\)（\(c>0\)）のような、どの方向にも下に凸に曲がっていること。唯一の最小点を生む。 |
| 停留点・最小点 | 勾配が 0 の点・値が最小の点。 |
| 部分準位集合 | \(\{x\mid V(x)\le a\}\)。ポテンシャルの低い領域。 |
| 常微分方程式（ODE） | \(\dot x=f(x,t)\) の形の、時間変化の方程式。 |
| dist（距離）・infDist | 点と点の距離。`infDist x Z` は点 \(x\) から集合 \(Z\) までの距離（下限）。 |
| 凸集合 | 集合内の 2 点を結ぶ線分がすべて集合内にある。 |
| namespace・open | 名前の置き場所（名前空間）と、その名前を省略して使えるようにする宣言。 |
| Prop・仮定（hypothesis） | Lean では命題も「型」。補題の仮定は引数 `h…` として渡す。 |
<!-- GLOSSARY:END -->

---

## 0. このファイルの全体像

### 0.1 一言でいうと

定理23（TCZ・段階切替）の `StageSwitching.lean` の内容を、**緩和した不変領域の段階入力**（`InvariantRegionMeanFieldStageInput`、`Tomabechi/Dynamics/InvariantRegion.lean`）が持つ**凍結軌道と指数評価**に対して**構成し直す**ファイルです。論文と同じ**段階 TCZ**（局所球・閉到達集合・谷からのポテンシャル差）を構成し、(i) 各段階の TCZ が**空でなく閉**、(ii) 隣り合う段階で TCZ が**異なる**、(iii) 切替軌道が各待ち時間の区間で凍結軌道と**一致**し、切替時の誤差が \(\varepsilon_n\) 以内、という結論を得ます。

### 0.2 構成

| 内容 | 宣言 |
| --- | --- |
| 段階 TCZ | `stagePotential`, `invariantRegionStageTCZ` |
| 非空性・閉性 | `relaxed_minimizer_mem_stageTCZ`, `all_relaxed_stage_TCZs_nonempty`, `..._closed` |
| 強凸性・隣接の非一致 | `stageEffectiveStrongConvexity`, `relaxed_adjacent_stageTCZs_differ`, `all_relaxed_stage_TCZs_nonempty_closed_nonfixed`, `meanField_invariant_region_stages_have_TCZs` |
| 切替軌道 | `stitchedInvariantRegionOrbit`, `stitched_relaxed_orbits_*` |
| 条件 23-B の核 | `invariant_region_stages_and_switches_give_condition23B_core` |

### 0.3 このファイルが証明していないこと

- **段階間のギャップ（強凸性の閾値）・線分の包含・端点の状態遷移の整合・非 Zeno 性（総待ち時間の発散）**は、`StageSwitching.lean` と同じく**独立した明示的な仮定**です。
- 緩和した入力の構成（不変領域・谷の所属）は、`InvariantRegion.lean` の入力条件のままです。
- **初期の全劣水準集合との等式は導入しません**（この経路では使いません）。

### 0.4 ファイル冒頭のコメント（日本語訳）と名前空間

> **定理23：不変領域の段階列の TCZ 接続**
>
> このファイルは、緩和した段階の入力が持つ凍結軌道と指数の評価から、原文と同じ段階 TCZ（局所球・閉到達集合・谷からのポテンシャル差）を構成する。各段階の TCZ の非空性と閉性、隣接の非一致を、新しい証人の型へ移植し、切替軌道の継ぎ合わせ・待ち時間の端点の誤差・条件 23-B の核まで接続する。段階間のギャップ・線分の包含・端点の遷移・非 Zeno は、原文どおり、独立の明示的な仮定として保つ。

名前空間は `Tomabechi.Theorem23InvariantRegion`。`open Tomabechi.Theorem22InvariantRegion`、`open Tomabechi.Theorem23`、`open scoped Topology`。

---

<a id="Tomabechi.Theorem23InvariantRegion.stagePotential"></a>

## 定義 `stagePotential`

### 式

$$V_{\text{eff}}(x)=V(x)-\kappa p\,S_\mu(x)$$

### Lean のコメント（日本語訳）

> 緩和した平均場の段階の、平均化された実効ポテンシャル。

### 定義の説明

背景ポテンシャルから、ゲイン × 臨場感 × 平均場を引いた実効ポテンシャルです。

### 証明の概略

1. 定義：`background x - gain * presenceGain * meanField x`。

----

<a id="Tomabechi.Theorem23InvariantRegion.invariantRegionStageTCZ"></a>

## 定義 `invariantRegionStageTCZ`

### 式

$$\mathrm{TCZ}_n=\bar B_n\cap\overline{x_n([t_n,\infty))}\cap\{V_{\text{eff}}-V_{\text{eff}}(x^\*_n)\le\theta_n\}$$

### Lean のコメント（日本語訳）

> 原文の段階 TCZ を、緩和した段階と、それ自身の選ばれた凍結軌道の証人から作る。その定義は `Theorem23.stageTCZ` に合う。

### 定義の説明

`StageSwitching.lean` の `stageTCZ` を、緩和した段階の証人に特殊化したものです。

### 証明の概略

1. 定義：`stageTCZ (stagePotential ..) (minimizer ..) theta (closedBall ..) (closure (orbit '' Ici startTime))`。

----

<a id="Tomabechi.Theorem23InvariantRegion.relaxed_minimizer_mem_stageTCZ"></a>

## 補題 `relaxed_minimizer_mem_stageTCZ`

### 式

$$\theta\ge0\ \Longrightarrow\ x^\*\in\mathrm{TCZ}$$

### Lean のコメント（日本語訳）

> 指数減衰は、緩和した段階の最小点を、それ自身の前向きの到達可能な集合の閉包に入れる。そのポテンシャル差は零なので、非負の閾値をもつすべての TCZ に入る。

### 補題の説明

`chosen_valley_minimizer_in_stageTCZ`（StageSwitching）の緩和版です。

### 証明の概略

1. `limit_in_closed_reachable_of_exponential_decay`（StageSwitching）で軌道の閉包に入る、ポテンシャル差 0 で閾値条件。

----

<a id="Tomabechi.Theorem23InvariantRegion.all_relaxed_stage_TCZs_nonempty"></a>

## 補題 `all_relaxed_stage_TCZs_nonempty`

### 式

$$\forall n,\ \mathrm{TCZ}_n\neq\varnothing$$

### Lean のコメント（日本語訳）

> 緩和した選択された段階の証人から作った、すべての TCZ は空でない。

### 補題の説明

`all_chosen_stage_TCZs_nonempty` の緩和版です。

### 証明の概略

1. 最小点が TCZ に属す（上の補題）。

----

<a id="Tomabechi.Theorem23InvariantRegion.all_relaxed_stage_TCZs_closed"></a>

## 補題 `all_relaxed_stage_TCZs_closed`

### 式

$$\forall n,\ \mathrm{TCZ}_n\ \text{閉}$$

### Lean のコメント（日本語訳）

> 緩和した各段階の TCZ は閉である。ポテンシャルは、閉球の上で、その \(C^2\) の入力により連続であり、到達可能な因子は、定義により閉包である。

### 補題の説明

閉球（閉）・到達集合の閉包（閉）・ポテンシャルの閾値集合（連続関数の劣水準）の共通部分です。

### 証明の概略

1. `isClosed_stageTCZ_of_continuousOn`（StageSwitching）。

----

<a id="Tomabechi.Theorem23InvariantRegion.stageEffectiveStrongConvexity"></a>

## 補題 `stageEffectiveStrongConvexity`

### 式

$$V_{\text{eff}}\ \text{は}\ \bar B\ \text{で}\ (\kappa pm-\beta)\text{-強凸}$$

### Lean のコメント（日本語訳）

> 緩和した平均場の段階の、閾値の Hessian の境界は、不変領域の形によらず、その実効ポテンシャルの強凸性を、なお意味する。

### 補題の説明

強凸性は不変領域に依らず、Hessian の境界とゲインの閾値から出ます。

### 証明の概略

1. `per_stage_effective_strong_convexity`（StageData）を平均場に特殊化。

----

<a id="Tomabechi.Theorem23InvariantRegion.relaxed_adjacent_stageTCZs_differ"></a>

## 補題 `relaxed_adjacent_stageTCZs_differ`

### 式

$$\text{段階間の線分・強いギャップの条件}\ \Longrightarrow\ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> 隣り合う緩和した段階の TCZ は、既存の定理23の核と同じ、線分と厳密なギャップの条件のもとで異なる。強凸性は、共有する平均場の Hessian のデータから導かれる。直前の最小点は、この局所の評価が使えるように、次の閉球に入っていなければならない。

### 補題の説明

`chosen_valley_adjacent_stageTCZs_differ`（StageSwitching）の緩和版です。

### 証明の概略

1. `stageEffectiveStrongConvexity` で次の段階のポテンシャルの強凸性を得る。
2. 前段の最小点は、軌道の距離減衰（`distance_decay`、`decayAmplitude`・`decayRate`）と `limit_in_closed_reachable_of_exponential_decay` から前段の TCZ に属す。
3. ギャップと閾値の仮定から、前段の最小点は次段の TCZ に属さないので、2 つの TCZ は異なる（72 行）。

----

<a id="Tomabechi.Theorem23InvariantRegion.all_relaxed_stage_TCZs_nonempty_closed_nonfixed"></a>

## 補題 `all_relaxed_stage_TCZs_nonempty_closed_nonfixed`

### 式

$$\forall n:\ \mathrm{TCZ}_n\ \text{非空・閉},\ \ \mathrm{TCZ}_{n+1}\neq\mathrm{TCZ}_n$$

### Lean のコメント（日本語訳）

> すべての緩和した段階の TCZ の、非空性・閉性・隣接の非固定性。厳密なギャップと線分の包含は、対応する原文の入力に合わせて明示的なままで、谷の分離が正であることは導かれる。

### 補題の説明

上の 3 つの補題をまとめた定理です。

### 証明の概略

1. `all_relaxed_stage_TCZs_closed`（閉）と `all_relaxed_stage_TCZs_nonempty`（非空）を得る。
2. 隣接段の TCZ が異なること（`relaxed_adjacent_stageTCZs_differ`：前段の最小点が線分の端として前段の領域に入る `hsegment` を使う）。
3. 隣接段の最小点の分離（ノルム差が正）も、同じギャップの議論から示す（51 行）。

----

<a id="Tomabechi.Theorem23InvariantRegion.meanField_invariant_region_stages_have_TCZs"></a>

## 定理 `meanField_invariant_region_stages_have_TCZs`

### 式

$$\text{平均場の緩和入力の列}\ \Longrightarrow\ \text{TCZ の非空・閉・非固定}$$

### Lean のコメント（日本語訳）

> 緩和した平均場の段階の入力の列からの、エンドツーエンドの TCZ の橋。選ばれる谷の証人は、新しい定理22のアダプタが作ったものと、まさに同じである。原文の段階間のギャップと線分の条件は、独立の明示的な仮定のままで、この道では、初期の全部分準位との等式は導入されない。

### 補題の説明

平均場の段階入力の列から、全段階の証人（`chooseAllInvariantRegionStageWitnesses`）を選び、TCZ の結論をまとめます。

### 証明の概略

1. `chooseAllInvariantRegionStageWitnesses`（InvariantRegion）で証人を選び、`all_relaxed_stage_TCZs_nonempty_closed_nonfixed` を適用。

----

<a id="Tomabechi.Theorem23InvariantRegion.stitchedInvariantRegionOrbit"></a>

## 定義 `stitchedInvariantRegionOrbit`

### 式

$$x(t)=w_{\mathrm{active}(t)}.\mathrm{orbit}(t)$$

### Lean のコメント（日本語訳）

> 各時刻で、1 つの凍結軌道を、区分的に選ぶ。

### 定義の説明

`stitchedStageOrbit`（StageSwitching）の緩和版の継ぎ合わせ軌道です。

### 証明の概略

1. 定義：`witnesses (activeStage t) |>.orbit t`。

----

<a id="Tomabechi.Theorem23InvariantRegion.stitched_relaxed_orbits_agree_on_closed_dwell"></a>

## 補題 `stitched_relaxed_orbits_agree_on_closed_dwell`

### 式

$$\text{標準の段階番号の法則}\ +\ \text{端点の遷移の等式}\ \Longrightarrow\ \text{継ぎ合わせ}=w_n.\mathrm{orbit}\ \text{on}\ [t_n,t_n+d_n]$$

### Lean のコメント（日本語訳）

> 標準の待ち時間の番号の法則と、原文の遷移の等式があれば、区分的な緩和した軌道は、切替の端点を含む、閉じた待ち時間の区間の全体で、各凍結軌道と一致する。これは、切替軌道の連続性と、待ち時間の結論を証明する前に必要な、鍵となる端点の整合性である。

### 補題の説明

各待ち時間の閉区間で、継ぎ合わせた軌道が対応する凍結軌道に一致します（端点 \(t_n+d_n\) では、遷移の等式で次の初期状態と一致）。

### 証明の概略

1. 待ち時間の内部では定義から一致。端点では遷移の等式（前の軌道の端点＝次の段階の初期状態）。

----

<a id="Tomabechi.Theorem23InvariantRegion.stitched_relaxed_orbits_form_a_switching_solution"></a>

## 補題 `stitched_relaxed_orbits_form_a_switching_solution`

### 式

$$\text{継ぎ合わせた軌道は連続・段階の球内・右微分で ODE を満たす}$$

### Lean のコメント（日本語訳）

> 整合したスケジュールは、選ばれた緩和した凍結軌道を、すべての閉じた待ち時間の区間で、1 つの連続な切替軌道に変える。軌道は、有効な段階の局所球に留まり、対応する半開区間の全体で、その段階の ODE を右から解く。

### 補題の説明

`stitched_stage_orbits_form_a_switching_solution`（StageSwitching）の緩和版です。

### 証明の概略

1. 前の補題で各待ち時間の閉区間で一致。凍結軌道の連続性・ODE・球内から継ぎ合わせ軌道の性質を得る。

----

<a id="Tomabechi.Theorem23InvariantRegion.stitched_relaxed_orbits_follow_valleys_before_tolerance"></a>

## 補題 `stitched_relaxed_orbits_follow_valleys_before_tolerance`

### 式

$$\operatorname{dist}(\text{actual}(t_n+d_n),x^\*_n)\le\varepsilon_n$$

### Lean のコメント（日本語訳）

> 継ぎ合わせた緩和した軌道は、定理22と同じ対数の待ち時間の評価から、段階ごとの端点の許容誤差を引き継ぐ。

### 補題の説明

(22.5) の待ち時間の評価（`dwell_time_suffices_for_error`）を継ぎ合わせ軌道に適用します。

### 証明の概略

1. `stitched_relaxed_orbits_form_a_switching_solution` で、貼り合わせた軌道が各 dwell 区間で凍結軌道に一致すること（`hsolution.1`）を得る。
2. 端点 \(t_n+d_n\) で貼り合わせ軌道を凍結軌道に置き換え、谷の距離減衰 `distance_decay`（\(\le Ae^{-\rho(\cdot)}\)）を適用する。
3. 待ち時間の条件 `hwait`（\(d_n\ge\frac1\rho\log\frac A\epsilon\)）から `dwell_time_suffices_for_error`（Theorem22）で \(\le\epsilon_n\)（45 行）。

----

<a id="Tomabechi.Theorem23InvariantRegion.invariant_region_stages_and_switches_give_condition23B_core"></a>

## 定理 `invariant_region_stages_and_switches_give_condition23B_core`

### 式

$$\begin{aligned}
&u_{n+1}=u_n\vee v_{n+1},\ \ u_n<\top,\ \ v_{n+1}\not\le u_n;\ \ \text{段の中心 }=\iota(u_n)\ (\iota\ \text{単射});\ \ \text{ギャップ: }\theta_{n+1}<\tfrac{\lambda_{n+1}}2\|x^\ast_{n+1}-x^\ast_n\|^2;\\
&\text{線分 }[x^\ast_n,x^\ast_{n+1}]\subset\bar B_{n+1};\ \ \text{切替: }x_{n+1}(t_{n+1})\text{ は前段の軌道の端点};\ \ t_{n+1}=t_n+d_n,\ d_n>0,\ \textstyle\sum d_n=\infty;\ \ d_n\ge\max\{0,\tfrac1{\rho_n}\log\tfrac{A_n}{\epsilon_n}\}\\
&\Longrightarrow\ \ u\ \text{は厳密増加・}\top\text{ 未満},\ \ t_n\to\infty,\ \ \mathrm{center}_n\ne\mathrm{center}_{n+1},\ \ x^\ast_n\ne x^\ast_{n+1},\ \ \text{各段 TCZ は非空・閉・隣接段で異なる},\ \ \text{切替時の誤差}\le\epsilon_n
\end{aligned}$$
（ギャップ・線分・端点遷移・非 Zeno は原文どおり**独立の明示仮定**。条件 23-B の核の条件付き結論。）

### Lean のコメント（日本語訳）

> 解析的な条件 23-B の核の、エンドツーエンドの、緩和した H 段階の版。原文の独立な、厳密なギャップ・線分・端点の遷移・非 Zeno の仮定を保ちつつ、標準の切替軌道を構成する。

### 補題の説明

`theorem22_stage_specs_and_switches_give_condition23B_core`（StageSwitching）の、緩和した不変領域版です。

### 証明の概略

1. `chooseAllInvariantRegionStageWitnesses` と、本ファイルの上の定理群、`switching_times_unbounded`（StageSwitching）などをまとめる。

----


## コメント修正記録

- ファイル冒頭のモジュールコメントが「隣接非一致と切替軌道の全結論は後続実装する」と、実装前の状態のままだった。実装済みの範囲（切替軌道・待ち時間の誤差・条件 23-B の核まで）に合わせて書き換えた（コメントのみ、宣言は不変）。
